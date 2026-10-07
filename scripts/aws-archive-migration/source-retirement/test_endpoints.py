"""Actual SDK endpoint provenance with synthetic creds and explicit test transports."""
import sys
import os
import socket
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
from urllib.parse import urlsplit
sys.path.insert(0, str(Path(__file__).resolve().parent))
import boto3
from botocore.awsrequest import AWSResponse
from aws import AWS, Mutator, ENDPOINTS, guard_endpoint
from safety import SOURCE, DEST, BUCKET, Stop
from test_transport import Raw


class EndpointTests(unittest.TestCase):
    def test_all_ambient_override_sources_actual_read_and_mutation(self):
        for mode in ('global-env', 'service-env', 'profile-global', 'profile-services'):
            with self.subTest(mode=mode), tempfile.TemporaryDirectory() as td:
                config = Path(td)/'config'
                profiles = ''
                for name in ('cyint-ea-prod', 'quantyra'):
                    profiles += '[profile ' + name + ']\nregion = us-east-1\n'
                    profiles += ('endpoint_url = https://profile.invalid\n' if mode == 'profile-global' else '')
                    profiles += ('services = hostile\n' if mode == 'profile-services' else '')
                profiles += '[services hostile]\n'
                for service in ENDPOINTS:
                    profiles += service + ' =\n  endpoint_url = https://service-profile.invalid\n'
                config.write_text(profiles)
                env = {'AWS_CONFIG_FILE': str(config), 'AWS_SHARED_CREDENTIALS_FILE': str(Path(td)/'no-credentials'),
                       'AWS_EC2_METADATA_DISABLED': 'true', 'AWS_IGNORE_CONFIGURED_ENDPOINT_URLS': 'false'}
                if mode == 'global-env':
                    env['AWS_ENDPOINT_URL'] = 'https://global.invalid'
                if mode == 'service-env':
                    env.update({'AWS_ENDPOINT_URL_' + s.upper(): 'https://service.invalid' for s in ENDPOINTS})
                make = boto3.Session
                def session(**kw):
                    return make(**kw, aws_access_key_id='SYNTHETIC', aws_secret_access_key='SYNTHETIC')
                sends = []
                with patch.dict(os.environ, env), patch.object(socket, 'socket', side_effect=AssertionError('REAL_SOCKET_FORBIDDEN')):
                    with patch.object(boto3, 'Session', side_effect=session):
                        aws = AWS()
                    for account in (SOURCE, DEST):
                        for service in ('s3', 'sts', 'iam'):
                            if service == 'iam' and account == DEST:
                                continue
                            c = aws.client(service, account)
                            self.assertEqual(c.meta.endpoint_url, ENDPOINTS[service])
                            def read(request):
                                sends.append(request.url)
                                self.assertEqual(urlsplit(request.url).hostname, urlsplit(ENDPOINTS[service]).hostname)
                                body = b'<Error><Code>AccessDenied</Code><Message>synthetic</Message></Error>'
                                return AWSResponse(request.url, 403, {'content-type': 'application/xml'}, Raw(body))
                            c._endpoint.http_session.send = read
                            with self.assertRaises(Exception):
                                if service == 's3': c.list_buckets()
                                elif service == 'sts': c.get_caller_identity()
                                else: c.get_user()
                            c.close()
                    m = Mutator(aws.sessions[SOURCE], lambda: None)
                    def mutation(request):
                        sends.append(request.url)
                        self.assertEqual(urlsplit(request.url).hostname, BUCKET + '.s3.us-east-1.amazonaws.com')
                        return AWSResponse(request.url, 204, {'x-amz-version-id': 'immutable-fixture'}, Raw(b''))
                    m.client._endpoint.http_session.send = mutation
                    m.delete_version({'key': 'fixture', 'source_version': 'immutable-fixture', 'source_etag': '"etag"'})
                    m.delete_bucket()
                    m.client.close()
                self.assertEqual(len(sends), 7)

    def test_tls_partition_region_and_signed_url_drift_reject(self):
        s = boto3.Session(aws_access_key_id='SYNTHETIC', aws_secret_access_key='SYNTHETIC')
        for field, value in (('partition', 'aws-cn'), ('region_name', 'us-west-2'),
                             ('endpoint_url', 'https://hostile.invalid')):
            m = Mutator(s, lambda: None)
            target, attr = (m.client.meta.config, 'region_name') if field == 'region_name' else (m.client.meta, '_' + field)
            with patch.object(target, attr, value):
                with self.assertRaisesRegex(Stop, 'PRODUCTION_ENDPOINT_DRIFT'): guard_endpoint(m.client)
            m.client.close()
        m = Mutator(s, lambda: None)
        m.client._endpoint.http_session._verify = False
        with self.assertRaisesRegex(Stop, 'PRODUCTION_ENDPOINT_DRIFT'): m.delete_bucket()
        m.client.close()
        for url in ('http://s3.us-east-1.amazonaws.com/', 'https://hostile.invalid/',
                    'https://s3.us-east-1.amazonaws.com:444/', 'https://user@s3.us-east-1.amazonaws.com/'):
            m = Mutator(s, lambda: None)
            sends = []
            def redirect(request, **kw): request.url = url
            m.client.meta.events.register_first('before-send.s3.DeleteBucket', redirect)
            m.client._endpoint.http_session.send = lambda request: sends.append(request)
            with patch.object(socket, 'socket', side_effect=AssertionError('REAL_SOCKET_FORBIDDEN')):
                with self.assertRaisesRegex(Stop, 'PRODUCTION_WIRE_ENDPOINT_DRIFT'): m.delete_bucket()
            self.assertEqual(sends, [])
            m.client.close()


if __name__ == '__main__':
    unittest.main(verbosity=2)
