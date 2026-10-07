"""Installed SDK single-wire tests with explicit fake creds and forbidden sockets."""
import io
import socket
import sys
import unittest
from pathlib import Path
from unittest.mock import patch
sys.path.insert(0, str(Path(__file__).resolve().parent))
import boto3
from botocore.awsrequest import AWSResponse
from botocore.exceptions import ReadTimeoutError, ConnectionClosedError, EndpointConnectionError
from aws import single_wire_client, guard_mutation_client
from safety import BUCKET, SOURCE, Stop


class Raw:
    def __init__(self, body):
        self.body = body

    def stream(self, *args, **kwargs):
        yield self.body


class TransportTests(unittest.TestCase):
    def test_real_sdk_matrix(self):
        with patch.object(socket, 'socket', side_effect=AssertionError('REAL_SOCKET_FORBIDDEN')):
            session = boto3.Session(aws_access_key_id='SYNTHETIC', aws_secret_access_key='SYNTHETIC',
                                    aws_session_token='SYNTHETIC', region_name='us-east-1')
            cases = [ReadTimeoutError(endpoint_url='https://fixture.invalid'),
                     ConnectionClosedError(endpoint_url='https://fixture.invalid'),
                     EndpointConnectionError(endpoint_url='https://fixture.invalid'),
                     500, 503, 429, 301, 307, 400]
            for operation in ['delete_object', 'delete_bucket']:
                for case in cases:
                    with self.subTest(operation=operation, case=type(case).__name__ if isinstance(case, Exception) else case):
                        c = single_wire_client(session)
                        sends = []
                        def send(request):
                            sends.append(request)
                            if isinstance(case, Exception):
                                raise case
                            code = 'AuthorizationHeaderMalformed' if case == 400 else 'TemporaryFailure'
                            body = f'<Error><Code>{code}</Code><Region>us-west-2</Region></Error>'.encode()
                            return AWSResponse(request.url, case, {'content-type': 'application/xml',
                                                'x-amz-bucket-region': 'us-west-2'}, Raw(body))
                        c._endpoint.http_session.send = send
                        args = {'Bucket': BUCKET, 'ExpectedBucketOwner': SOURCE}
                        if operation == 'delete_object':
                            args.update(Key='fixture', VersionId='immutable-fixture', IfMatch='"etag"')
                        with self.assertRaises(Exception):
                            getattr(c, operation)(**args)
                        self.assertEqual(len(sends), 1)
                        c.close()

    def test_guard_replacement_blocks(self):
        session = boto3.Session(aws_access_key_id='SYNTHETIC', aws_secret_access_key='SYNTHETIC')
        c = single_wire_client(session)
        c._endpoint._needs_retry = lambda *args: False
        with self.assertRaisesRegex(Stop, 'SINGLE_WIRE_GUARD_CHANGED'):
            guard_mutation_client(c)
        c.close()


if __name__ == '__main__':
    unittest.main(verbosity=2)
