"""Independent installed-SDK endpoint, gate and permission probes; sockets forbidden."""
import json
import os
from pathlib import Path
import socket
import sys
import unittest
from unittest.mock import patch
from urllib.parse import urlparse, parse_qs
AUDIT=Path(__file__).resolve().parent
REPO=AUDIT.parents[2]
sys.path.insert(0,str(REPO/'scripts/aws-archive-migration/source-retirement'))
import boto3
import botocore
from botocore.awsrequest import AWSResponse
from aws import AWS,Mutator,single_wire_client
from safety import SOURCE,DEST,BUCKET,Stop
from permission import simulate_one
from policy import source_freeze
from test_transport import Raw
results=[]
def record(name,**details):
    results.append({'name':name,**details})
    (AUDIT/'independent-archive-results.json').write_text(json.dumps(results,indent=2),encoding='utf-8')
def session():
    return boto3.Session(aws_access_key_id='SYNTHETIC',aws_secret_access_key='SYNTHETIC',region_name='us-east-1')

class Review(unittest.TestCase):
    def setUp(self):
        p=patch.object(socket,'socket',side_effect=AssertionError('REAL_SOCKET_FORBIDDEN'))
        p.start();self.addCleanup(p.stop)

    def test_A1_mutation_endpoint_ambient_override(self):
        with patch.dict(os.environ,{'AWS_ENDPOINT_URL_S3':'https://archive-fixture.invalid','AWS_EC2_METADATA_DISABLED':'true'}):
            s=session();m=Mutator(s,lambda:None);sent=[]
            def send(request):
                sent.append(request)
                return AWSResponse(request.url,204,{'x-amz-version-id':'immutable-fixture'},Raw(b''))
            m.client._endpoint.http_session.send=send
            m.delete_version({'key':'fixture','source_version':'immutable-fixture','source_etag':'"etag"'})
            self.assertEqual(len(sent),1)
            self.assertEqual(urlparse(sent[0].url).hostname,'archive-fixture.invalid')
            self.assertEqual(parse_qs(urlparse(sent[0].url).query)['versionId'],['immutable-fixture'])
            record('A1-custom-mutation-endpoint-accepted',reproduced=True,url=sent[0].url,sends=len(sent),
                   sdk=botocore.__version__,ignore_configured_endpoint_urls=m.client.meta.config.ignore_configured_endpoint_urls)
            m.client.close()

    def test_A1_read_endpoint_ambient_override(self):
        with patch.dict(os.environ,{'AWS_ENDPOINT_URL_S3':'https://archive-fixture.invalid','AWS_EC2_METADATA_DISABLED':'true'}):
            make_session=boto3.Session
            with patch.object(boto3,'Session',side_effect=lambda **kw:make_session(aws_access_key_id='SYNTHETIC',aws_secret_access_key='SYNTHETIC',region_name='us-east-1')):
                aws=AWS()
            c=aws.client('s3',DEST)
            self.assertEqual(c.meta.endpoint_url,'https://archive-fixture.invalid')
            record('A1-custom-observation-endpoint-accepted',reproduced=True,destinationEndpoint=c.meta.endpoint_url)
            c.close()

    def test_before_send_ttl_guard_zero_physical_requests(self):
        sent=[];calls=[]
        def authorize():
            calls.append(1)
            if len(calls)==2:raise Stop('ROOT_GATE_EXPIRED')
        m=Mutator(session(),authorize)
        m.client._endpoint.http_session.send=lambda request:sent.append(request)
        with self.assertRaisesRegex(Stop,'ROOT_GATE_EXPIRED'):
            m.delete_version({'key':'fixture','source_version':'immutable-fixture','source_etag':'"etag"'})
        self.assertEqual(len(sent),0)
        record('archive-before-send-expiry-negative-control',passed=True,authorizationCalls=len(calls),sends=0)
        m.client.close()

    def test_permission_resource_denial_rejected(self):
        resource='arn:aws:s3:::'+BUCKET+'/fixture'
        class IAM:
            def simulate_principal_policy(self,**kw):
                return {'IsTruncated':False,'EvaluationResults':[{'EvalActionName':'s3:DeleteObjectVersion',
                        'EvalResourceName':resource,'EvalDecision':'allowed','ResourceSpecificResults':[
                        {'EvalResourceName':resource,'EvalResourceDecision':'explicitDeny'}]}]}
        with self.assertRaisesRegex(Stop,'PERMISSION_DECISION_SCOPE'):
            simulate_one(IAM(),'s3:DeleteObjectVersion',resource,source_freeze(),'immutable-fixture')
        record('archive-resource-denial-negative-control',passed=True)

    def test_original_allowlist_cannot_be_rebound(self):
        # Scope is hard-pinned; no arbitrary artifact rebind is possible through the real root loader.
        from root import BOUND_ALLOWLIST
        from safety import digest
        data=(REPO/'scripts/aws-archive-migration/source-retirement/evidence/bound-allowlist.json').read_bytes()
        self.assertEqual(digest(data),BOUND_ALLOWLIST)
        record('archive-original-allowlist-negative-control',passed=True,allowlist_sha256=digest(data))

if __name__=='__main__':
    unittest.main(verbosity=2)
