"""Empty replacement before bucket intent; real loader/adapter/SDK, synthetic observations."""
import json
import os
from pathlib import Path
import socket
import sys
import tempfile
from unittest.mock import patch
AUDIT=Path(__file__).resolve().parent
REPO=next(p for p in AUDIT.parents if (p/'scripts/aws-archive-migration').is_dir())
sys.path.insert(0,str(REPO/'scripts/aws-archive-migration/source-retirement'))
from test_production import Bundle,FakeAWS,A
from test_transport import Raw
from botocore.awsrequest import AWSResponse
from adapter import ProductionAdapter
from aws import Mutator
from retirement import run
from safety import SOURCE,DEST,BUCKET,Journal,digest,Stop
from datetime import datetime
temp=Path('C:/Users/dfred/Desktop/Projects/realizable-cmmsa-hardness/tmp/spr')
temp.mkdir(parents=True,exist_ok=True)
fixture=Path(tempfile.mkdtemp(prefix='archive-recreated-',dir=temp))
os.environ['GIT_CONFIG_COUNT']='1'
os.environ['GIT_CONFIG_KEY_0']='core.longpaths'
os.environ['GIT_CONFIG_VALUE_0']='true'
bundle=Bundle(fixture)
root=bundle.loader()
aws=FakeAWS(bundle.base)
adapter=ProductionAdapter(aws,root,True)
state=fixture/'state';state.mkdir()
journal=Journal(state/'retirement.journal',root.expected_hash,digest(root.allowlist_bytes))
for row in A['rows']:
    identity=[row['key'],row['source_version']]
    journal.append('intent','version',identity,destination_version=row['destination_version'])
    journal.append('confirmed','version',identity,observed_absent=True)
# The original source bucket was externally deleted after its versions were removed,
# and the name was recreated with matching account/config controls BEFORE bucket intent.
# CreationDate is deliberately exposed by the fake API but is never requested by code.
aws.s3[SOURCE].inv['rows']=[]
new_marker='2026-10-07T14:00:00Z'
creation_reads=[]
def list_buckets(**kwargs):
    creation_reads.append(kwargs)
    return {'Owner':{'ID':aws.s3[SOURCE].config['get_bucket_acl']['Owner']['ID']}, 'Buckets':[{'Name':BUCKET,'BucketRegion':'us-east-1','CreationDate':datetime.fromisoformat(new_marker)}]}
aws.s3[SOURCE].list_buckets=list_buckets
sends=[]
def wire(request):
    sends.append({'url':request.url,'method':request.method})
    assert not aws.s3[SOURCE].inv['rows']
    aws.s3[SOURCE].absent=True
    return AWSResponse(request.url,204,{'x-amz-request-id':'synthetic-replacement-deletion'},Raw(b''))
mutator=Mutator(aws.sessions[SOURCE],root.authorize)
mutator.client._endpoint.http_session.send=wire
adapter.mutator=mutator
def authorize():
    g=root.authorize();g['execution_state_directory']=str(state);return g
with patch.object(socket,'socket',side_effect=AssertionError('REAL_SOCKET_FORBIDDEN')), \
     patch.object(ProductionAdapter,'verify_packet_artifacts',return_value=None):
    try:
        run(adapter,A,authorize,journal,True)
        raise AssertionError('REPLACEMENT_ACCEPTED')
    except Stop as exc:
        assert str(exc) in ('BUCKET_CONTINUITY_DRIFT','CONFIGURATION_DRIFT')
        result={'rejected':str(exc)}
assert len(sends)==0 and creation_reads
assert not journal.find('bucket',BUCKET,'intent')

receipt={'name':'A2-empty-replacement-before-bucket-intent-rejected','reproduced':False,'repair_rejected':True,
         'fixture':str(fixture),'root_evidence_commit':bundle.commit,'gate_commit':bundle.gate_commit,
         'gate_sha256':bundle.hash,'gate_file':str(bundle.gate),'journal_sha256':digest(journal.file.read_bytes()),
         'synthetic_source_was_replaced':True,'replacement_creation_marker':new_marker,
         'creation_marker_reads':len(creation_reads),'physical_requests':sends,'result':result,
         'bulk_artifact_hashing':'isolated; real 305/45 binder separately passed',
         'real_cloud_requests':0,'real_mutations':0}
(AUDIT/'independent-archive-recreated-final4-results.json').write_text(json.dumps(receipt,indent=2),encoding='utf-8')
print(json.dumps(receipt))
mutator.client.close()
