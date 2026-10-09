"""Two-copy custody for six immutable Full95 reports, inputs and membership evidence."""
import hashlib
import io
import json
from pathlib import Path
import shutil
import tarfile
from prepare_builder02_full95 import OUTPUT
from custody_checks import digest,verify_local_custody
HERE=Path(__file__).parent
BASE=OUTPUT/'consumption-v1/qualification'
def main():
    files={}
    for kind,folder in [('original','material-integration-v1'),('addendum','material-integration-identity-addendum-v1')]:
        root=BASE/folder
        files[kind+'/manifest.json']=(root/'manifest.json').read_bytes()
        files[kind+'/integration.txt']=(root/'integration.txt').read_bytes()
        reports=HERE/('full95-material-integration-reports' if kind=='original' else 'full95-material-identity-addendum-reports')
        for lens in ['proof-adversarial','complexity','non-claims']:
            key=lens+'-01'; receipt=json.loads((reports/(key+'.json')).read_bytes())
            assert receipt['native_exit']==0 and receipt['actual_packet_context_fit'] and receipt['supplied_file_count']==67
            assert digest(reports/(key+'.md'))==receipt['report_sha256']
            assert digest(root/key/'stdout.json')==receipt['raw_stdout_sha256']
            for name in ['prompt.txt','command.json','live.json','stdout.json','stderr.txt','native-exit.txt']:
                files[kind+'/'+key+'/'+name]=(root/key/name).read_bytes()
            for suffix in ['.md','.json']:
                files[kind+'/reports/'+key+suffix]=(reports/(key+suffix)).read_bytes()
    mapping=BASE/'source-object-identity-reconciliation-v1.json';files['source-object-identity-reconciliation-v1.json']=mapping.read_bytes()
    marker=json.loads((OUTPUT/'launch-once.json').read_bytes());native=json.loads((Path(marker['preflight'])/'terminal-custody.json').read_bytes())['custody']
    verify_local_custody(native['short_path'],native['repository_path'],native['remote_sha256'],native['bytes'])
    with tarfile.open(native['repository_path']) as archive:
        for name in ['capture-manifest.json','source-before.json','source-after.json','compiled-project-objects.json','object-after.json']:
            data=archive.extractfile(name).read();assert hashlib.sha256(data).hexdigest().upper()==json.loads(mapping.read_bytes())['native_archive_member_pins'][name]
            files['native-receipt-members/'+name]=data
    files['custody-provenance.json']=(json.dumps(dict(native_custody=native,source_object_mapping_sha256=digest(mapping),original_and_addendum_reports_unchanged=True,
        object_inventory_members_included=True,compiled_object_binary_bytes_not_in_this_archive=True,independent_material_only_verdicts=True,full_goal_complete=False),indent=2)+'\n').encode()
    root=BASE/'six-review-custody-v1';root.mkdir();first=Path('C:/a8gcp/13a1218e-full95-six-review-v1.tar.gz')
    with tarfile.open(first,'x:gz') as archive:
        for name,data in sorted(files.items()):
            member=tarfile.TarInfo(name);member.size=len(data);member.mode=0o644;archive.addfile(member,io.BytesIO(data))
    second=root/'evidence.tar.gz'
    with first.open('rb') as source,second.open('xb') as destination:shutil.copyfileobj(source,destination)
    custody=verify_local_custody(first,second,digest(first),first.stat().st_size)
    report=dict(schema='full95-six-review-two-copy-custody-v1',custody=custody,members=len(files),member_sha256={n:hashlib.sha256(d).hexdigest().upper() for n,d in files.items()},
        original_reports=3,addendum_reports=3,all_provider_native_exits_zero=True,all_actual_context_fits_verified=True,accepted=False,full_goal_complete=False)
    (root/'custody.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8');print(json.dumps({'members':len(files),'custody':custody}))
if __name__=='__main__':main()
