"""Re-pin mandatory complete review bodies; no completeness, native or review credit."""
import json
from pathlib import Path
import tarfile
from custody_checks import digest
from prepare_builder02 import sha
from full86_controller import ROOT,validate_successor

PLANNING=Path('C:/Users/dfred/Desktop/Projects/IGH/Quantyra-AI-Planning')

def main():
    validate_successor()
    seed=PLANNING/'docs/research/pvnp/full82-a22-hc46-current-critical-body-pins-2026-10-07.json'
    previous=json.loads(seed.read_bytes())
    manifest=json.loads((ROOT/'capture-manifest.json').read_bytes())
    with tarfile.open(ROOT/'input-archive.tar.gz','r:gz') as archive:
        members=archive.getmembers()
        if any(not member.isfile() for member in members) or len({m.name for m in members})!=len(members): raise RuntimeError('Invalid capsule')
        files={member.name:archive.extractfile(member).read() for member in members}
    for rel,row in manifest['project_sources'].items():
        if sha(files[rel])!=row['sha256']: raise RuntimeError('Project source drift')
    rows=[]; changed=[]
    for old in previous['bodies']:
        rel=old['path']; data=files[rel]; pin=sha(data)
        rows.append(dict(path=rel,sha256=pin,bytes=len(data),current_complete_body_required=True,
                         previous_full82_sha256=old['sha256'],identity_changed_since_full82=pin!=old['sha256']))
        if pin!=old['sha256']: changed.append(rel)
    if len(rows)!=86 or len({row['path'] for row in rows})!=86: raise RuntimeError('Mandatory body scope drift')
    report=dict(schema='cmmsa-current-minimum-critical-body-pins-v2',resource=ROOT.name,
        input_archive_sha256=digest(ROOT/'input-archive.tar.gz'),capture_manifest_sha256=digest(ROOT/'capture-manifest.json'),
        previous_index_sha256=digest(seed),project_source_count=319,minimum_body_count=len(rows),
        minimum_body_bytes=sum(row['bytes'] for row in rows),changed_since_full82=changed,bodies=rows,
        complete_consumption_trace=False,selection_complete=False,context_fit_verified=False,
        native_green=False,reviewed=False,accepted=False,
        scope='Exact minimum full-text body identities only; transitive consumption, remaining dispositions, context fit and native/provider reviews remain unverified.')
    destination=PLANNING/'docs/research/pvnp/full86-current-minimum-critical-body-pins-2026-10-07.json'
    with destination.open('x',encoding='utf-8') as output: json.dump(report,output,indent=2)
    print(json.dumps(dict(minimum_body_count=len(rows),minimum_body_bytes=report['minimum_body_bytes'],changed_since_full82=changed,complete_consumption_trace=False),indent=2))

if __name__=='__main__': main()
