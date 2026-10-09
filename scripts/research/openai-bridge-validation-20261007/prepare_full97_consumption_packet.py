"""Prepare full184/focused16 metadata tooling by exact algorithm-preserving rebinding."""
import ast
import io
import json
import re
import tarfile
from pathlib import Path
from custody_checks import digest
from prepare_builder02 import sha
from prepare_builder02_full95 import OUTPUT as PARENT
from prepare_builder02_full97 import OUTPUT,REQUESTS
from prepare_builder02_full96 import MODULES
from full97_capture_gates import validate_successor

def main():
    validate_successor();parent=PARENT/'consumption-preparation-v1-dag'
    readiness=json.loads((parent/'readiness.json').read_bytes());assert digest(parent/'tooling.tar.gz')==readiness['tooling_archive_sha256']=='A0955F3BA77E9E4A0F1EB4DFE991A49403182782978C04A1E4B75E281073C0FD'
    old=json.loads((PARENT/'capture-manifest.json').read_bytes());new=json.loads((OUTPUT/'capture-manifest.json').read_bytes())
    assert new['requested_axioms']==old['requested_axioms']+REQUESTS and len(new['requested_axioms'])==184
    with tarfile.open(parent/'tooling.tar.gz') as archive:files={m.name:archive.extractfile(m).read() for m in archive.getmembers()}
    for name,row in readiness['files'].items():assert sha(files[name])==row['sha256'] and len(files[name])==row['bytes']
    source=files['probe.lean'].decode();original=source;replacements=[]
    for field,old_values,values in [('roots',old['requested_axioms'],new['requested_axioms']),('projectModules',[p.removeprefix('lean/').removesuffix('.lean').replace('/','.') for p in old['project_sources']],[p.removeprefix('lean/').removesuffix('.lean').replace('/','.') for p in new['project_sources']])]:
        match=re.search(r'private def '+field+r' : List String := (\[.*?\])',source);assert match and json.loads(match.group(1))==old_values
        before=match.group(1);after=json.dumps(values);source=source[:match.start(1)]+after+source[match.end(1):];replacements.append((before,after))
    inverse=source
    for before,after in reversed(replacements):assert inverse.count(after)==1;inverse=inverse.replace(after,before,1)
    assert inverse==original
    files['probe.lean']=''.join('import '+m+'\n' for m in MODULES).encode()+source.encode()
    post=files['postprocess.py'].decode();guard='assert len(roots)==181 and len(set(roots))==181 and len(focused)==len(set(focused))==13 and set(focused)<=set(roots)';assert post.count(guard)==1
    post=post.replace(guard,'assert len(roots)==184 and len(set(roots))==184 and len(focused)==len(set(focused))==16 and set(focused)<=set(roots)').replace('focused-thirteen-consumer','focused-sixteen-consumer').replace('exact181-native','exact184-native');ast.parse(post);files['postprocess.py']=post.encode()
    spec=json.loads(files['preparation-status.json']);assert spec['roots']==old['requested_axioms'] and len(spec['focused_roots'])==13
    spec.update(status='Full97 full184/focused16 tooling; native qualification required',roots=new['requested_axioms'],focused_roots=spec['focused_roots']+REQUESTS,graph_labels=['focused-sixteen-consumer','exact184-native']);files['preparation-status.json']=(json.dumps(spec,indent=2)+'\n').encode()
    root=OUTPUT/'consumption-preparation-v1-dag';root.mkdir()
    with tarfile.open(root/'tooling.tar.gz','x:gz') as archive:
        for name,data in sorted(files.items()):member=tarfile.TarInfo(name);member.size=len(data);member.mode=0o644;archive.addfile(member,io.BytesIO(data))
    for name,data in files.items():(root/name).write_bytes(data)
    report=dict(schema='full97-complete184-focused16-preparation-v1',parent_tooling_archive_sha256=digest(parent/'tooling.tar.gz'),capture_manifest_sha256=digest(OUTPUT/'capture-manifest.json'),input_archive_sha256=digest(OUTPUT/'input-archive.tar.gz'),tooling_archive_sha256=digest(root/'tooling.tar.gz'),files={name:{'sha256':sha(data),'bytes':len(data)} for name,data in files.items()},project_modules_exact=325,requested_roots_exact=184,focused_consumers_exact=16,original181_root_order_preserved=True,additional_roots=readiness['additional_roots']+REQUESTS,focused_roots=spec['focused_roots'],shared_DAG_algorithm_inverse_parity=True,probe_executed=False,native_qualification_pending=True,accepted=False,launch_clearance=False)
    (root/'readiness.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8');print(json.dumps({'roots':184,'focused':16,'modules':325,'tooling_sha256':report['tooling_archive_sha256'],'probe_executed':False}))
if __name__=='__main__':main()
