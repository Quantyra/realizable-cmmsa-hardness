"""Two disjoint successors adding only the source-verified CoveringSpan open."""
from pathlib import Path
import hashlib, json, re, subprocess, sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
from lean_source_static_preflight_v2 import inspect_bytes
S=Path(__file__).resolve().parent
P=Path('C:/Users/dfred/Desktop/Projects/IGH/Quantyra-AI-Planning')
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
report_path=S/'numeric-uniform-array-namespace-inspection-v1/result.json'
report_raw=report_path.read_bytes()
assert sha(report_raw)=='CB8D3A39C9361A9C9024DB83900A5334ABF518F536803B2C044825E652D84E4F'
report=json.loads(report_raw)
assert len(report['findings'])==2
OUT=S/'numeric-uniform-array-namespace-repair-offer-20261011-v1'
OUT.mkdir(exist_ok=False)
records=[]
for row in report['findings']:
    parent=Path(row['captured_source']);original=parent.read_bytes()
    assert sha(original)==row['sha256']
    index_path=parent.parent/'index.json';index=index_path.read_bytes()
    assert sha(index)==row['capture_index_sha256']
    manifest_path=parent.parent/'manifest.json';manifest=manifest_path.read_bytes()
    assert all(x['namespace']=='CoveringSpan' for x in row['missing'])
    newline=b'\r\n' if b'\r\n' in original else b'\n'
    marker=newline+b'set_option autoImplicit false'
    insertion=newline+b'open CoveringSpan'+newline
    assert original.count(marker)==1
    updated=original.replace(marker,insertion+marker,1)
    assert updated.replace(insertion+marker,marker,1)==original
    (OUT/parent.name).write_bytes(updated)
    checks_parent=parent.parent/'Checks.lean';checks=checks_parent.read_bytes()
    assert sha(checks)==next(x['sha256'] for x in json.loads(manifest)['files'] if x['path']=='Checks.lean')
    checks_target=OUT/(parent.stem+'Checks.lean');checks_target.write_bytes(checks)
    imports=re.findall(r'(?m)^import (\S+)',updated.decode())
    assert imports==re.findall(r'(?m)^import (\S+)',original.decode())
    records.append(dict(module='PvNP.RealizableHardness.'+parent.stem,path=parent.name,
        bytes=len(updated),sha256=sha(updated),parent_source=str(parent),parent_source_sha256=sha(original),
        parent_capture_index=str(index_path),parent_capture_index_sha256=sha(index),
        parent_manifest=str(manifest_path),parent_manifest_sha256=sha(manifest),added_namespaces=['CoveringSpan'],
        exact_inverse_byte_check=True,declarations_proofs_imports_unchanged=True,
        checks_path=checks_target.name,checks_parent=str(checks_parent),checks_sha256=sha(checks),
        checks_unchanged=True,direct_imports=imports,source_only_lexical_preflight=inspect_bytes(updated,parent.name),
        original_dependency_pins_retained_in_parent_manifest=True,execution_dependency_rebind_required=True,accepted=False))
relative='docs/research/pvnp/full90-actual-rhs-numeric-no-obligations-2026-10-08.md'
plan=subprocess.run(['git','-C',str(P),'show','26ccc3b:'+relative],check=True,stdout=subprocess.PIPE).stdout
heading='## 2026-10-11 Exact finite verifier aggregation before source-contract application'
text=plan.decode();assert text.count(heading)==1
section=text[text.index(heading):].split('\n## ',1)[0]
(OUT/'ARGUMENT.md').write_text('# Source-only uniform-array namespace repairs\n\n'+section+'\n',encoding='utf-8',newline='\n')
(OUT/'.gitattributes').write_text('* -text\n',encoding='utf-8',newline='\n')
manifest=dict(schema=OUT.name,author='/root',story='E002/S3137',accepted=False,compiler_invoked=False,
    mathematical_changes=False,independent_static_review_completed=False,
    inspection=dict(path=str(report_path),sha256=sha(report_raw)),source_successors=records,
    planning_argument=dict(repository=str(P),relative_path=relative,committed_head='26ccc3b',
        committed_blob_sha256=sha(plan),heading=heading,section_sha256=sha(section.encode())),
    toolchain='leanprover/lean4:v4.34.0-rc2',mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2',
    historical_pins_and_metadata_unchanged=True,explicit_execution_rebind_required=True,
    source_game_law_identified=False,source_no_proved=False,
    files=[dict(path=p.name,bytes=p.stat().st_size,sha256=sha(p.read_bytes())) for p in sorted(OUT.iterdir()) if p.is_file()])
(OUT/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(dict(manifest_sha256=sha((OUT/'manifest.json').read_bytes()),
    source_successors=[dict(module=r['module'],sha256=r['sha256']) for r in records])))
