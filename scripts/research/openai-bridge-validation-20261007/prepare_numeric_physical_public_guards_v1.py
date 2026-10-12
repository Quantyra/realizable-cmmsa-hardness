"""Append two public wrappers, preserving the exact complete physical source prefix."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
from lean_source_static_preflight_v2 import inspect_bytes
S=Path(__file__).resolve().parent
P=Path('C:/Users/dfred/Desktop/Projects/IGH/Quantyra-AI-Planning')
CAP=S/'numeric-physical-density-capture-v4'
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
source=(CAP/'ActualNumericPhysicalDensity.lean').read_bytes()
assert sha(source)=='58BBC9F6D120FFC7435DDA5437821C9CE14B573F275187B6D14D302E3201DDE2'
index=(CAP/'index.json').read_bytes()
assert sha(index)=='E010176FB8A1353D70923DA51198ED457FE3DF51B3909B8A6E260CF713076B91'
parent_manifest=(CAP/'manifest.json').read_bytes()
parent_checks=(CAP/'ActualNumericPhysicalDensityChecks.lean').read_bytes()
assert sha(parent_checks)=='1150349DF69B8321950EE19CA9C250E6EDAB89B23091B59AF9ECA7EED25AB5FA'
nl=b'\r\n' if b'\r\n' in source else b'\n'
wrappers=[];records=[]
for old,new in [('numeric_selected_guards','selected_numeric_physical_guards'),
                ('numeric_selected_slack','selected_numeric_physical_slack')]:
    start=('private theorem '+old).encode()
    assert source.count(start)==1
    header=source.split(start,1)[1].split(b' := by',1)[0]
    wrapper=('theorem '+new).encode()+header+b' := by'+nl+('  exact '+old+' hm hnum hdiv hA').encode()+nl
    wrappers.append(wrapper)
    records.append(dict(private_name=old,public_name=new,statement_bytes_unchanged=True,
        statement_sha256=sha(header),proof='exact '+old+' hm hnum hdiv hA'))
insertion=nl+b'/- Public arithmetic interfaces for the common-floor composition. -/'+nl+nl.join(wrappers)
marker=nl+b'end'+nl+b'end PvNP.RealizableHardness.ActualNumericPhysicalDensity'
assert source.count(marker)==1
updated=source.replace(marker,insertion+marker,1)
assert updated.replace(insertion+marker,marker,1)==source
checks=parent_checks+nl
for row in records:
    name='PvNP.RealizableHardness.ActualNumericPhysicalDensity.'+row['public_name']
    checks+=('#check '+name).encode()+nl+('#print axioms '+name).encode()+nl
relative='docs/research/pvnp/full90-actual-rhs-numeric-no-obligations-2026-10-08.md'
plan=subprocess.run(['git','-C',str(P),'show','5964d53:'+relative],check=True,stdout=subprocess.PIPE).stdout
heading='## 2026-10-11 One fixed integer defines the coefficient family and common floor'
text=plan.decode();assert text.count(heading)==1
section=text[text.index(heading):].split('\n## ',1)[0]
OUT=S/'numeric-physical-density-public-guards-offer-v1';OUT.mkdir(exist_ok=False)
(OUT/'ActualNumericPhysicalDensity.lean').write_bytes(updated)
(OUT/'ActualNumericPhysicalDensityChecks.lean').write_bytes(checks)
(OUT/'ARGUMENT.md').write_text('# Public physical arithmetic interfaces\n\n'+section+'\n',encoding='utf-8',newline='\n')
(OUT/'.gitattributes').write_bytes(b'* -text\n')
manifest=dict(schema=OUT.name,author='/root',story='E002/S3137',accepted=False,compiler_invoked=False,
    module='PvNP.RealizableHardness.ActualNumericPhysicalDensity',
    source_only_lexical_preflight=inspect_bytes(updated,'ActualNumericPhysicalDensity.lean'),
    parent_source=str(CAP/'ActualNumericPhysicalDensity.lean'),parent_source_sha256=sha(source),
    parent_capture_index=str(CAP/'index.json'),parent_capture_index_sha256=sha(index),
    parent_manifest=str(CAP/'manifest.json'),parent_manifest_sha256=sha(parent_manifest),
    original_source_bytes_exact_inverse=True,original_checks_preserved_as_exact_prefix=True,
    public_wrappers=records,public_axiom_requests=re.findall(r'(?m)^#print axioms (\S+)',checks.decode()),
    direct_imports=re.findall(r'(?m)^import (\S+)',updated.decode()),
    historical_dependency_pins_in_parent_manifest=True,explicit_execution_rebind_required=True,
    planning_argument=dict(repository=str(P),relative_path=relative,committed_head='5964d53',
        committed_blob_sha256=sha(plan),heading=heading,section_sha256=sha(section.encode())),
    toolchain='leanprover/lean4:v4.34.0-rc2',mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2',
    source_no_proved=False,common_floor_discharged=False,
    files=[dict(path=p.name,bytes=p.stat().st_size,sha256=sha(p.read_bytes())) for p in sorted(OUT.iterdir()) if p.is_file()])
(OUT/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(dict(source_sha256=sha(updated),checks_sha256=sha(checks),
    manifest_sha256=sha((OUT/'manifest.json').read_bytes()),new_public_wrappers=records)))
