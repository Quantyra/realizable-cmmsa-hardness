"""Freeze conditional source NO, preserving every original physical antecedent."""
from pathlib import Path
import hashlib,json,re,subprocess,sys,tarfile
sys.path.insert(0,str(Path(__file__).resolve().parent))
from lean_source_static_preflight_v2 import inspect_bytes
S=Path(__file__).resolve().parent
OUT=S/'numeric-original-source-no-offer-20261011-v1'
P=Path('C:/Users/dfred/Desktop/Projects/IGH/Quantyra-AI-Planning')
ARCHIVE=Path('C:/Users/dfred/.quantyra/builder02/full114-exact-real-complex-operators-repair4-resource02/input-archive.tar.gz')
PIN='70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
assert not (OUT/'manifest.json').exists()
with ARCHIVE.open('rb') as f:assert hashlib.file_digest(f,'sha256').hexdigest().upper()==PIN
member='lean/PvNP/RealizableHardness/TaggedFinite3LinSource.lean'
with tarfile.open(ARCHIVE,'r:gz') as t:
    toolchain=t.extractfile('lean-toolchain').read()
    baseline=t.extractfile(member).read()
assert toolchain.decode().strip()=='leanprover/lean4:v4.34.0-rc2'
candidates=[]
for module,directory,sourcepin,cappin in [
    ('ActualVerifierAggregation','numeric-actual-verifier-aggregation-capture-v1',
     'F44564BA1EB97CBD5FF465FA4EFDF2E856F5AC89E2DF4065D6C4DD35C9817660',
     '1B2DE96BE29AEC54C6990893409E9B04A17ACAF4141D031C8E10886740D5CF31'),
    ('ActualOriginalSourceScalar','numeric-original-source-scalar-capture-v1',
     'B1ABDF556AA8FFD7027F19FB0A314B93BD79C8535E0A59D491FCFE43B47E2F52',
     '128244671E5F4B7C41ADF7861BF31BF05B35E124049DD06A94097C32D8942A60')]:
    cap=S/directory;index=(cap/'index.json').read_bytes()
    assert sha(index)==cappin and sourcepin in index.decode()
    path=cap/(module+'.lean');raw=path.read_bytes();assert sha(raw)==sourcepin
    candidates.append(dict(module='PvNP.RealizableHardness.'+module,path=str(path),bytes=len(raw),
        sha256=sourcepin,capture_index=str(cap/'index.json'),capture_sha256=cappin,accepted=False))
source=(OUT/'ActualOriginalSourceNo.lean').read_bytes()
assert sha(source)=='46188EB312B13D78591E6613AC9757616E0510B3384C9DEB29C232BAC66CAFFF'
preflight=inspect_bytes(source,'ActualOriginalSourceNo.lean');code=source.decode()
imports=re.findall(r'(?m)^import (\S+)',code)
assert imports==[x['module'] for x in candidates]+['PvNP.RealizableHardness.TaggedFinite3LinSource']
exports=re.findall(r'(?m)^theorem (\w+)',code)
definitions=re.findall(r'(?m)^(?:def|structure) (\w+)',code)
assert len(exports)==5 and len(definitions)==3
parent=(S/'numeric-uniform-array-namespace-repair-capture-v1/ActualTotalOrderedStrategy.lean').read_bytes()
assert sha(parent)=='993EE237B8F89920083D6772CEED2DBA7527F78F9AFFC579434CDCEAD6FC960D'
header=parent.decode().split('theorem physical_forces_total_original_iid_mean',1)[1].split(' :\n    ∃ choice',1)[0]
candidate_header=code.split('theorem physical_source_no_contradiction',1)[1].split('\n    (kappa gap : Real)',1)[0]
assert candidate_header==header
checks='import PvNP.RealizableHardness.ActualOriginalSourceNo\n\n'
for name in definitions+exports:checks+='#check PvNP.RealizableHardness.ActualOriginalSourceNo.'+name+'\n'
for name in exports:checks+='#print axioms PvNP.RealizableHardness.ActualOriginalSourceNo.'+name+'\n'
relative='docs/research/pvnp/full90-actual-rhs-numeric-no-obligations-2026-10-08.md'
plan=subprocess.run(['git','-C',str(P),'show','4489537:'+relative],check=True,stdout=subprocess.PIPE).stdout
heading='## 2026-10-11 Tagged NO promise and explicit imported source-bound composition'
text=plan.decode();assert text.count(heading)==1
section=text[text.index(heading):].split('\n## ',1)[0]
for name,value in [('Checks.lean',checks),('ARGUMENT.md','# Conditional source NO composition\n\n'+section+'\n'),('.gitattributes','* -text\n')]:
    (OUT/name).write_text(value,encoding='utf-8',newline='\n')
files=[]
for path in sorted(OUT.rglob('*')):
    if path.is_file():
        raw=path.read_bytes();files.append(dict(path=path.relative_to(OUT).as_posix(),bytes=len(raw),
            sha256=sha(raw),diagnostic='diagnostics' in path.relative_to(OUT).parts))
manifest=dict(schema=OUT.name,author='/root',story='E002/S3137',accepted=False,compiler_invoked=False,
    source_only_lexical_preflight=preflight,independent_static_review_completed=False,
    full114_archive=dict(path=str(ARCHIVE),sha256=PIN,accepted=False),candidate_dependencies=candidates,
    baseline_dependencies=[dict(module='PvNP.RealizableHardness.TaggedFinite3LinSource',archive_member=member,
        sha256=sha(baseline),bytes=len(baseline),accepted=False)],
    direct_imports=imports,planning_argument=dict(repository=str(P),relative_path=relative,committed_head='4489537',
        committed_blob_sha256=sha(plan),heading=heading,section_sha256=sha(section.encode())),
    toolchain=dict(value=toolchain.decode().strip(),sha256=sha(toolchain)),
    mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2',public_axiom_requests=exports,
    checked_definitions=definitions,original_physical_antecedents_exact_byte_check=True,
    original_physical_antecedents_sha256=sha(header.encode()),literal_tagged_no_promise_transport=True,
    universal_external_source_contract_explicit_hypothesis=True,actual_occurrence_no_promise_explicit_hypothesis=True,
    actual_verifier_derandomization_and_scalar_composed=True,conditional_numeric_no_composed=True,
    supplied_special_strategy_upper_assumed=False,source_no_proved=False,
    sat_source_promise_instantiated=False,common_floor_discharged=False,
    historical_dependency_pins_unchanged=True,dependency_successor_recompilation_required=True,files=files)
(OUT/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(dict(source_sha256=sha(source),checks_sha256=sha((OUT/'Checks.lean').read_bytes()),
    manifest_sha256=sha((OUT/'manifest.json').read_bytes()),public_theorems=len(exports))))
