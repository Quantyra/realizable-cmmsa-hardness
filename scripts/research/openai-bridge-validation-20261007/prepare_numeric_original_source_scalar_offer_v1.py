"""Freeze the exact count denominator and strict source exponent comparison."""
from pathlib import Path
import hashlib, json, re, subprocess, sys, tarfile
sys.path.insert(0, str(Path(__file__).resolve().parent))
from lean_source_static_preflight_v2 import inspect_bytes
S = Path(__file__).resolve().parent
OUT = S/'numeric-original-source-scalar-offer-20261011-v1'
P = Path('C:/Users/dfred/Desktop/Projects/IGH/Quantyra-AI-Planning')
ARCHIVE = Path('C:/Users/dfred/.quantyra/builder02/full114-exact-real-complex-operators-repair4-resource02/input-archive.tar.gz')
PIN = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
sha = lambda b: hashlib.sha256(b).hexdigest().upper()
assert not (OUT/'manifest.json').exists()
with ARCHIVE.open('rb') as f:
    assert hashlib.file_digest(f, 'sha256').hexdigest().upper() == PIN
with tarfile.open(ARCHIVE, 'r:gz') as t:
    toolchain = t.extractfile('lean-toolchain').read()
assert toolchain.decode().strip() == 'leanprover/lean4:v4.34.0-rc2'
candidates = []
for module, directory, sourcepin, cappin in [
    ('ActualCountedAssignmentScore','numeric-counted-assignment-score-capture-v1',
     'ADADC0C54FDD6CE27912A9C550E723FD116A183233CE48EDF3C238B816BBC2FD',
     '7369AF940ADDF9F4B0B2741D3F363912AA29D33A13710C7846C8D8F5F80CBBB4'),
    ('ActualMaximalCountSpecialization','numeric-maximal-count-specialization-capture-v1',
     'FD24114B0AEAF07FB276165C50A12D5AFC41052BC3D1D08045048556A5E0204B',
     'AFA10520585DE7D8B3C6D448D1549C27411C33401F2C164AD584C357B48C12B3')]:
    cap = S/directory
    index = (cap/'index.json').read_bytes()
    assert sha(index) == cappin and sourcepin in index.decode()
    path = cap/(module+'.lean')
    raw = path.read_bytes()
    assert sha(raw) == sourcepin
    candidates.append(dict(module='PvNP.RealizableHardness.'+module,path=str(path),
        bytes=len(raw),sha256=sourcepin,capture_index=str(cap/'index.json'),
        capture_sha256=cappin,accepted=False))
source = (OUT/'ActualOriginalSourceScalar.lean').read_bytes()
preflight = inspect_bytes(source,'ActualOriginalSourceScalar.lean')
code = source.decode('utf-8')
imports = re.findall(r'(?m)^import (\S+)',code)
assert imports == [x['module'] for x in candidates]
exports = re.findall(r'(?m)^theorem (\w+)',code)
definitions = re.findall(r'(?m)^def (\w+)',code)
assert len(exports) == 5 and len(definitions) == 1
checks = 'import PvNP.RealizableHardness.ActualOriginalSourceScalar\n\n'
for name in definitions+exports:
    checks += '#check PvNP.RealizableHardness.ActualOriginalSourceScalar.'+name+'\n'
for name in exports:
    checks += '#print axioms PvNP.RealizableHardness.ActualOriginalSourceScalar.'+name+'\n'
relative = 'docs/research/pvnp/full90-actual-rhs-numeric-no-obligations-2026-10-08.md'
plan = subprocess.run(['git','-C',str(P),'show','babde59:'+relative],check=True,stdout=subprocess.PIPE).stdout
heading = '## 2026-10-11 Primary outer exponent and final scalar contradiction argument'
text = plan.decode()
assert text.count(heading) == 1
section = text[text.index(heading):].split('\n## ',1)[0]
for name,value in [('Checks.lean',checks),('ARGUMENT.md','# Source scalar comparison\n\n'+section+'\n'),('.gitattributes','* -text\n')]:
    (OUT/name).write_text(value,encoding='utf-8',newline='\n')
files = []
for path in sorted(OUT.rglob('*')):
    if path.is_file():
        raw = path.read_bytes()
        files.append(dict(path=path.relative_to(OUT).as_posix(),bytes=len(raw),sha256=sha(raw),
            diagnostic='diagnostics' in path.relative_to(OUT).parts))
manifest = dict(schema=OUT.name,author='/root',story='E002/S3137',accepted=False,
    compiler_invoked=False,source_only_lexical_preflight=preflight,independent_static_review_completed=False,
    full114_archive=dict(path=str(ARCHIVE),sha256=PIN,accepted=False),candidate_dependencies=candidates,
    direct_imports=imports,planning_argument=dict(repository=str(P),relative_path=relative,
        committed_head='babde59',committed_blob_sha256=sha(plan),heading=heading,section_sha256=sha(section.encode())),
    toolchain=dict(value=toolchain.decode().strip(),sha256=sha(toolchain)),
    mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2',public_axiom_requests=exports,
    checked_definitions=definitions,exact_combined_count_denominator=True,
    strict_fixed_coefficient_and_positive_height_required=True,primary_big_omega_constant_not_numeric=True,
    actual_verifier_aggregation_instantiated=False,external_source_game_contract_applied=False,
    source_game_law_identified=False,source_no_proved=False,common_floor_discharged=False,
    historical_dependency_pins_unchanged=True,dependency_successor_recompilation_required=True,files=files)
(OUT/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(dict(source_sha256=sha(source),checks_sha256=sha((OUT/'Checks.lean').read_bytes()),
    manifest_sha256=sha((OUT/'manifest.json').read_bytes()),public_theorems=len(exports))))
