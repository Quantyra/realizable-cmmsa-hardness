"""Freeze finite local derandomization against the exact parent source."""
from pathlib import Path
import hashlib, json, re, subprocess, sys, tarfile
sys.path.insert(0, str(Path(__file__).resolve().parent))
from lean_source_static_preflight_v2 import inspect_bytes
S = Path(__file__).resolve().parent
OUT = S/'numeric-local-derandomization-offer-20261011-v1'
P = Path(r'C:\Users\dfred\Desktop\Projects\IGH\Quantyra-AI-Planning')
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PIN = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
sha = lambda b: hashlib.sha256(b).hexdigest().upper()
assert not (OUT/'manifest.json').exists()
with ARCHIVE.open('rb') as stream:
    assert hashlib.file_digest(stream,'sha256').hexdigest().upper() == PIN
member = 'lean/PvNP/RealizableHardness/ActualFiniteLaw.lean'
with tarfile.open(ARCHIVE,'r:gz') as archive:
    toolchain = archive.extractfile('lean-toolchain').read()
    dependency = archive.extractfile(member).read()
assert sha(dependency) == '8C39A4BA4045F4F6D31C92CEDDA4C5B46F50A48E4F654BF517F90E08CFD0FA32'
assert toolchain.decode().strip() == 'leanprover/lean4:v4.34.0-rc2'
source = (OUT/'ActualFiniteLocalDerandomization.lean').read_bytes()
assert sha(source) == 'C51780B7C20DCBE1BE56D858F921A33AD7F87AD9E53D5B95B39A1013E5E5E97E'
preflight = inspect_bytes(source,'ActualFiniteLocalDerandomization.lean')
code = source.decode('utf-8')
imports = re.findall(r'(?m)^import (\S+)',code)
assert imports == ['PvNP.RealizableHardness.ActualFiniteLaw','Mathlib.Data.Finset.Max','Mathlib.Tactic']
exports = re.findall(r'(?m)^theorem (\w+)',code)
definitions = re.findall(r'(?m)^def (\w+)',code)
assert len(exports) == 3 and len(definitions) == 3
checks = 'import PvNP.RealizableHardness.ActualFiniteLocalDerandomization\n\n'
for name in definitions+exports:
    checks += '#check PvNP.RealizableHardness.ActualFiniteLocalDerandomization.'+name+'\n'
for name in exports:
    checks += '#print axioms PvNP.RealizableHardness.ActualFiniteLocalDerandomization.'+name+'\n'
relative = 'docs/research/pvnp/full90-actual-rhs-numeric-no-obligations-2026-10-08.md'
plan = subprocess.run(['git','-C',str(P),'show','9949dfd:'+relative],check=True,stdout=subprocess.PIPE).stdout
heading = '## 2026-10-11 Finite private-randomness reduction for the original game'
text = plan.decode()
assert text.count(heading) == 1
section = text[text.index(heading):].split('\n## ',1)[0]
for name,value in [('Checks.lean',checks),('ARGUMENT.md','# Finite local derandomization\n\n'+section+'\n'),('.gitattributes','* -text\n')]:
    (OUT/name).write_text(value,encoding='utf-8',newline='\n')
files = []
for path in sorted(OUT.rglob('*')):
    if path.is_file():
        raw = path.read_bytes()
        files.append(dict(path=path.relative_to(OUT).as_posix(),bytes=len(raw),sha256=sha(raw),
            diagnostic='diagnostics' in path.relative_to(OUT).parts))
manifest = dict(schema=OUT.name,author='/root',story='E002/S3137',accepted=False,
    compiler_invoked=False,source_only_lexical_preflight=preflight,independent_static_review_completed=False,
    full114_archive=dict(path=str(ARCHIVE),sha256=PIN,accepted=False),
    baseline_dependencies=[dict(module='PvNP.RealizableHardness.ActualFiniteLaw',archive_member=member,
        bytes=len(dependency),sha256=sha(dependency),accepted=False)],direct_imports=imports,
    planning_argument=dict(repository=str(P),relative_path=relative,committed_head='9949dfd',
        committed_blob_sha256=sha(plan),heading=heading,section_sha256=sha(section.encode())),
    toolchain=dict(value=toolchain.decode().strip(),sha256=sha(toolchain)),
    mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2',public_axiom_requests=exports,
    checked_definitions=definitions,private_law_normalization_used=True,
    each_deterministic_answer_depends_only_on_own_question=True,
    arbitrary_real_payoff_kernel=True,actual_verifier_aggregation_instantiated=False,
    external_source_game_contract_applied=False,source_game_law_identified=False,source_no_proved=False,
    historical_dependency_pins_unchanged=True,dependency_successor_recompilation_required=True,files=files)
(OUT/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(dict(source_sha256=sha(source),checks_sha256=sha((OUT/'Checks.lean').read_bytes()),
    manifest_sha256=sha((OUT/'manifest.json').read_bytes()),public_theorems=len(exports))))
