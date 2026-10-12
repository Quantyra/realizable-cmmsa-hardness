"""Freeze the concrete total original iid strategy and physical application."""
from pathlib import Path
import hashlib, json, re, subprocess, sys, tarfile
sys.path.insert(0, str(Path(__file__).resolve().parent))
from lean_source_static_preflight_v2 import inspect_bytes
S = Path(__file__).resolve().parent
OUT = S/'numeric-total-ordered-strategy-offer-20261011-v1'
P = Path(r'C:\Users\dfred\Desktop\Projects\IGH\Quantyra-AI-Planning')
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PIN = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
sha = lambda b: hashlib.sha256(b).hexdigest().upper()
assert not (OUT/'manifest.json').exists()
with ARCHIVE.open('rb') as stream:
    assert hashlib.file_digest(stream, 'sha256').hexdigest().upper() == PIN
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    toolchain = archive.extractfile('lean-toolchain').read()
assert toolchain.decode().strip() == 'leanprover/lean4:v4.34.0-rc2'
candidates = []
for module, directory, sourcepin, cappin in [
    ('ActualOccurrenceAdviceLaw','numeric-occurrence-advice-law-capture-v1',
     '3F602F6ADDDA1AAEE52C1081CA23C427173975B61F09E29FE0590274C3DD0FD8',
     '85D996B0654277F4E435962506A070A9F7675A35DB02413B0E58C858272626E4'),
    ('ActualLocalQuestionLaw','numeric-decay-namespace-repair-capture-v1',
     'AA528979F5B0D348D4C30BFBDA044AA5C17F21B118691C2281F6D7615F135CCF',
     '87CD0A81AC0EEEBC5C188CBEA914D6ED753BBA6AFD8E7DFE9C18C315ABCDF190'),
    ('ActualOriginalRealRowLaw','numeric-original-real-row-law-capture-v1',
     'F393355475C2EE187363B1877622D79EB77663A0696D7800D7A4980C97A09BDA',
     'DFB26F58E641FF5433BC563FDD320ABDA3EEB68B6B76F8B7F8FB1D20AD63C497')]:
    capdir = S/directory
    index = (capdir/'index.json').read_bytes()
    assert sha(index) == cappin and sourcepin in index.decode()
    dependency = capdir/(module+'.lean')
    raw = dependency.read_bytes()
    assert sha(raw) == sourcepin
    candidates.append(dict(module='PvNP.RealizableHardness.'+module,path=str(dependency),
        bytes=len(raw),sha256=sourcepin,capture_index=str(capdir/'index.json'),
        capture_sha256=cappin,accepted=False))
source = (OUT/'ActualTotalOrderedStrategy.lean').read_bytes()
assert sha(source) == '45143B0568DC332AC4F99D68E7DF8FAF87C8AD7A50615862F277678D16A418DF'
preflight = inspect_bytes(source,'ActualTotalOrderedStrategy.lean')
code = source.decode('utf-8')
imports = re.findall(r'(?m)^import (\S+)',code)
assert imports == [r['module'] for r in candidates]
exports = re.findall(r'(?m)^theorem (\w+)',code)
definitions = re.findall(r'(?m)^def (\w+)',code)
assert len(exports) == 9 and len(definitions) == 5
checks = 'import PvNP.RealizableHardness.ActualTotalOrderedStrategy\n\n'
for name in definitions+exports:
    checks += '#check PvNP.RealizableHardness.ActualTotalOrderedStrategy.'+name+'\n'
for name in exports:
    checks += '#print axioms PvNP.RealizableHardness.ActualTotalOrderedStrategy.'+name+'\n'
relative = 'docs/research/pvnp/full90-actual-rhs-numeric-no-obligations-2026-10-08.md'
plan = subprocess.run(['git','-C',str(P),'show','d262519:'+relative],check=True,stdout=subprocess.PIPE).stdout
heading = '## 2026-10-11 Concrete total iid strategy composition and namespace repair'
text = plan.decode()
assert text.count(heading) == 1
section = text[text.index(heading):].split('\n## ',1)[0]
argument = '# Concrete total original iid strategy\n\nE002/S3137. UNCOMPILED and UNACCEPTED.\n\n'+section+'\n'
for name,value in [('Checks.lean',checks),('ARGUMENT.md',argument),('.gitattributes','* -text\n')]:
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
        committed_head='d262519',committed_blob_sha256=sha(plan),heading=heading,section_sha256=sha(section.encode())),
    toolchain=dict(value=toolchain.decode().strip(),sha256=sha(toolchain)),
    mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2',public_axiom_requests=exports,
    checked_definitions=definitions,total_original_local_strategies_instantiated=True,
    original_occurrence_advice_product_preserved=True,exact_eligible_score_identity_present=True,
    eligible_domination_proved_not_assumed=True,exact_iid_eligibility_factor=True,
    actual_padded_physical_to_iid_mean_application=True,eligibility_factor_charged_once=True,
    supplied_final_probability_assumed=False,external_source_game_contract_applied=False,
    source_game_law_identified=False,source_no_proved=False,external_count_explicit_hypothesis=True,
    historical_dependency_pins_unchanged=True,dependency_successor_recompilation_required=True,files=files)
(OUT/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(dict(source_sha256=sha(source),checks_sha256=sha((OUT/'Checks.lean').read_bytes()),
    manifest_sha256=sha((OUT/'manifest.json').read_bytes()),public_theorems=len(exports))))
