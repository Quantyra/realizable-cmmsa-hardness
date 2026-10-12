"""Freeze the shared-interface Boolean occurrence transfer candidate."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from lean_source_static_preflight_v2 import inspect_bytes
from lean_source_static_preflight_v1 import code_only

S = Path(__file__).resolve().parent
P = Path('C:/Users/dfred/Desktop/Projects/IGH/Quantyra-AI-Planning')
OUT = S / 'numeric-boolean-occurrence-source-offer-20261012-v2'
sha = lambda data: hashlib.sha256(data).hexdigest().upper()
assert not (OUT / 'manifest.json').exists(), 'offer already frozen'

old = S / 'numeric-boolean-occurrence-source-offer-20261011-v1'
old_source = (old / 'ActualBooleanOccurrenceSource.lean').read_bytes()
assert sha(old_source) == 'BFDA6801B7ADC0720D345B9B0655EBE18A0BD15E15606B96FB251FC2DC28DFAD'
text = old_source.decode('utf-8')
text = text.replace(
    'import PvNP.RealizableHardness.ActualOccurrenceGapBridge\n',
    'import PvNP.RealizableHardness.ActualOccurrenceGapBridge\n'
    'import PvNP.RealizableHardness.BooleanParityInput\n',
    1)
text = text.replace(
    'open ActualOccurrenceAllocation ActualOccurrenceGapBridge ActualOriginalSourceNo',
    'open ActualOccurrenceAllocation ActualOccurrenceGapBridge ActualOriginalSourceNo BooleanParityInput',
    1)
text = text.replace(
    'The record mirrors the inspected upstream fields, but this CMMSA candidate\n'
    'does not import or certify the upstream reduction across toolchains.',
    'This CMMSA candidate imports the shared literal Boolean input interface; it\n'
    'does not certify the upstream reduction across toolchains.',
    1)
start = text.index('structure Equation (Name : Type) where\n')
end = text.index('def asInstance (I : Input)', start)
text = text[:start] + text[end:]
text = text.replace('def asInstance (I : Input)',
                    'def asInstance (I : BooleanParityInput.Input)', 1)
text = re.sub(
    r'(?s)def failureCount \(I : Input\).*?theorem rows_positive \(I : Input\)',
    'theorem rows_positive (I : BooleanParityInput.Input)', text, count=1)
text = text.replace('(e : Equation Name)', '(e : BooleanParityInput.Equation Name)')
text = text.replace('(I : Input)', '(I : BooleanParityInput.Input)')
text = re.sub(r'(?<![A-Za-z0-9_.])failureCount I a',
              'BooleanParityInput.failureCount I a', text)
text = re.sub(r'(?<![A-Za-z0-9_.])failureRate I a',
              'BooleanParityInput.failureRate I a', text)
text = text.replace('satisfied (I.equations.get r) a',
                    'BooleanParityInput.satisfied (I.equations.get r) a')
text = text.replace('failureRate, Rat.cast_div',
                    'BooleanParityInput.failureRate, Rat.cast_div')
text = text.replace('unfold failureCount',
                    'unfold BooleanParityInput.failureCount')
text = text.replace('def asInstance (I : BooleanParityInput.Input)',
                    'def asInstance (I : BooleanParityInput.Input)', 1)
# Every declaration now uses the single imported data model and its semantics.
assert 'structure Equation' not in text and 'structure Input' not in text
assert not re.search(r'(?m)^def (?:satisfied|failureCount|failureRate)\b', text)
assert text.count('import PvNP.RealizableHardness.BooleanParityInput') == 1
source = text.encode('utf-8')
preflight = inspect_bytes(source, 'ActualBooleanOccurrenceSource.lean')
code = code_only(text)
imports = re.findall(r'(?m)^import (\S+)', code)
assert imports == [
    'PvNP.RealizableHardness.ActualOccurrenceGapBridge',
    'PvNP.RealizableHardness.BooleanParityInput',
    'Mathlib.Data.List.OfFn',
    'Mathlib.Tactic',
]
names = re.findall(r'(?m)^(?:theorem|def|structure) (\w+)', code)
theorems = re.findall(r'(?m)^theorem (\w+)', code)
assert len(names) == len(set(names))
for name in [
    'failureCount_index_sum', 'raw_violations_eq_failureCount',
    'raw_violations_eq_failureCount_bit', 'failureRate_cast',
    'raw_no_of_failureRate', 'raw_yes_of_failureRate',
    'actual_no_of_failure_quarter', 'actual_yes_of_failureRate',
]:
    assert name in theorems

checks = 'import PvNP.RealizableHardness.ActualBooleanOccurrenceSource\n\n'
ns = 'PvNP.RealizableHardness.ActualBooleanOccurrenceSource.'
checks += ''.join(f'#check {ns}{name}\n' for name in names)
checks += ''.join(f'#print axioms {ns}{name}\n' for name in theorems)
checks += '\n#print axioms PvNP.RealizableHardness.BooleanParityInput.failureRate\n'

rel = 'docs/research/pvnp/openai-math-source-bridge-crosswalk-2026-10-06.md'
plan = subprocess.run(
    ['git', '-C', str(P), 'show', f'efc7f45:{rel}'],
    check=True, stdout=subprocess.PIPE).stdout
heading = '## 2026-10-11 Shared literal interface and exact machine-output transport argument'
plan_text = plan.decode('utf-8')
assert plan_text.count(heading) == 1
section = plan_text[plan_text.index(heading):].split('\n## ', 1)[0]
for filename, value in [
    ('ActualBooleanOccurrenceSource.lean', source),
    ('Checks.lean', checks.encode('utf-8')),
    ('ARGUMENT.md', (section + '\n').encode('utf-8')),
    ('.gitattributes', b'* -text\n'),
]:
    (OUT / filename).write_bytes(value)

gap = S / 'numeric-actual-occurrence-gap-capture-v1'
gap_index = (gap / 'index.json').read_bytes()
assert sha(gap_index) == 'A4366E4354F2E8379E61F0C6C2B4C83DFCC2F9A0EF0E04DA841D28C14B5D04F9'
gap_row = next(row for row in json.loads(gap_index)['files']
               if row['copy_path'] == 'ActualOccurrenceGapBridge.lean')
gap_source = gap / gap_row['copy_path']
assert sha(gap_source.read_bytes()) == gap_row['sha256']

shared = S / 'shared-boolean-parity-input-capture-v1'
shared_index = (shared / 'index.json').read_bytes()
assert sha(shared_index) == '75D4A29565E58DB905B614DDFC84E83856F82AD626384FC6F5B20BE09356AB3F'
shared_row = next(row for row in json.loads(shared_index)['files']
                  if row['copy_path'] == 'BooleanParityInput.lean')
shared_source = shared / shared_row['copy_path']
assert sha(shared_source.read_bytes()) == shared_row['sha256'] == \
    '704B76A68488A6473613A2B69C53A962A54E9914AC298FE24CFAED78865A1414'

upstream_readback = S / 'upstream-uncloned-binary-source-readback-v1' / 'result.json'
readback = upstream_readback.read_bytes()
assert sha(readback) == '8B52463294CA180A43B7070C19256560A0E8F94C3A3C1930521A481750DB16B1'

files = []
for path in sorted(OUT.iterdir()):
    if path.is_file():
        data = path.read_bytes()
        files.append({'path': path.name, 'bytes': len(data), 'sha256': sha(data)})
manifest = {
    'schema': OUT.name,
    'author': '/root/occurrence_bridge',
    'story': 'E002/S3137',
    'accepted': False,
    'compiler_invoked': False,
    'independent_static_review_completed': False,
    'source_only_lexical_preflight': preflight,
    'direct_imports': imports,
    'public_axiom_requests': theorems,
    'checked_declarations': names,
    'toolchain': 'leanprover/lean4:v4.34.0-rc2',
    'mathlib_revision': 'e06eff5f95374108acfaf19f1ff7473aa7771df2',
    'candidate_dependencies': [
        {'module': 'PvNP.RealizableHardness.ActualOccurrenceGapBridge',
         'path': str(gap_source), 'bytes': gap_row['bytes'], 'sha256': gap_row['sha256'],
         'capture_index': str(gap / 'index.json'), 'capture_sha256': sha(gap_index),
         'accepted': False},
        {'module': 'PvNP.RealizableHardness.BooleanParityInput',
         'path': str(shared_source), 'bytes': shared_row['bytes'], 'sha256': shared_row['sha256'],
         'capture_index': str(shared / 'index.json'), 'capture_sha256': sha(shared_index),
         'accepted': False},
    ],
    'upstream_semantic_readback': {'path': str(upstream_readback), 'bytes': len(readback),
                                   'sha256': sha(readback)},
    'planning_argument': {
        'repository': str(P), 'relative_path': rel, 'committed_head': 'efc7f45',
        'committed_blob_sha256': sha(plan), 'heading': heading,
        'section_sha256': sha(section.encode('utf-8')),
    },
    'shared_semantics_imported_without_local_redeclaration': True,
    'repeated_equations_and_owners_retained': True,
    'assignment_conversion_both_directions': True,
    'exact_indexed_failure_count_translated': True,
    'rational_fraction_denominator_preserved': True,
    'concrete_occurrence_yes_and_no_composed': True,
    'upstream_reduction_imported': False,
    'upstream_to_local_typed_interface_proved': False,
    'sat_source_promise_instantiated': False,
    'encoded_runtime_proved': False,
    'historical_dependency_pins_unchanged': True,
    'dependency_successor_recompilation_required': True,
    'files': files,
}
manifest_bytes = (json.dumps(manifest, indent=2) + '\n').encode('utf-8')
(OUT / 'manifest.json').write_bytes(manifest_bytes)
print(json.dumps({
    'source_sha256': sha(source),
    'checks_sha256': sha((OUT / 'Checks.lean').read_bytes()),
    'argument_sha256': sha((OUT / 'ARGUMENT.md').read_bytes()),
    'manifest_sha256': sha(manifest_bytes),
    'public_theorems': len(theorems),
    'declarations': len(names),
}))
