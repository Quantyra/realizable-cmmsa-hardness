"""Repair only the planning-byte pin for the immutable v2 source offer."""
from pathlib import Path
import hashlib
import json
import subprocess

S = Path(__file__).resolve().parent
V2 = S / 'numeric-boolean-occurrence-source-offer-20261012-v2'
OUT = S / 'numeric-boolean-occurrence-source-offer-20261012-v3'
P = Path('C:/Users/dfred/Desktop/Projects/IGH/Quantyra-AI-Planning')
REL = 'docs/research/pvnp/openai-math-source-bridge-crosswalk-2026-10-06.md'
HEADING = '## 2026-10-11 Shared literal interface and exact machine-output transport argument'
CAPTURE = S / 'numeric-boolean-occurrence-source-capture-v2'
CAPTURE_INDEX = CAPTURE / 'index.json'
sha = lambda data: hashlib.sha256(data).hexdigest().upper()

assert not (OUT / 'manifest.json').exists(), 'successor already frozen'
capture_index = CAPTURE_INDEX.read_bytes()
assert sha(capture_index) == '9C66555C956F4C2F6F8667E5D2BEFA7E68E586B8493E4984494B76D9E3D77F4B'
capture = json.loads(capture_index)
captured_source = next(x for x in capture['files']
                       if x['copy_path'] == 'ActualBooleanOccurrenceSource.lean')
source = (CAPTURE / captured_source['copy_path']).read_bytes()
assert sha(source) == captured_source['sha256'] == \
    'AA2810A6CCBDD473ADF7153208B709FAAA3BF203101F7B6B3165B16725945487'

plan = subprocess.run(
    ['git', '-C', str(P), 'show', f'efc7f45:{REL}'],
    check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE).stdout
plan_text = plan.decode('utf-8')
assert plan_text.count(HEADING) == 1
section = plan_text[plan_text.index(HEADING):].split('\n## ', 1)[0]
argument = (section + '\n').encode('utf-8')
assert sha(plan) == 'AF21E3A9BFE1094225A7C6CA60DD9FA354AEA2B90C46949AEA22042D2516B5D8'
assert sha(section.encode('utf-8')) == \
    'D23149B02E90565BCE84E5016171C3D70BBCDFE912061447080BAB09C40BBE41'

for filename in ('.gitattributes', 'ActualBooleanOccurrenceSource.lean', 'Checks.lean'):
    (OUT / filename).write_bytes((V2 / filename).read_bytes())
(OUT / 'ARGUMENT.md').write_bytes(argument)
manifest = json.loads((V2 / 'manifest.json').read_bytes())
manifest['schema'] = OUT.name
manifest['planning_argument']['committed_blob_sha256'] = sha(plan)
manifest['planning_argument']['section_sha256'] = sha(section.encode('utf-8'))
manifest['planning_argument']['whole_blob_pin_verified'] = True
manifest['planning_argument']['raw_git_stdout_capture'] = True
manifest['source_offer_origin'] = {
    'path': str(V2),
    'immutable_capture_index': str(CAPTURE_INDEX),
    'immutable_capture_index_sha256': sha(capture_index),
    'source_sha256': sha(source),
    'source_edited': False,
}
manifest['files'] = [
    {'path': p.name, 'bytes': p.stat().st_size, 'sha256': sha(p.read_bytes())}
    for p in sorted(OUT.iterdir()) if p.is_file() and p.name != 'manifest.json'
]
manifest_bytes = (json.dumps(manifest, indent=2) + '\n').encode('utf-8')
(OUT / 'manifest.json').write_bytes(manifest_bytes)
print(json.dumps({
    'source_sha256': sha(source),
    'argument_sha256': sha(argument),
    'planning_blob_sha256': sha(plan),
    'manifest_sha256': sha(manifest_bytes),
}))
