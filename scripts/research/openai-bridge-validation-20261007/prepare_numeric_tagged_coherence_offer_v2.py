from pathlib import Path
import hashlib
import json

S = Path(__file__).resolve().parent
OLD = S / 'numeric-tagged-common-leaf-offer-20261011-v1'
OUT = S / 'numeric-tagged-common-leaf-offer-20261011-v2'
CAPTURE = S / 'numeric-tagged-common-leaf-capture-v1'
V1_SOURCE = '7CE2900696DCD1787D8076E053FB835408C7DF0557F7C717C8E1856F23C067F3'
V1_INDEX = 'F784ADD50E8C218BA3EE3BE8ED6E95621A83D7F2083D7894FB0B4FECAB1A5C2C'

def digest(data):
    return hashlib.sha256(data).hexdigest().upper()

assert digest((CAPTURE / 'index.json').read_bytes()) == V1_INDEX
old = (OLD / 'ActualTaggedCommonLeafCoherence.lean').read_bytes()
assert digest(old) == V1_SOURCE
assert (CAPTURE / 'ActualTaggedCommonLeafCoherence.lean').read_bytes() == old
before = b'(M := I.GlobalVar \xe2\x86\x92 ZMod 2)'
after = b'(M := TaggedAmbient I copies)'
assert old.count(before) == 1
new = old.replace(before, after)
assert new.replace(after, before) == old
assert b'I.GlobalVar' not in new
assert not OUT.exists(), 'Refuse to overwrite a successor offer'
OUT.mkdir()
for name in ['Checks.lean', 'ARGUMENT.md', '.gitattributes']:
    (OUT / name).write_bytes((OLD / name).read_bytes())
(OUT / 'ActualTaggedCommonLeafCoherence.lean').write_bytes(new)
manifest = json.loads((OLD / 'manifest.json').read_text(encoding='utf-8'))
manifest['schema'] = 'numeric-tagged-common-leaf-offer-v2'
manifest['predecessor'] = {'source_sha256': V1_SOURCE, 'capture_index_sha256': V1_INDEX}
manifest['repair'] = 'Change the private span_span_coe_preimage M parameter to TaggedAmbient I copies; exact reverse reconstruction preserves all remaining source and all Checks bytes.'
manifest['files'] = []
for path in sorted(OUT.iterdir()):
    raw = path.read_bytes()
    raw.decode('utf-8')
    assert not raw.startswith(b'\xef\xbb\xbf')
    manifest['files'].append({'path': path.name, 'bytes': len(raw), 'sha256': digest(raw)})
(OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8', newline='\n')
print(json.dumps({'source_sha256': digest(new), 'manifest_sha256': digest((OUT/'manifest.json').read_bytes()), 'reverse_reconstruction': True, 'checks_unchanged': (OUT/'Checks.lean').read_bytes() == (OLD/'Checks.lean').read_bytes()}, indent=2))
