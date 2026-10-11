from pathlib import Path
import hashlib
import json
import shutil

S = Path(__file__).resolve().parent
SRC = S / 'numeric-hside-full-zoom-offer-20261011-v1'
OUT = S / 'numeric-hside-full-zoom-offer-20261011-v2'
sha = lambda b: hashlib.sha256(b).hexdigest().upper()
capture = S / 'numeric-hside-full-zoom-capture-v1/index.json'
assert sha(capture.read_bytes()) == '49ED2BE5D7C41CAE5DFF02C4185BBA8D62E9E9C61A5300904EA207A047A217B5'
raw = (SRC / 'ActualHSideFullZoom.lean').read_bytes()
assert sha(raw) == '137A4A29B4BBD402824E954A01F829218941BF8E0D4B5AE3B176CE5EACAE7357'
old = b'    sideRestriction_iff_agreesOn I copies U A W\' g K hKW T s L.1 _\n'
new = b'    sideRestriction_iff_agreesOn I copies U A W\' g K hKW T s L.1\n      ((side_full_le_iff I copies U K L.1 P.W le_sup_left).mp L.2)\n'
assert raw.count(old) == 1
successor = raw.replace(old, new)
assert successor.replace(new, old) == raw
OUT.mkdir(exist_ok=False)
for p in SRC.iterdir():
    if p.name not in ['manifest.json', 'ActualHSideFullZoom.lean']:
        shutil.copyfile(p, OUT / p.name)
(OUT / 'ActualHSideFullZoom.lean').write_bytes(successor)
argument = (OUT / 'ARGUMENT.md').read_text(encoding='utf-8')
argument += '\nV2 explicitly supplies the existing bounded-leaf containment proof in the pointwise event equivalence. All public statements, imports, other proof lines, definitions and Checks remain unchanged. V1 was frozen and captured before this disjoint successor. No compiler ran.\n'
(OUT / 'ARGUMENT.md').write_text(argument, encoding='utf-8', newline='\n')
manifest = json.loads((SRC / 'manifest.json').read_bytes())
manifest['schema'] = OUT.name
manifest['predecessor_capture_sha256'] = sha(capture.read_bytes())
manifest['predecessor_source_sha256'] = sha(raw)
manifest['exact_replacement_count'] = 1
manifest['checks_unchanged'] = (OUT / 'Checks.lean').read_bytes() == (SRC / 'Checks.lean').read_bytes()
manifest['files'] = []
for path in sorted(OUT.iterdir()):
    data = path.read_bytes()
    assert not data.startswith(b'\xef\xbb\xbf') and '\ufffd' not in data.decode('utf-8')
    manifest['files'].append(dict(path=path.name, bytes=len(data), sha256=sha(data)))
(OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(successor),
    manifest_sha256=sha((OUT / 'manifest.json').read_bytes()), checks_unchanged=True)))
