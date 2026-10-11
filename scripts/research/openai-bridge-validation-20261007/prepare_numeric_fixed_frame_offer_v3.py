from pathlib import Path
import hashlib
import json
import tarfile

S = Path(__file__).resolve().parent
OLD = S / 'numeric-fixed-frame-transport-capture-v2'
OUT = S / 'numeric-fixed-frame-transport-offer-20261011-v3'
sha = lambda raw: hashlib.sha256(raw).hexdigest().upper()
index = json.loads((OLD/'index.json').read_bytes())
for row in index['files']:
    assert sha((OLD/row['copy']).read_bytes()) == row['sha256']
assert not OUT.exists()
source = (OLD/'ActualCoordinateStarDensity.lean').read_bytes()
assert sha(source) == '4BA47E5F95985C5FA214490C909A7B6D3DE3F04B876A8A391086B851DF1C70ED'
line = b'open PvNP.RealizableHardness.ActualTaggedConcreteStarLaw\n'
anchor = b'open PvNP.RealizableHardness.ActualTaggedComplementIncidence\n'
assert source.count(anchor) == 1
new = source.replace(anchor, anchor + line)
assert new.replace(line, b'') == source
archive = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
assert sha(archive.read_bytes()) == '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
with tarfile.open(archive, 'r:gz') as f:
    member = 'lean/PvNP/RealizableHardness/ActualTaggedConcreteStarLaw.lean'
    raw = f.extractfile(member).read()
assert b'def TaggedGoodU (J : Nat)' in raw
OUT.mkdir()
for name in ['.gitattributes', 'ActualCoordinateStarDensityChecks.lean', 'ARGUMENT-AND-API-MAP.md']:
    (OUT/name).write_bytes((OLD/name).read_bytes())
(OUT/'ActualCoordinateStarDensity.lean').write_bytes(new)
(OUT/'REPAIR.md').write_text('''# Namespace repair

Root inspected the v2 fixed-frame source while composing the ordinary leaf marginal. TaggedGoodU is defined in ActualTaggedConcreteStarLaw; opening its importing namespaces does not open this namespace. The sole Lean change is an explicit open of that already-imported namespace. Every declaration, proof body, import and Checks byte remains unchanged; removing that single line exactly reconstructs captured v2.

This is an uncompiled successor, not an accepted proof. The original complete argument and all earlier offers remain preserved.

Remaining to-do list: native verification and the existing refresh/decoder/certification scope.
''', encoding='utf-8', newline='\n')
manifest = json.loads((OLD/'manifest.json').read_bytes())
manifest['offer'] = OUT.name
manifest['source']['sha256'] = sha(new)
manifest['supersedes'] = dict(capture=OLD.name, capture_index_sha256=sha((OLD/'index.json').read_bytes()), exact_repair='One explicit namespace open; reverse byte reconstruction passed')
manifest['additional_inspected_dependency'] = dict(member=member, sha256=sha(raw))
manifest['files'] = [dict(path=p.name, bytes=p.stat().st_size, sha256=sha(p.read_bytes())) for p in sorted(OUT.iterdir())]
(OUT/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(new), manifest_sha256=sha((OUT/'manifest.json').read_bytes()), old_index_sha256=sha((OLD/'index.json').read_bytes())), indent=2))
