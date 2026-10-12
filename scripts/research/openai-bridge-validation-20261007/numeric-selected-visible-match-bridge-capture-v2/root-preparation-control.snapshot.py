from pathlib import Path
import hashlib, json, re

S = Path(__file__).resolve().parent
OLD = S / 'numeric-selected-visible-match-bridge-offer-20261011-v1'
CAP = S / 'numeric-selected-visible-match-bridge-capture-v1'
OUT = S / 'numeric-selected-visible-match-bridge-offer-20261011-v2'
sha = lambda b: hashlib.sha256(b).hexdigest().upper()
assert not OUT.exists()
source = (OLD / 'ActualSelectedVisibleMatchBridge.lean').read_bytes()
assert sha(source) == '775A4D86153E2F1E3C523B0137D62E4F8402BB90FCE0A068BFE8E7AD4FF31F28'
assert source == (CAP / 'ActualSelectedVisibleMatchBridge.lean').read_bytes()
index_raw = (CAP / 'index.json').read_bytes()
assert sha(index_raw) == '7F5A4864C12B5126F762CFFD9AB40988FBD5E0A8D0A55D30F2D2E023ABF874B7'
old_manifest = (OLD / 'manifest.json').read_bytes()
assert sha(old_manifest) == 'BF73E2ED65168E7E3F7CE89D9D76DA25ABA09F40367407309685D33B1D06E226'
manifest = json.loads(old_manifest)
for row in manifest['files']:
    assert sha((OLD / row['path']).read_bytes()) == row['sha256']
for row in manifest['candidate_dependencies']:
    assert sha(Path(row['path']).read_bytes()) == row['sha256']
    assert sha(Path(row['capture_index']).read_bytes()) == row['capture_sha256']
before = b'open ActualStarAffineFunctionalSelection\n'
after = before + b'open ActualOriginalLawFullDecoderIntegration\n'
assert source.count(before) == 1
new = source.replace(before, after)
assert new.replace(after, before) == source
headers = lambda raw: re.findall(rb'(?m)^theorem\s+\w+[\s\S]*?:= by', raw)
assert headers(new) == headers(source) and len(headers(new)) == 1
assert not new.startswith(b'\xef\xbb\xbf') and '\ufffd' not in new.decode('utf-8')
OUT.mkdir()
for name in ['Checks.lean', 'ARGUMENT.md', '.gitattributes']:
    (OUT / name).write_bytes((OLD / name).read_bytes())
(OUT / 'ActualSelectedVisibleMatchBridge.lean').write_bytes(new)
repair = dict(kind='missing-namespace-source-repair', accepted=False, compiler_invoked=False,
    namespace='ActualOriginalLawFullDecoderIntegration', declaration='actualFullDecoderFavorable',
    old_source_sha256=sha(source), new_source_sha256=sha(new),
    unchanged_public_headers=True, unchanged_checks=True, unchanged_proofs=True,
    exact_inverse_reconstruction=True, immutable_predecessor_unchanged=True,
    predecessor_capture=str(CAP/'index.json'), predecessor_capture_sha256=sha(index_raw),
    predecessor_diagnostics_retained_in_parent=True, capture_terminal_chunk='00badb')
(OUT/'repair.json').write_text(json.dumps(repair, indent=2)+'\n', encoding='utf-8', newline='\n')
manifest.update(schema=OUT.name, predecessor_manifest_sha256=sha(old_manifest),
    predecessor_capture=str(CAP/'index.json'), predecessor_capture_sha256=sha(index_raw),
    static_repair=repair, files=[])
for path in sorted(OUT.iterdir()):
    raw = path.read_bytes()
    manifest['files'].append(dict(path=path.name, bytes=len(raw), sha256=sha(raw), candidate_scope=True))
(OUT/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(new), checks_sha256=sha((OUT/'Checks.lean').read_bytes()),
    manifest_sha256=sha((OUT/'manifest.json').read_bytes()), exact_inverse_reconstruction=True)))
