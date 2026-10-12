from pathlib import Path
import hashlib, json, re, tarfile

S = Path(__file__).resolve().parent
OLD = S / 'numeric-maximal-count-guards-offer-20261011-v1'
CAP = S / 'numeric-maximal-count-guards-capture-v1'
OUT = S / 'numeric-maximal-count-guards-offer-20261011-v2'
sha = lambda b: hashlib.sha256(b).hexdigest().upper()
assert not OUT.exists()
source = (OLD / 'ActualMaximalCountGuards.lean').read_bytes()
assert sha(source) == '6C01F6A58BAC0645D307EB9B7436568E00DA79171448C0C1D06696E92D1D1647'
assert source == (CAP / 'ActualMaximalCountGuards.lean').read_bytes()
assert sha((CAP / 'index.json').read_bytes()) == '037BE52EAC655132616E606E96BF9041844C14976ADAE4E4A72E8FDDBC5C4AA4'
manifest = json.loads((OLD / 'manifest.json').read_bytes())
for row in manifest['files']:
    assert sha((OLD / row['path']).read_bytes()) == row['sha256']
archive_path = Path(manifest['full114_archive']['path'])
with archive_path.open('rb') as f:
    assert hashlib.file_digest(f, 'sha256').hexdigest().upper() == manifest['full114_archive']['sha256']
with tarfile.open(archive_path, 'r:gz') as archive:
    for row in manifest['dependencies']:
        raw = archive.extractfile(row['member']).read()
        assert sha(raw) == row['sha256'] and len(raw) == row['bytes']
edits = [
    (b'pow_le_pow_left\xe2\x82\x80 (by norm_num) (by norm_num)\n',
     b'pow_le_pow_left\xe2\x82\x80 (by norm_num) (by norm_num) r\n'),
    (b'pow_le_pow_left\xe2\x82\x80 hdelta hdeltarho\n',
     b'pow_le_pow_left\xe2\x82\x80 hdelta hdeltarho 3\n'),
    (b'convert hc using 1 <;> ring', b'convert hc using 1 <;> field_simp <;> ring')]
new = source
for before, after in edits:
    assert new.count(before) == 1, before
    new = new.replace(before, after)
reverse = new
for before, after in reversed(edits):
    assert reverse.count(after) == 1
    reverse = reverse.replace(after, before)
assert reverse == source
headers = lambda b: re.findall(rb'(?m)^theorem\s+\w+[\s\S]*?:= by', b)
assert headers(new) == headers(source) and len(headers(new)) == 5
assert not new.startswith(b'\xef\xbb\xbf') and '\ufffd' not in new.decode('utf-8')
mathlib = S / 'full107-trace-qualified-source-record-v1/review-sources/external/Mathlib/Algebra/Order/GroupWithZero/Basic.lean'
api = mathlib.read_bytes()
assert b': \xe2\x88\x80 n, a ^ n \xe2\x89\xa4 b ^ n' in api
OUT.mkdir()
for name in ['.gitattributes', 'Checks.lean', 'ARGUMENT.md']:
    (OUT / name).write_bytes((OLD / name).read_bytes())
(OUT / 'ActualMaximalCountGuards.lean').write_bytes(new)
repair = dict(kind='source-only-static-api-and-denominator-repair', accepted=False,
    compiler_invoked=False, old_source_sha256=sha(source), new_source_sha256=sha(new),
    unchanged_public_headers=True, unchanged_checks=True, exact_inverse_reconstruction=True,
    edits=[dict(before=a.decode(), after=b.decode()) for a,b in edits],
    mathlib_api=dict(path=str(mathlib), sha256=sha(api)),
    historical_v1_unchanged=True, dependent_execution_rebind_required=True)
(OUT / 'repair.json').write_text(json.dumps(repair, indent=2)+'\n', encoding='utf-8', newline='\n')
manifest.update(schema=OUT.name, predecessor_capture=str(CAP/'index.json'),
    predecessor_capture_sha256=sha((CAP/'index.json').read_bytes()),
    predecessor_manifest_sha256=sha((OLD/'manifest.json').read_bytes()),
    static_repair=repair, files=[])
for path in sorted(OUT.iterdir()):
    raw = path.read_bytes()
    manifest['files'].append(dict(path=path.name, bytes=len(raw), sha256=sha(raw)))
(OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(new), checks_sha256=sha((OUT/'Checks.lean').read_bytes()),
    manifest_sha256=sha((OUT/'manifest.json').read_bytes()), exact_inverse_reconstruction=True)))
