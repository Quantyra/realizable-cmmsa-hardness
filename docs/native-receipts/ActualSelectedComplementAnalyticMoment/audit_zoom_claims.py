"""Scoped native receipt consistency audit; independent reviews remain separate."""
import hashlib
import json
import pathlib
import re
import tarfile

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / 'zoom-claims-manifest.json').read_text())
run = HERE / manifest['run']
archive = run / (run.name + '-evidence.tar.gz')
assert hashlib.sha256(archive.read_bytes()).hexdigest() == manifest['evidence_archive_sha256']
with tarfile.open(archive) as receipt:
    raw = {pathlib.PurePosixPath(m.name).name: receipt.extractfile(m).read()
           for m in receipt.getmembers() if m.isfile()}
assert int(raw['native-exit']) == int(raw['prebuild-0.native-exit']) == 0
pins = dict(line.split(None, 1)[::-1] for line in raw['pins.sha256'].decode().splitlines())
for name, expected in manifest['sources'].items():
    assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == expected
    assert pins[name] == expected
stdout = raw['build.stdout'].decode()
assert 'Build completed successfully' in stdout
assert not re.search(r'^error:', stdout, re.M)
assert 'sorryAx' not in stdout
profiles = {}
for export in manifest['axiom_exports']:
    full = 'PvNP.RealizableHardness.' + export
    found = re.findall(re.escape("'" + full + "' depends on axioms:") + r'\s*\[([^\]]*)\]', stdout)
    assert len(found) == 1, full
    axioms = [a.strip() for a in found[0].split(',') if a.strip()]
    assert set(axioms) <= set(manifest['allowed_axioms'])
    profiles[full] = axioms
objects = {p: h for p, h in pins.items() if p.endswith('.olean')}
assert len(objects) == 2
report = {'success': True, 'source_pins': manifest['sources'], 'object_receipt_pins': objects,
          'native_exit_codes': [0, 0], 'axiom_profiles': profiles,
          'audit_scope': 'actual receipt/source/profile consistency only',
          'final_three_lens_acceptance': 'not evaluated; see independent reviews and ledger'}
(HERE / 'zoom-claims-audit-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'success': True, 'verified_profiles': len(profiles), 'verified_sources': 2}))
