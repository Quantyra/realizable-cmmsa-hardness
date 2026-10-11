"""Create one disjoint, statement-preserving successor after capture ACK."""
from pathlib import Path
import hashlib
import json

BASE = Path(__file__).resolve().parent
OLD = BASE / 'numeric-robust-real-offer-20261011-v1'
NEW = BASE / 'numeric-robust-real-offer-20261011-v2'

def sha(data):
    return hashlib.sha256(data).hexdigest().upper()

def main():
    assert not NEW.exists(), 'Never overwrite an offered successor'
    old_source = (OLD / 'ActualNumericRobustReal.lean').read_bytes()
    assert sha(old_source) == '6B573265E5E2B136BA1F0EE570350609EBE4925DD04D27F51575CC07820BFFCC'
    old_manifest = (OLD / 'manifest.json').read_bytes()
    assert sha(old_manifest) == '387E1A0A132624BA91C6E30048AADC0374FC67BDEF09C54ABA1FA03FB65F5B0C'
    old = b'  have hp : 1 \xe2\x89\xa4 2 ^ (r * n + 2 * h + 3) := by positivity'
    new = (b'  have hp : 1 \xe2\x89\xa4 2 ^ (r * n + 2 * h + 3) :=\n'
           b'    Nat.one_le_pow (r * n + 2 * h + 3) 2 (by norm_num)')
    assert old_source.count(old) == 1
    successor = old_source.replace(old, new)
    assert successor.replace(new, old) == old_source
    manifest = json.loads(old_manifest)
    files = {}
    for name, expected in manifest['offered_files'].items():
        data = (OLD / name).read_bytes()
        assert len(data) == expected['bytes'] and sha(data) == expected['sha256'], name
        files[name] = data
    files['ActualNumericRobustReal.lean'] = successor
    files['ARGUMENT-AND-API-MAP.md'] += (
        '\n## Disjoint v2 source repair\n\n'
        'After Sol acknowledged immutable v1 capture CA49087DCA8531CBFE4954E57351F5A314B1B71DE916FE1CDAF67A5008592052, '
        'root replaced the private horizon proof of 1<=2^k by an explicit Nat.one_le_pow invocation. '
        'This avoids relying on positivity to prove a lower bound with left side one. '
        'The change reverses exactly to the preserved v1 bytes. All six public statements, '
        'definitions and Checks are unchanged. This is a source-level repair, not a compiler result.\n'
    ).encode('utf-8')
    for data in files.values():
        assert not data.startswith(b'\xef\xbb\xbf')
        assert '\ufffd' not in data.decode('utf-8', errors='strict')
    manifest['offer'] = NEW.name
    manifest['predecessor_manifest_sha256'] = sha(old_manifest)
    manifest['predecessor_capture_index_sha256'] = 'CA49087DCA8531CBFE4954E57351F5A314B1B71DE916FE1CDAF67A5008592052'
    manifest['repair'] = 'One private Nat lower-bound proof uses explicit Nat.one_le_pow; exact inverse reconstruction passed'
    manifest['public_statements_and_Checks_unchanged'] = True
    manifest['offered_files'] = {name: {'bytes': len(data), 'sha256': sha(data)} for name, data in files.items()}
    manifest['control_sha256'] = sha(Path(__file__).read_bytes())
    NEW.mkdir()
    for name, data in files.items():
        (NEW / name).write_bytes(data)
    (NEW / 'manifest.json').write_bytes((json.dumps(manifest, indent=2) + '\n').encode('utf-8'))
    print(json.dumps({'source_sha256': sha(successor),
                      'checks_sha256': sha(files['ActualNumericRobustRealChecks.lean']),
                      'manifest_sha256': sha((NEW / 'manifest.json').read_bytes()),
                      'inverse_reconstruction_passed': True, 'compiler_invoked': False}, indent=2))

if __name__ == '__main__':
    main()
