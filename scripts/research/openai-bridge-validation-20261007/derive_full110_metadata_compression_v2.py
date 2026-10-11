"""Extend lossless compression to five additional settled native text inventories."""
import ast
import json
from pathlib import Path
from custody_checks import digest

HERE = Path(__file__).resolve().parent
source = HERE / 'compress_full110_settled_native_metadata_v1.py'
text = source.read_text(encoding='utf-8')
old = """        path = check / 'qualified-native' / marker['run'] / 'remote-evidence/package-object-before.json'
        assert path.resolve(strict=True).is_relative_to(BASE.resolve())
        with tarfile.open(receipt['custody']['repository_path'], 'r:gz') as archive:
            assert archive.extractfile('package-object-before.json').read() == path.read_bytes()
        paths.append(path)
"""
new = """        with tarfile.open(receipt['custody']['repository_path'], 'r:gz') as archive:
            for name in ('cslib-tracked-diff.patch', 'capture-manifest.json', 'verified-cache-provenance.json',
                         'package-source-hashes.json', 'core-object-before.json'):
                path = check / 'qualified-native' / marker['run'] / 'remote-evidence' / name
                assert path.resolve(strict=True).is_relative_to(BASE.resolve())
                assert archive.extractfile(name).read() == path.read_bytes()
                paths.append(path)
"""
changes = [(old, new), ('full110-settled-native-metadata-lossless-v1', 'full110-settled-native-metadata-lossless-v2')]
for old, new in changes:
    assert text.count(old) == 1
    text = text.replace(old, new)
ast.parse(text)
target = HERE / 'compress_full110_settled_native_metadata_v2.py'
target.open('xb').write(text.encode('utf-8'))
(HERE / 'full110-metadata-compression-derivation-v2.json').open('x', encoding='utf-8').write(json.dumps(dict(
    source=source.name, source_sha256=digest(source), target=target.name, target_sha256=digest(target),
    exact_replacements=changes, logical_bytes_preserved=True, delete_operation=False), indent=2)+'\n')
print(json.dumps(dict(derived=target.name, compression_executed=False)))
