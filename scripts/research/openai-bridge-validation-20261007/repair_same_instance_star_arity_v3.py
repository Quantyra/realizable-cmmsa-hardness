"""Repair two stale internal arities, preserving the exact public statement."""
import hashlib
import json
from pathlib import Path
import tarfile
from lean_source_static_preflight_v2 import inspect_bytes
import prepare_complete_numeric_scope_v2 as scope

HERE = Path(__file__).resolve().parent


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    parent = HERE / 'numeric-same-instance-composition-capture-v2'
    index_raw = (parent / 'index.json').read_bytes()
    assert sha(index_raw) == '48672D236093387B5D9E8C8AFF076F490EB9783A740B63761E804323974CA46D'
    for row in json.loads(index_raw)['files']:
        data = (parent / row['copy']).read_bytes()
        assert len(data) == row['bytes'] and sha(data) == row['sha256']
    manifest = json.loads((parent / 'manifest.json').read_bytes())
    old = scope.parent()
    additions, _, _ = scope.additions()
    all_sources = old | additions
    for row in manifest['direct_project_dependencies']:
        data = all_sources[row['path']]
        assert len(data) == row['bytes'] and sha(data) == row['sha256']
    for folder, pin in manifest['numeric_capture_indices']:
        assert sha((HERE / folder / 'index.json').read_bytes()) == pin
    package = scope.PARENT / 'checks/20261011T065940457444Z/qualified-native/cmmsa_a8_output_20261011T070000Z_135b1f28/remote-evidence/package-sources.tar.gz'
    assert sha(package.read_bytes()) == manifest['package_sources_sha256']
    with tarfile.open(package, 'r:gz') as tar:
        for row in manifest['external_dependencies']:
            data = tar.extractfile(row['member']).read()
            assert len(data) == row['bytes'] and sha(data) == row['sha256']
    name = 'ExactNumericSameInstanceComposition.lean'
    source = (parent / name).read_bytes()
    before, after = b'c h s C T', b'c h m C T'
    assert source.count(before) == 2
    new = source.replace(before, after)
    assert new.replace(after, before) == source
    assert new[:new.index(b' := by\n  classical', new.index(b'theorem same_instance_real_inverse_agreement'))] == source[:source.index(b' := by\n  classical', source.index(b'theorem same_instance_real_inverse_agreement'))]
    checks_name = 'ExactNumericSameInstanceCompositionChecks.lean'
    files = {name: new, checks_name: (parent / checks_name).read_bytes()}
    map_name = 'ARGUMENT-AND-API-MAP.md'
    files[map_name] = (parent / map_name).read_bytes() + b'\n## V3 internal star-arity repair\n\nThe v2 public premise correctly used selected m stars, but both internal hscore annotations still used the append width s. V3 changes only those two internal applications from c/h/s to c/h/m. The public theorem, imports, Checks, scalar argument and dependency identities are unchanged. The v2 candidate and its inaccurate broad star-count flag remain preserved; neither version has passed Lean.\n'
    lexical = [inspect_bytes(data, file) for file, data in files.items() if file.endswith('.lean')]
    manifest['offer'] = 'numeric-same-instance-composition-offer-v3'
    manifest['parent_capture_index_sha256'] = sha(index_raw)
    manifest['repair'] = dict(before=before.decode(), after=after.decode(), occurrences=2,
        public_statement_unchanged=True, checks_unchanged=True, proof_bodies_otherwise_unchanged=True,
        prior_broad_star_count_flag_did_not_detect_these_internal_arity_errors=True)
    manifest['offered_files'] = {file: dict(bytes=len(data), sha256=sha(data)) for file, data in files.items()}
    manifest['lexical_preflight'] = lexical
    files['manifest.json'] = (json.dumps(manifest, indent=2) + '\n').encode()
    offer = HERE / 'numeric-same-instance-composition-offer-v3'
    offer.mkdir(exist_ok=False)
    for file, data in files.items():
        (offer / file).open('xb').write(data)
    capture = HERE / 'numeric-same-instance-composition-capture-v3'
    capture.mkdir(exist_ok=False)
    (capture / '.gitattributes').write_bytes(b'* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    rows = []
    for file, data in files.items():
        (capture / file).open('xb').write(data)
        assert (capture / file).read_bytes() == (offer / file).read_bytes() == data
        rows.append(dict(original=str(offer / file), copy=file, bytes=len(data), sha256=sha(data)))
    result = dict(files=rows, parent_capture_index_sha256=sha(index_raw),
        exact_repair=manifest['repair'], actual_dependencies_reverified=True,
        lexical_preflight=lexical, public_declarations=manifest['public_declarations'],
        root_read_actual_source_and_identified_stale_internal_arity=True,
        compiler_invoked=False, accepted=False, full_goal_complete=False,
        control_sha256=sha(Path(__file__).read_bytes()))
    data = (json.dumps(result, indent=2) + '\n').encode()
    (capture / 'index.json').open('xb').write(data)
    print(json.dumps(dict(folder=capture.name, source_sha256=sha(new), index_sha256=sha(data),
                         repaired_internal_occurrences=2, public_statement_unchanged=True)))


if __name__ == '__main__':
    main()
