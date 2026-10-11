"""Check the unexecuted package transformation in memory, with negative mutations."""
import ast
import copy
import json
from pathlib import Path
from custody_checks import digest
from prepare_builder02_full90 import capsule
import prepare_builder02_full115 as prepare
from full115_gl_repair_structure_v1 import validate as structure

HERE = Path(__file__).resolve().parent


def main():
    assert not prepare.OUTPUT.exists(), 'This control validates only unexecuted preparation'
    derivation = HERE / 'full115-control-derivation-v1.json'
    value = json.loads(derivation.read_bytes())
    for row in value['records']:
        assert digest(HERE / row['target']) == row['target_sha256']
        ast.parse((HERE / row['target']).read_text(encoding='utf-8'))
    for scope, records in [('package', value['records'][:2]), ('execution', value['records'][2:])]:
        metadata = dict(value, records=records, source_combined_derivation_sha256=digest(derivation),
                        purpose='Provide the separate snapshot names required by the unchanged validation collector')
        (HERE / f'full115-{scope}-control-derivation-v1.json').open('x').write(json.dumps(metadata, indent=2) + '\n')
    old = capsule(prepare.PARENT / 'input-archive.tar.gz')
    new = dict(old)
    manifest = json.loads(old['capture-manifest.json'])
    name, data, index, pin = prepare.repairs()[0]
    new[name] = data
    manifest['project_sources'][name] = dict(sha256=index['new_sha256'], bytes=len(data))
    new['capture-manifest.json'] = (json.dumps(manifest, indent=2) + '\n').encode()
    assert prepare.validate_expansion(old, new)
    structure_result = structure(old[name], data)
    mutations = []

    def reject(label, action):
        try:
            action()
        except (AssertionError, RuntimeError):
            mutations.append(dict(mutation=label, rejected=True))
        else:
            raise AssertionError('Mutation was accepted: ' + label)

    reject('heartbeat increase', lambda: structure(old[name], data.replace(b'maxHeartbeats 400000', b'maxHeartbeats 800000')))
    reject('declaration rename', lambda: structure(old[name], data.replace(b'theorem row_prefix_uniform_mean', b'theorem changed_row_prefix_uniform_mean')))
    checks = name.replace('.lean', 'Checks.lean')
    changed = dict(new); changed[checks] += b'\n'
    reject('unchanged Checks mutation', lambda: prepare.validate_expansion(old, changed))
    changed = dict(new); changed.pop(checks)
    reject('missing Checks member', lambda: prepare.validate_expansion(old, changed))
    for label, change in [
        ('missing axiom request', lambda m: m['requested_axioms'].pop()),
        ('extra axiom request', lambda m: m['requested_axioms'].append('Unapproved.extra')),
        ('missing stage', lambda m: m['stages'].pop()),
        ('different stage command', lambda m: m['stages'][4].update(argv=['lake', 'build', 'Unapproved']))]:
        changed = dict(new); altered = copy.deepcopy(manifest); change(altered)
        changed['capture-manifest.json'] = (json.dumps(altered, indent=2) + '\n').encode()
        reject(label, lambda: prepare.validate_expansion(old, changed))
    out = HERE / 'full115-preparation-scope-validation-v1'
    out.mkdir(exist_ok=False)
    (out / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    (out / 'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
    result = dict(source_count=369, requested_axioms=347, stages=7, members=376,
                  changed_sources=[name], structure=structure_result, negative_mutations=mutations,
                  all_other_368_source_bytes_and_all_checks_preserved=True,
                  parent_archive_sha256=digest(prepare.PARENT / 'input-archive.tar.gz'),
                  repair_capture_sha256=pin, exact_manifest_snapshot_name_binding_reconciled=True,
                  package_written=False, full_execution_tests_run=False, compiler_invoked=False,
                  cloud_action=False, launch_clearance=False, accepted=False)
    (out / 'result.json').open('x').write(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(folder=out.name, rejected_mutations=len(mutations), package_written=False, compiler_invoked=False)))


if __name__ == '__main__':
    main()
