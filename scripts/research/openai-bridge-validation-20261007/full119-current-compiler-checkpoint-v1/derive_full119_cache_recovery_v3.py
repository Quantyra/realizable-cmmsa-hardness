"""Bind reversible recovery to six disjoint settled dependency artifact scopes."""

import ast

import hashlib

import json

from pathlib import Path

import subprocess

import tarfile

from custody_checks import digest, verify_local_custody

from full118_builder02_controller import ROOT, VM_ID



HERE = Path(__file__).resolve().parent

REPO = HERE.parents[2]

PREFIX = HERE.relative_to(REPO).as_posix() + '/'





def main():

    marker = json.loads((ROOT / 'launch-once.json').read_bytes())

    check = Path(marker['preflight'])

    receipt = json.loads((check / 'terminal-custody.json').read_bytes())

    with tarfile.open(receipt['custody']['repository_path']) as archive:

        terminal = archive.extractfile('dedicated-worker-terminal.json').read()

    terminal_pin = hashlib.sha256(terminal).hexdigest().upper()

    source = HERE / 'full111_settled_cache_native111_v2.py'

    raw = source.read_bytes()

    assert raw == subprocess.check_output(['git', 'cat-file', 'blob', '9f8f04c8:' + PREFIX + source.name], cwd=REPO)

    future = ROOT.parent / 'full119-exact-real-complex-operators-repair9-resource02'

    observations=[future/'staging-controls/20261012T045817054295Z/inspection.json',future/'earlier-settled-capacity-inspection-v1/inspection.json',future/'earlier-settled-capacity-inspection-v2/inspection.json']
    assert all(p.is_file() for p in observations)
    capacity=observations[-1];other=observations[0]
    values=[json.loads(p.read_bytes()) for p in observations]
    assert all(v['read_only'] and not v['compiler_invoked'] for v in values)
    actual=dict(values[-1]);actual['scopes']=[row for value in values for row in value['scopes']]
    assert len(actual['scopes'])==len({r['number'] for r in actual['scopes']})
    older=actual
    assert actual['read_only'] and not actual['compiler_invoked']
    required=40*1024**3; margin=384*1024**2
    needed=max(0,required+margin-actual['disk_available_bytes'])
    selected=[];anticipated_rows=0
    for row in actual['scopes']:
        native=row['number']
        for kind in ('lean-large','generated','lean-small'):
            group=row['groups'].get(kind,{});available=group.get('allocated_bytes',0)
            if available<1024**2:continue
            selected.append((str(native)+'_'+kind.replace('-','_')+'_additive',native,kind,available));anticipated_rows+=group['files']
    gross=sum(r[3] for r in selected)
    assert gross>=int(1.2*1024**3) and gross-anticipated_rows*5120-16*1024**2>=needed,'Insufficient conservatively budgeted remaining recovery; preserve inspection and stop idle VM'
    actual_capacity=capacity

    scopes = []

    for number, native, kind, target_bytes in selected:

        resource, = [p for p in ROOT.parent.glob('full' + str(native) + '-*') if (p / 'launch-once.json').is_file()]

        current = json.loads((resource / 'launch-once.json').read_bytes()); old_check = Path(current['preflight'])

        old_receipt = json.loads((old_check / 'terminal-custody.json').read_bytes())

        stop = json.loads((old_check / 'vm-termination.json').read_bytes())

        assert current['run'] == old_receipt['run'] == stop['run']

        assert old_receipt['terminal']['native_terminal'] and stop['custody_verified_before_stop']

        assert stop['independent']['status'] == 'TERMINATED' and str(stop['independent']['id']) == VM_ID

        custody = old_receipt['custody']

        verify_local_custody(custody['short_path'], custody['repository_path'], custody['remote_sha256'], custody['bytes'])

        text = raw.decode('utf-8'); changes = []

        def replace(old, new, expected=1):

            nonlocal text

            assert text.count(old) == expected, (number, old, text.count(old))

            text = text.replace(old, new); changes.append(dict(old=old, new=new, occurrences=expected))

        replace("RUN = 'cmmsa_a8_output_20261011T035621Z_498f7ba6'", 'RUN = ' + repr(current['run']))

        replace('24251BCA8C0A9231CD98D0B966B322DAD9123526D1340398982A0D5A54116865', digest(resource / 'capture-manifest.json'))

        replace('29A942FBF1594E1C09EC34ECE58DB02F1742E8B9FDCDA0E88B3084E3F4B7F192', custody['remote_sha256'])

        remote_name = 'full119-settled-cache-native' + str(number) + '-v1'

        replace('full111-settled-cache-native111-v2', remote_name)

        replace("settled = HOME / 'cmmsa_a8_output_20261011T035621Z_498f7ba6_evidence/dedicated-worker-terminal.json'", "settled = HOME / '" + marker['run'] + "_evidence/dedicated-worker-terminal.json'")

        replace('F7B4332D6F0026583CC96F517F19BF6CF016A1F326D981F96233FEE29AE09277', terminal_pin)

        replace('Original Full111 native terminal drift', 'Original Full118 native terminal drift')

        replace('full112-exact-real-complex-operators-repair2-resource02-launch-once.json', 'full119-exact-real-complex-operators-repair9-resource02-launch-once.json')

        replace('Full111 compiler already launched', 'Full119 compiler already launched')

        replace("'full111_verify.py', 'full112_verify.py'", "'full111_verify.py', 'full112_verify.py', 'full113_verify.py', 'full114_verify.py', 'full115_verify.py', 'full116_verify.py', 'full117_verify.py', 'full118_verify.py', 'full119_verify.py'")

        if target_bytes != 5 * 1024**3:

            replace('TARGET = 5 * 1024**3', 'TARGET = ' + str(target_bytes))

        if kind == 'lean-small':

            replace('info.st_size >= 65536', '1 <= info.st_size < 65536')

        if kind == 'generated':

            old = "        if not any(path.name.endswith(suffix) for suffix in ('.olean', '.olean.private', '.olean.server', '.ilean')):\n            continue\n        if not {'.lake', 'build', 'lib', 'lean'} <= set(rel.parts):\n            continue"

            new = "        parts = rel.parts\n        generated_ir = {'.lake', 'build', 'ir'} <= set(parts) and path.name.endswith(('.c', '.c.o.export', '.setup.json'))\n        generated_lean_ir = {'.lake', 'build', 'lib', 'lean'} <= set(parts) and path.name.endswith('.ir')\n        generated_bin = rel.as_posix() in ('batteries/.lake/build/bin/runLinter', 'mathlib/.lake/build/bin/cache')\n        if not (generated_ir or generated_lean_ir or generated_bin):\n            continue"

            replace(old, new)

            replace('GCP-only reversible deduplication of settled native109 dependency object copies.', 'GCP-only reversible sharing of exact settled generated dependency artifacts; no Lean source or project artifacts.')

        if kind == 'generated':
            replace('info.st_size >= 65536', 'info.st_size > 0')
        target = HERE / ('full119_settled_cache_native' + str(number) + '_v1.py')

        ast.parse(text); target.open('xb').write(text.encode('utf-8'))

        scopes.append(dict(number=number, native_number=native, kind=kind, resource=str(resource), run=current['run'],

            manifest_sha256=digest(resource / 'capture-manifest.json'), archive_sha256=custody['remote_sha256'],

            source=source.name, source_commit='9f8f04c8', source_sha256=digest(source), helper=target.name,

            helper_sha256=digest(target), remote_control='/home/dfredriksen_quantyra_org/' + remote_name,

            target_bytes=target_bytes, exact_replacements=changes))

    value = dict(schema='full119-adaptive-disjoint-settled-dependency-recovery-scopes-v1', scopes=scopes,

        current_native_run=marker['run'], current_native_terminal_sha256=terminal_pin,

        parent_stop_sha256=digest(check / 'vm-termination.json'), capacity_observation=str(capacity),

        capacity_observation_sha256=digest(capacity),

        all_generated_scopes_have_actual_read_only_capacity_observation=True,

        all_scope_capacity_observation=str(actual_capacity), all_scope_capacity_sha256=digest(actual_capacity), second_capacity_observation=str(other), second_capacity_sha256=digest(other),

        capacity_observations=[dict(path=str(p),sha256=digest(p)) for p in observations],
        actual_plan_content_hashes_still_required=True,

        lean_sources_project_artifacts_canonical_cache_and_archives_excluded=True,

        complete_append_only_per_file_journal_and_final_receipt=True,

        current_byte_identity_required_before_and_after_every_repoint=True,

        minimum_disk_GiB=40, minimum_local_bytes=1803550720, target_post_recovery_margin_bytes=margin, anticipated_rows=anticipated_rows, conservative_persistent_overhead_per_row_bytes=5120, failed_prior_capacity_audit_preserved=True, cloud_action_performed=False)

    (HERE / 'full119-cache-recovery-derivation-v1.json').open('x').write(json.dumps(value, indent=2) + '\n')

    print(json.dumps(dict(scopes=len(scopes), target_allocated_bytes=sum(s['target_bytes'] for s in scopes), compiler_invoked=False)), flush=True)





if __name__ == '__main__':

    main()

