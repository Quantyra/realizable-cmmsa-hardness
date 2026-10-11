"""Bind proven duplicate-cache recovery to seven settled runs; no cloud action."""
import ast
import hashlib
import json
from pathlib import Path
from custody_checks import digest, verify_local_custody
from full111_builder02_controller import ROOT, VM_ID

HERE = Path(__file__).resolve().parent


def main():
    current = json.loads((ROOT / 'launch-once.json').read_bytes())
    current_check = Path(current['preflight'])
    current_receipt = json.loads((current_check / 'terminal-custody.json').read_bytes())
    with __import__('tarfile').open(current_receipt['custody']['repository_path']) as archive:
        terminal = archive.extractfile('dedicated-worker-terminal.json').read()
    terminal_pin = hashlib.sha256(terminal).hexdigest().upper()
    scopes = []
    for number in (111, 96, 97, 98, 99, 100, 101):
        resource = ROOT if number == 111 else next(ROOT.parent.glob('full' + str(number) + '-*'))
        marker = json.loads((resource / 'launch-once.json').read_bytes())
        check = Path(marker['preflight'])
        receipt = json.loads((check / 'terminal-custody.json').read_bytes())
        stop = json.loads((check / 'vm-termination.json').read_bytes())
        assert marker['run'] == receipt['run'] == stop['run']
        assert receipt['terminal']['native_terminal'] and stop['custody_verified_before_stop']
        assert stop['independent']['status'] == 'TERMINATED' and str(stop['independent']['id']) == VM_ID
        custody = receipt['custody']
        verify_local_custody(custody['short_path'], custody['repository_path'], custody['remote_sha256'], custody['bytes'])
        source = HERE / ('full109_trace_cache_large_native109_v1.py' if number == 111 else 'full109_trace_cache_small_native89_v1.py')
        raw = source.read_bytes()
        text = raw.decode('utf-8')
        changes = []

        def replace(old, new):
            nonlocal text
            assert text.count(old) == 1, (number, old, text.count(old))
            text = text.replace(old, new)
            changes.append(dict(old=old, new=new))

        old_run = 'cmmsa_a8_output_20261010T110328Z_0d5c26f4' if number == 111 else 'cmmsa_a8_output_20261008T094623Z_e93b94e1'
        old_manifest = '7212F8D1D98A899BA54DC3498D3E47CC3B68AAB432B3BA3B68ABA74117B8E6B4' if number == 111 else '81813B3B53BC6112914005E65C4F41CCB96B9D5C0FC45D23D9E3E66B2AE11348'
        old_archive = 'BD8EC70F9A138EBB5C3AC8E52B7732CF7CFE3D3E5C9B9F8CB3FB16FE37F21154' if number == 111 else '0ECFA6657CEB08927A2ED197363DD2539A3319AC8F3945C02BB077AC67424A64'
        old_control = 'full109-trace-cache-large-native109-v1' if number == 111 else 'full109-trace-cache-small-native89-v1'
        remote_name = 'full111-settled-cache-native' + str(number) + '-v2'
        replace(old_run, marker['run'])
        replace(old_manifest, digest(resource / 'capture-manifest.json'))
        replace(old_archive, custody['remote_sha256'])
        replace(old_control, remote_name)
        old_guard = "    if (HOME / 'full109-consumption-v3-launch-once.json').exists():\n        raise RuntimeError('Full109 " + ('consumption trace already launched' if number == 111 else 'trace already launched') + "')\n"
        new_guard = "    settled = HOME / '" + current['run'] + "_evidence/dedicated-worker-terminal.json'\n"
        new_guard += "    if digest(settled) != '" + terminal_pin + "':\n        raise RuntimeError('Original Full111 native terminal drift')\n"
        new_guard += "    if (HOME / 'full112-exact-real-complex-operators-repair2-resource02-launch-once.json').exists():\n        raise RuntimeError('Full111 compiler already launched')\n"
        replace(old_guard, new_guard)
        replace("('_worker.py', 'cloud_capture.py', 'full109_verify.py')",
                "('_worker.py', 'cloud_capture.py', 'full109_verify.py', 'full111_verify.py', 'full112_verify.py')")
        # Preserve a complete append-only per-file journal instead of repeatedly
        # rewriting the entire growing receipt after every identical-byte repoint.
        replace("        (CONTROL / 'partial-execution.json').write_text(json.dumps(receipt, indent=2) + '\\n')",
                "        with (CONTROL / 'execution-journal.jsonl').open('a', encoding='utf-8') as journal:\n            journal.write(json.dumps(row) + '\\n')")
        target = HERE / ('full111_settled_cache_native' + str(number) + '_v2.py')
        ast.parse(text, filename=target.name)
        rebuilt = raw.decode('utf-8')
        for change in changes:
            assert rebuilt.count(change['old']) == 1
            rebuilt = rebuilt.replace(change['old'], change['new'])
        assert rebuilt == text
        target.open('xb').write(text.encode('utf-8'))
        scopes.append(dict(number=number, resource=str(resource), run=marker['run'],
            manifest_sha256=digest(resource / 'capture-manifest.json'), archive_sha256=custody['remote_sha256'],
            source=source.name, source_sha256=digest(source), helper=target.name, helper_sha256=digest(target),
            remote_control='/home/dfredriksen_quantyra_org/' + remote_name,
            target_bytes=5 * 1024**3 if number == 111 else 896 * 1024**2, exact_replacements=changes))
    value = dict(schema='full111-settled-cache-recovery-controls-v2', scopes=scopes,
        current_native_run=current['run'], current_native_terminal_sha256=terminal_pin,
        parent_stop_sha256=digest(current_check / 'vm-termination.json'),
        source_project_objects_canonical_cache_and_archives_excluded=True,
        complete_append_only_per_file_journal_and_final_receipt=True,
        current_byte_identity_required_before_and_after_every_repoint=True,
        minimum_disk_GiB=40, minimum_local_MiB=1536, cloud_action_performed=False)
    (HERE / 'full111-settled-cache-recovery-derivation-v2.json').open('x', encoding='utf-8').write(json.dumps(value, indent=2)+'\n')
    print(json.dumps(dict(scopes=len(scopes), terminal_sha256=terminal_pin, cloud_action_performed=False)))


if __name__ == '__main__':
    main()
