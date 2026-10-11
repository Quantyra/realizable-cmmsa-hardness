"""Close only the identified receipt-download proxy after complete byte custody."""
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import sys
import time
from audit_full109_trace_cache_small_v1 import main as audit
from custody_checks import digest
from full109_builder02_controller import ROOT

HERE = Path(__file__).resolve().parent
SOURCE = ROOT/'consumption-v3/cache-repoint-controls/20261011T001721041630Z'
WRAPPER = ROOT/'research-resume-20261010/20261011T001649934562Z'
PIN = 'CA71F3017FFB28AD14A84DDE93230D576A70E27B3E3BD4EDEE545E38CAE84F47'


def read(path):
    return json.loads(Path(path).read_bytes())


def main():
    assert sys.argv[1:] in ([], ['--cancel-owned-proxy'])
    audit('plan', 84)
    commands = read(SOURCE/'commands.json')
    assert [r['native_exit'] for r in commands] == [0,0,0,0]
    assert '--command=python3 -B /home/dfredriksen_quantyra_org/full109-trace-cache-small-native84-v1/full109_trace_cache_small_native84_v1.py --execute' in commands[2]['argv']
    assert (SOURCE/'control/003.stdout').read_text().split()[0].upper() == PIN
    assert digest(SOURCE/'receipt.json') == PIN
    receipt = read(SOURCE/'receipt.json')
    operations = [read(p) for p in (ROOT/'consumption-v3/cache-repoint-controls').glob('*/operation.json')]
    plan_op = next(p for p in operations if p['action'] == 'plan' and p['remote_control'].endswith('native84-v1'))
    plan = read(plan_op['local_result'])
    assert receipt['applied'] == plan['rows'] and len(receipt['applied']) == 19233
    assert receipt['content_identity_verified_after_repoint'] and receipt['reversible_by_copying_identical_canonical_bytes']
    for key in ('warm_files_written','source_or_project_object_files_changed','failed_evidence_archive_changed','compiler_invoked'):
        assert receipt[key] is False
    target = ROOT/'scope84-completed-download-settlement-v1'
    target.mkdir(exist_ok=False)
    (target/'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
    (target/'received-receipt.json').open('xb').write((SOURCE/'receipt.json').read_bytes())
    assert digest(target/'received-receipt.json') == PIN
    observation = '''$rows = Get-CimInstance Win32_Process
$ids = @(15972,16992,4836,15808)
$descendants = @($rows | Where-Object { $_.ParentProcessId -eq 15808 })
$processes = @($rows | Where-Object { $_.ProcessId -in $ids } | Select-Object ProcessId,ParentProcessId,Name,CommandLine,CreationDate)
$tcp = @(Get-NetTCPConnection -ErrorAction SilentlyContinue | Where-Object { $_.OwningProcess -eq 15808 } | Select-Object OwningProcess,State,LocalPort,RemoteAddress,RemotePort)
[PSCustomObject]@{processes=$processes;proxy_children=@($descendants | Select-Object ProcessId,ParentProcessId,Name,CommandLine);tcp=$tcp} | ConvertTo-Json -Depth 4
'''
    for number in range(2):
        assert 'native_exit' not in read(WRAPPER/'command.json')
        active = read(SOURCE/'active-handle.json')
        assert active['command_index'] == 4 and active['control_pid'] == 15972 and active['elapsed_seconds'] >= 300
        assert digest(SOURCE/'receipt.json') == PIN
        result = subprocess.run(['powershell.exe','-NoProfile','-NonInteractive','-Command',observation], capture_output=True,
                                creationflags=subprocess.CREATE_NO_WINDOW)
        (target/f'{number}.stdout').write_bytes(result.stdout)
        (target/f'{number}.stderr').write_bytes(result.stderr)
        assert result.returncode == 0
        value = json.loads(result.stdout)
        rows = {p['ProcessId']:p for p in value['processes']}
        assert set(rows) == {15972,16992,4836,15808}
        assert rows[15972]['ParentProcessId'] == 13548 and rows[15972]['Name'] == 'cmd.exe'
        assert rows[16992]['ParentProcessId'] == 15972 and rows[16992]['Name'] == 'python.exe'
        assert rows[4836]['ParentProcessId'] == 16992 and rows[4836]['Name'] == 'pscp.exe'
        assert rows[15808]['ParentProcessId'] == 4836 and rows[15808]['Name'] == 'python.exe'
        for pid in (15972,16992,4836):
            assert 'full109-trace-cache-small-native84-v1/receipt.json' in rows[pid]['CommandLine']
        assert 'compute start-iap-tunnel "quantyra-lean-builder-02" 22 --listen-on-stdin' in rows[15808]['CommandLine']
        assert all(p['ParentProcessId'] == 15808 and p['Name'] == 'conhost.exe' for p in value['proxy_children'])
        (target/f'{number}.active-handle.json').write_text(json.dumps(active,indent=2)+'\n')
        if number == 0:
            time.sleep(5)
    intent = dict(utc=datetime.now(timezone.utc).isoformat(), pid=15808, parent_pscp_pid=4836,
                  downloaded_receipt_sha256=PIN, complete_applied_rows_verified=19233,
                  original_remote_execution_native_exit=0, authenticated_remote_hash_command_native_exit=0,
                  rationale='Complete received bytes match the pre-disconnection remote hash; only the read-only download proxy is closed after five minutes without original terminal.',
                  active_TCP_connections_not_reclassified_as_absent=True,
                  vm_power_operation=False, remote_recovery_replayed=False,
                  authentication_guard_not_bypassed=True, original_transport_result_must_be_preserved=True,
                  cancellation_requested=bool(sys.argv[1:]))
    (target/'intent.json').open('x',encoding='utf-8').write(json.dumps(intent,indent=2)+'\n')
    if sys.argv[1:]:
        result = subprocess.run(['taskkill.exe','/PID','15808','/T','/F'],capture_output=True,creationflags=subprocess.CREATE_NO_WINDOW)
        (target/'taskkill.stdout').write_bytes(result.stdout)
        (target/'taskkill.stderr').write_bytes(result.stderr)
        (target/'taskkill.native-exit.json').write_text(json.dumps(dict(native_exit=result.returncode))+'\n')
        assert result.returncode == 0
    print(json.dumps(intent))


if __name__ == '__main__':
    main()
