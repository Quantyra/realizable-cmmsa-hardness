"""Lease-aware replacement for the existing 45-minute GCP idle check.

Undeployed. Missing controller enrollment blocks shutdown. The original VM
startup script and base unit are preserved; use a persistent systemd drop-in.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import time
from lifecycle_manager import drain_and_act
from thread_leases import Busy

REGISTRY = Path('/var/lib/quantyra-thread-leases')
STATE = Path('/var/lib/quantyra-idle-shutdown')
ACTIVITY_NAMES = {'lean', 'lake', 'git', 'apt', 'apt-get', 'dpkg', 'curl', 'tar', 'zstd'}


def observe(registry=REGISTRY, state=STATE, *, now=None, proc_root=Path('/proc'), sessions=None):
    now = int(time.time()) if now is None else now
    state.mkdir(parents=True, exist_ok=True)
    process_complete = True
    workloads = []
    for path in proc_root.iterdir():
        if not path.name.isdigit() or int(path.name) == os.getpid():
            continue
        try:
            name = (path / 'comm').read_text().strip()
            command = (path / 'cmdline').read_bytes().replace(b'\0', b' ').decode(errors='replace')
        except FileNotFoundError:
            continue  # Process disappeared; a registered run still holds its lease.
        except (OSError, UnicodeError):
            process_complete = False
            continue
        if name in ACTIVITY_NAMES or any(token in command for token in
                ('cloud_capture.py', 'cmmsa_a8_output_', 'launch-resume', 'controller.py')):
            workloads.append({'pid': int(path.name), 'name': name})
    if sessions is None:
        result = subprocess.run(['who'], capture_output=True, text=True)
        session_complete = result.returncode == 0
        sessions = result.stdout.splitlines()
    else:
        session_complete = True
    stamp = state / 'last-active'
    active = workloads or sessions or not process_complete or not session_complete
    if active or not stamp.exists():
        stamp.write_text(str(now) + '\n')
    try:
        idle = not active and now - int(stamp.read_text()) >= 2700
    except (OSError, ValueError):
        idle = False
    try:
        inventory = json.loads((registry / 'controller-inventory.json').read_bytes())
    except (OSError, ValueError):
        inventory = {}
    # Inventory is an explicit enrollment receipt, not inferred from an empty ps.
    return {'process_scan_complete': process_complete,
            'session_scan_complete': session_complete,
            'controller_inventory_complete': inventory.get('complete') is True,
            'all_controllers_lease_aware': inventory.get('all_controllers_lease_aware') is True,
            'idle_threshold_met': idle, 'unregistered_workloads': workloads,
            'interactive_sessions': sessions}


def main():
    if sys.platform != 'linux': raise RuntimeError('Shared idle service requires Linux')
    try:
        def shutdown(observation):
            result = subprocess.run(['/sbin/shutdown', '-h', 'now'], capture_output=True)
            if result.returncode: raise RuntimeError('Shutdown outcome uncertain; keep DRAINING')
            return 0
        return drain_and_act(REGISTRY, observe=observe, action=shutdown)
    except Busy as error:
        print('Shutdown refused:', error)
        # Active leases are activity through compilation and custody, including
        # gaps between child processes. Reset the original idle clock.
        active = REGISTRY / 'active'
        if active.exists() and any(active.iterdir()):
            STATE.mkdir(parents=True, exist_ok=True)
            (STATE / 'last-active').write_text(str(int(time.time())) + '\n')
        return 0


if __name__ == '__main__': raise SystemExit(main())
