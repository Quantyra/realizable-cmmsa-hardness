"""Refresh the existing dedicated idle activity while retained inspections run."""
from datetime import datetime, timezone
import json
from pathlib import Path
from custody_checks import digest
from full114_builder02_controller import ROOT, VM_ID
from full114_dedicated_openssh_v2 import Session
from run_full114_cache_recovery_v2 import RECOVERY


def main():
    assert not (ROOT / 'launch-once.json').exists()
    boot = json.loads((RECOVERY / 'boot-result.json').read_bytes())
    assert str(boot['after']['id']) == VM_ID and boot['after']['status'] == 'RUNNING'
    folder = RECOVERY / 'idle-refresh-controls' / datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    folder.mkdir(parents=True, exist_ok=False)
    (folder / Path(__file__).name).write_bytes(Path(__file__).read_bytes())
    with Session(folder / 'transport') as session:
        raw = session.ssh('set -e; date +%s | sudo tee /var/lib/quantyra-idle-shutdown/last-active; sudo systemctl start quantyra-idle-shutdown.timer; systemctl is-active quantyra-idle-shutdown.timer')
        assert raw.read_text().splitlines()[-1] == 'active'
        result = dict(state=session.state, boot_result_sha256=digest(RECOVERY / 'boot-result.json'),
            idle_timer_active=True, idle_activity_refreshed=True, power_operation=False,
            compiler_invoked=False, staged_inputs_modified=False, launch_clearance=False)
    (folder / 'idle-refreshed.json').open('x').write(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(receipt=str(folder / 'idle-refreshed.json'), refreshed=True)), flush=True)


if __name__ == '__main__':
    main()
