"""Profile the exact frozen seven-target driver after native build success, on GCP."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

ROOT = Path('/home/dfredriksen_quantyra_org/upstream_adc7f124_original_v1')


def main():
    assert (ROOT/'original-selected-build-v2/native-exit.txt').read_text().strip() == '0'
    manifest = json.loads((ROOT/'selected-capture-manifest.json').read_bytes())
    driver = ROOT/'selected-upstream-axioms.lean'
    pin = manifest['files'][driver.name]
    assert len(driver.read_bytes()) == pin['bytes']
    assert hashlib.sha256(driver.read_bytes()).hexdigest().upper() == pin['sha256']
    destination = ROOT/'original-selected-profiles-v1'
    destination.mkdir()
    toolchain = ROOT/'lean-4.34.1-linux'
    command = [str(toolchain/'bin/lake'), '--no-cache', 'env', 'lean', str(driver)]
    env = dict(os.environ, PATH=str(toolchain/'bin')+':/usr/bin:/bin')
    (destination/'command.json').write_text(json.dumps(dict(argv=command,
        requested_profiles=manifest['requested_axiom_profiles'], driver_sha256=pin['sha256']))+'\n')
    with (destination/'stdout.txt').open('xb') as out, (destination/'stderr.txt').open('xb') as err:
        child = subprocess.Popen(command, cwd=ROOT/'lean', env=env, stdout=out, stderr=err)
        (destination/'live.json').write_text(json.dumps(dict(pid=child.pid, start=time.time()))+'\n')
        while child.poll() is None:
            print('Same original upstream profile remains live',child.pid,flush=True)
            time.sleep(30)
    (destination/'native-exit.txt').write_text(str(child.returncode)+'\n')
    print(json.dumps(dict(native_exit=child.returncode, accepted=False)),flush=True)


if __name__ == '__main__':
    main()
