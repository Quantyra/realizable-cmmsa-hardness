"""One exclusive top-level read-only CLI review; retain same handle to terminal."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from datetime import datetime, timezone

ROOT = Path('C:/Users/dfred/.quantyra/builder02/full90-material-resource02/consumption-v1/qualification/material-review-packets-v1')


def main():
    lens, number = sys.argv[1], int(sys.argv[2])
    manifest = json.loads((ROOT/'manifest.json').read_bytes())
    if lens not in manifest['required_lenses'] or not 1 <= number <= len(manifest['packets']):
        raise ValueError('Unknown review scope')
    row = manifest['packets'][number-1]
    packet = Path(row['path']).read_bytes()
    if hashlib.sha256(packet).hexdigest().upper() != row['sha256']:
        raise ValueError('Packet changed')
    folder = ROOT/f'{lens}-{number:02d}'
    if len(sys.argv) == 4:
        if (lens, number, sys.argv[3]) != ('complexity', 5, 'retry-02'):
            raise ValueError('Unknown exclusive retry')
        failed = json.loads((folder/'stdout.json').read_bytes())
        if int((folder/'native-exit.txt').read_text()) != 1 or failed.get('api_error_status') != 429:
            raise ValueError('Original quota failure not preserved')
        folder = ROOT/f'{lens}-{number:02d}-retry-02'
    folder.mkdir()
    prompt = f'You are the independent {lens} reviewer.\n'.encode() + packet
    (folder/'prompt.txt').write_bytes(prompt)
    command = ['C:/Users/dfred/.local/bin/claude.exe', '--print', '--model', 'claude-opus-5-5[1m]', '--output-format', 'json', '--tools', '', '--no-session-persistence']
    (folder/'command.json').write_text(json.dumps(command)+'\n')
    child = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, cwd=str(folder), creationflags=subprocess.CREATE_NO_WINDOW)
    (folder/'live.json').write_text(json.dumps({'pid': child.pid, 'utc': datetime.now(timezone.utc).isoformat(), 'lens': lens, 'packet': number})+'\n')
    first = True
    while True:
        try:
            out, err = child.communicate(input=prompt if first else None, timeout=30)
            break
        except subprocess.TimeoutExpired:
            first = False
            print('Same independent reviewer remains live', child.pid, lens, number, flush=True)
    (folder/'stdout.json').write_bytes(out); (folder/'stderr.txt').write_bytes(err)
    (folder/'native-exit.txt').write_text(str(child.returncode)+'\n')
    print(json.dumps({'native_exit': child.returncode, 'folder': str(folder), 'stdout_bytes': len(out), 'stderr_bytes': len(err)}), flush=True)
    sys.exit(child.returncode)


if __name__ == '__main__': main()
