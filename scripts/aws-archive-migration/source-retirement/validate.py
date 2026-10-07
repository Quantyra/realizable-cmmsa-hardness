"""Sequential synthetic suites; immutable nonsecret validation receipt."""
import json
import subprocess
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from safety import digest, immutable, iso
HERE = Path(__file__).resolve().parent

pins = {p.name: digest(p.read_bytes()) for p in HERE.iterdir() if p.suffix in ('.py', '.mjs')}
started = iso()
results = []
for name in ('test_safety.py', 'test_transport.py', 'test_production.py'):
    r = subprocess.run([sys.executable, '-B', str(HERE/name)], capture_output=True)
    output = r.stdout + r.stderr
    results.append({'suite': name, 'exit_code': r.returncode, 'output_sha256': digest(output),
                    'summary': output.decode('utf-8', errors='replace').splitlines()[-5:]})
    print(json.dumps(results[-1]), flush=True)
if pins != {p.name: digest(p.read_bytes()) for p in HERE.iterdir() if p.suffix in ('.py', '.mjs')}:
    raise RuntimeError('CodeChangedDuringValidation')
receipt = {'type': 'archive-retirement-synthetic-validation-v1', 'started_at': started,
           'completed_at': iso(), 'code_sha256': pins, 'results': results,
           'real_cloud_requests': 0, 'real_socket_requests': 0, 'real_mutations': 0,
           'payload_downloads': 0, 'source_eligibility': 'HOLD'}
immutable(HERE/'evidence/completion-test-results-final.json', receipt)
raise SystemExit(0 if all(r['exit_code'] == 0 for r in results) else 1)
