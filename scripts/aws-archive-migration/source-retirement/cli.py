"""Default offline check; explicit observe is read-only. Execute always refused."""
import argparse
import json
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from safety import Stop, digest, immutable, execution_lock, validate_allowlist

HERE = Path(__file__).resolve().parent


def code_pins():
    return {name: digest((HERE/name).read_bytes()) for name in
            ('cli.py', 'inventory.py', 'aws.py', 'safety.py')}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('mode', nargs='?', choices=['check', 'observe', 'execute'], default='check')
    p.add_argument('--output', type=Path)
    a = p.parse_args()
    # Deliberate preparation-only interlock BEFORE credential/session construction.
    if a.mode == 'execute':
        raise Stop('EXECUTION_DISABLED_PENDING_INDEPENDENT_REVIEW_AND_ROOT_INTEGRATION')
    allowlist_bytes = (HERE / 'evidence/bound-allowlist.json').read_bytes()
    allowlist = validate_allowlist(json.loads(allowlist_bytes))
    if a.mode == 'check':
        print(json.dumps({'mode': 'check-only-offline', 'versions': 205, 'bytes': 18579936167,
                          'allowlist_stored_sha256': digest(allowlist_bytes),
                          'current_cloud_state': 'NOT_OBSERVED', 'permission_simulation': 'NOT_RUN',
                          'root_gate': 'DISABLED', 'source_eligibility': 'HOLD', 'cloud_requests': 0,
                          'cloud_mutations': 0, 'payload_downloads': 0}))
        return
    if a.output is None or not a.output.parent.is_dir():
        raise Stop('EXISTING_OWNED_OUTPUT_DIRECTORY_REQUIRED')
    from aws import AWS
    from inventory import observe
    with execution_lock(a.output.parent):
        pins = code_pins()
        observation = observe(AWS(), allowlist)
        if code_pins() != pins:
            raise Stop('OBSERVATION_CODE_CHANGED')
        observation['code_sha256'] = pins
        observation['allowlist_stored_sha256'] = digest(allowlist_bytes)
        immutable(a.output, observation)
        print(json.dumps({'mode': 'observe', 'file': str(a.output),
                          'sha256': digest(a.output.read_bytes()), 'source_eligibility': 'HOLD',
                          'cloud_mutations': 0, 'payload_downloads': 0}))


if __name__ == '__main__':
    try:
        main()
    except Exception as e:
        # Never expose AWS response bodies, credentials, raw exceptions or headers.
        code = str(e) if isinstance(e, Stop) else type(e).__name__
        print(json.dumps({'status': 'refused-or-unproven', 'safe_reason': code,
                          'source_eligibility': 'HOLD'}))
        raise SystemExit(1)
