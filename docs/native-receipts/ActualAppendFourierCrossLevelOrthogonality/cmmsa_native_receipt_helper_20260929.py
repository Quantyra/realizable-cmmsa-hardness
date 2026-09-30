"""Bounded native Lean receipt runner. No automatic retries; no unrelated kills."""
import argparse
import csv
import ctypes
import hashlib
import io
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import uuid
from datetime import datetime, timezone

ROOT = Path(r"C:\Users\Dan\Desktop\Projects\realizable-cmmsa-hardness").resolve()
LEAN = Path(r"C:\Users\Dan\.elan\toolchains\leanprover--lean4---v4.34.0-rc2\bin\lean.exe")
PACKAGES = ('aesop', 'batteries', 'complexitylib', 'importGraph', 'LeanSearchClient',
            'mathlib', 'plausible', 'proofwidgets', 'Qq')
PREFLIGHT_KIB = 3515864
GUARD_KIB = 1572864
SAMPLE_SECONDS = 1.0


def sha(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest().upper()


def utc():
    return datetime.now(timezone.utc).isoformat()


class MemoryStatus(ctypes.Structure):
    _fields_ = [('dwLength', ctypes.c_ulong), ('dwMemoryLoad', ctypes.c_ulong),
                ('ullTotalPhys', ctypes.c_ulonglong), ('ullAvailPhys', ctypes.c_ulonglong),
                ('ullTotalPageFile', ctypes.c_ulonglong), ('ullAvailPageFile', ctypes.c_ulonglong),
                ('ullTotalVirtual', ctypes.c_ulonglong), ('ullAvailVirtual', ctypes.c_ulonglong),
                ('ullAvailExtendedVirtual', ctypes.c_ulonglong)]


def available_kib():
    status = MemoryStatus()
    status.dwLength = ctypes.sizeof(status)
    if not ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(status)):
        raise ctypes.WinError()
    return int(status.ullAvailPhys // 1024)


def lean_pids():
    result = subprocess.run(['tasklist.exe', '/FI', 'IMAGENAME eq lean.exe', '/FO', 'CSV', '/NH'],
                            capture_output=True, check=True, text=True)
    return [int(row[1]) for row in csv.reader(io.StringIO(result.stdout))
            if len(row) >= 2 and row[0].lower() == 'lean.exe']


def capture(argv, cwd, env, stdout, stderr, receipt, guard=False):
    """Capture native returncode as an integer; terminate only this owned Popen."""
    started = time.monotonic()
    receipt.update(started_utc=utc(), argv=argv, cwd=str(cwd),
                   env_LEAN_PATH=env.get('LEAN_PATH'), pid=None, native_exit_code=None,
                   launched=False, guard_terminated=False, samples=[])
    proc = None
    try:
        with open(stdout, 'wb') as out, open(stderr, 'wb') as err:
            proc = subprocess.Popen(argv, cwd=str(cwd), env=env, stdout=out, stderr=err,
                                    shell=False, creationflags=subprocess.CREATE_NO_WINDOW)
            receipt.update(pid=proc.pid, launched=True)
            while proc.poll() is None:
                if guard:
                    free = available_kib()
                    receipt['samples'].append({'elapsed_seconds': time.monotonic() - started,
                                               'available_physical_kib': free})
                    if free < GUARD_KIB:
                        receipt['guard_terminated'] = True
                        proc.terminate()
                        break
                time.sleep(SAMPLE_SECONDS)
            code = proc.wait()
            assert code is not None and isinstance(code, int), 'Missing native integer exit code'
            receipt['native_exit_code'] = code
    except BaseException:
        if proc is not None:
            if proc.poll() is None:
                proc.terminate()
            code = proc.wait()
            assert code is not None and isinstance(code, int)
            receipt['native_exit_code'] = code
        raise
    finally:
        receipt.update(finished_utc=utc(), elapsed_seconds=time.monotonic() - started)


def write_receipt(path, receipt, stdout, stderr):
    receipt.update(stdout_path=str(stdout), stderr_path=str(stderr),
                   stdout_sha256=sha(stdout), stderr_sha256=sha(stderr),
                   stdout_bytes=stdout.stat().st_size, stderr_bytes=stderr.stat().st_size)
    with open(path, 'x', encoding='utf-8') as f:
        json.dump(receipt, f, indent=2)
        f.write('\n')
    print(str(path), flush=True)


def paths(mode):
    token = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ') + '_' + uuid.uuid4().hex
    stem = Path(__file__).parent / ('cmmsa_native_' + mode + '_' + token)
    out, err, receipt = (Path(str(stem) + suffix) for suffix in ('.stdout', '.stderr', '.json'))
    out.touch(exist_ok=False)
    err.touch(exist_ok=False)
    return out, err, receipt


def self_test():
    passed = True
    for expected in (0, 7):
        out, err, path = paths('selftest')
        receipt = {'mode': 'selftest', 'expected_native_exit_code': expected, 'success': False}
        env = os.environ.copy()
        argv = [sys.executable, '-c',
                "import sys; print('native capture test'); print('stderr capture test', file=sys.stderr); sys.exit(" + str(expected) + ')']
        try:
            capture(argv, Path(__file__).parent, env, out, err, receipt)
            receipt['success'] = (receipt['native_exit_code'] == expected
                                  and out.read_bytes().strip() == b'native capture test'
                                  and err.read_bytes().strip() == b'stderr capture test')
        except Exception as exc:
            receipt['exception'] = repr(exc)
        write_receipt(path, receipt, out, err)
        passed = passed and receipt['success']
    return 0 if passed else 1


def run(args):
    out, err, path = paths('lean')
    receipt = {'mode': 'lean', 'success': False, 'launched': False, 'native_exit_code': None,
               'created_utc': utc(), 'expected_source_sha256': args.expected_sha.upper(),
               'preflight_minimum_kib': PREFLIGHT_KIB, 'guard_minimum_kib': GUARD_KIB,
               'sample_interval_seconds': SAMPLE_SECONDS, 'normal_object_sha256': None}
    source = output = backup = None
    before = None
    try:
        source = Path(args.source)
        output = Path(args.output)
        if not source.is_absolute() or not output.is_absolute():
            raise ValueError('Source and normal output paths must be absolute')
        source, output = source.resolve(), output.resolve()
        relative = source.relative_to(ROOT / 'lean')
        if source.suffix != '.lean':
            raise ValueError('Source must be a .lean file within the satellite lean directory')
        required_output = (ROOT / '.lake/build/lib/lean' / relative).with_suffix('.olean').resolve()
        if output != required_output:
            raise ValueError('Output must be the matching normal .lake/build/lib/lean module object')
        if re.fullmatch(r'[0-9A-Fa-f]{64}', args.expected_sha) is None:
            raise ValueError('Expected SHA must have 64 hexadecimal digits')
        libs = [ROOT / '.lake/build/lib/lean'] + [ROOT / '.lake/packages' / p / '.lake/build/lib/lean' for p in PACKAGES]
        env = os.environ.copy()
        env['LEAN_PATH'] = os.pathsep.join(str(p) for p in libs)
        argv = [str(LEAN), '-j', '1', '-o', str(output), str(source)]
        receipt.update(source_path=str(source), normal_object_path=str(output),
                       argv=argv, cwd=str(ROOT), env_LEAN_PATH=env['LEAN_PATH'],
                       lean_exe_sha256=sha(LEAN))
        before = sha(source)
        receipt['source_before_sha256'] = before
        if before != args.expected_sha.upper():
            raise ValueError('Source hash does not match expected SHA; no launch')
        missing = [str(p) for p in libs if not p.is_dir()]
        if missing:
            raise ValueError('Missing LEAN_PATH directories: ' + repr(missing))
        pids = lean_pids()
        free = available_kib()
        receipt.update(preflight_lean_pids=pids, preflight_available_physical_kib=free)
        if pids:
            raise RuntimeError('Other lean.exe process exists; no launch')
        if free < PREFLIGHT_KIB:
            raise RuntimeError('Insufficient preflight memory; no launch')
        output.parent.mkdir(parents=True, exist_ok=True)
        if output.exists():
            backup = output.with_name(output.name + '.previous_' + uuid.uuid4().hex)
            receipt.update(previous_object_sha256=sha(output), previous_object_backup=str(backup))
            output.rename(backup)
        receipt['normal_object_absent_before_launch'] = not output.exists()
        assert receipt['normal_object_absent_before_launch']
        # Repeat volatile checks immediately before Popen, after preparing artifact isolation.
        if sha(source) != before or lean_pids() or available_kib() < PREFLIGHT_KIB:
            raise RuntimeError('Final preflight changed; no launch')
        capture(argv, ROOT, env, out, err, receipt, guard=True)
        after = sha(source)
        receipt['source_after_sha256'] = after
        error_text = bool(re.search(rb'\berror\s*:|\berror\[|\berror\(lean\.', out.read_bytes() + b'\n' + err.read_bytes(), re.I))
        receipt['lean_error_text_detected'] = error_text
        fresh = receipt['launched'] and output.is_file() and output.stat().st_size > 0
        receipt['fresh_normal_object_created'] = fresh
        receipt['success'] = (receipt['native_exit_code'] == 0 and not error_text
                              and not receipt['guard_terminated'] and before == after and fresh)
        if receipt['success']:
            receipt['normal_object_sha256'] = sha(output)
    except BaseException as exc:
        receipt['exception'] = repr(exc)
    finally:
        try:
            if source is not None and source.is_file():
                receipt['source_after_sha256'] = sha(source)
                if before is not None and receipt['source_after_sha256'] != before:
                    receipt['success'] = False
                    receipt['normal_object_sha256'] = None
            if not receipt['success'] and output is not None:
                if receipt.get('launched') and output.exists():
                    rejected = output.with_name(output.name + '.rejected_' + uuid.uuid4().hex)
                    output.rename(rejected)
                    receipt['rejected_object_path'] = str(rejected)
                if backup is not None and backup.exists():
                    backup.rename(output)
                    receipt['previous_object_restored'] = True
        except BaseException as exc:
            receipt['success'] = False
            receipt['normal_object_sha256'] = None
            receipt['finalization_exception'] = repr(exc)
        write_receipt(path, receipt, out, err)
    return 0 if receipt['success'] else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--self-test', action='store_true')
    parser.add_argument('--source')
    parser.add_argument('--expected-sha')
    parser.add_argument('--output')
    args = parser.parse_args()
    if args.self_test:
        if any((args.source, args.expected_sha, args.output)):
            parser.error('Self-test does not accept Lean arguments')
        return self_test()
    if not all((args.source, args.expected_sha, args.output)):
        parser.error('--source, --expected-sha, and --output are required')
    return run(args)


if __name__ == '__main__':
    sys.exit(main())
