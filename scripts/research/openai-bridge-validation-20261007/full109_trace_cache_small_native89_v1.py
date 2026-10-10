"""GCP-only reversible deduplication of settled full89 dependency object copies."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import sys
import urllib.request

HOME = Path('/home/dfredriksen_quantyra_org')
RUN = 'cmmsa_a8_output_20261008T094623Z_e93b94e1'
WARM = 'cmmsa_a8_output_20261007T230522Z_6af6dc24'
CONTROL = HOME / 'full109-trace-cache-small-native89-v1'
MANIFEST_SHA = '81813B3B53BC6112914005E65C4F41CCB96B9D5C0FC45D23D9E3E66B2AE11348'
ARCHIVE_SHA = '0ECFA6657CEB08927A2ED197363DD2539A3319AC8F3945C02BB077AC67424A64'
TARGET = 896 * 1024**2


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest().upper()


def write_new(path, value):
    with path.open('x', encoding='utf-8') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')


def guards():
    if sys.platform != 'linux' or Path.home().resolve() != HOME:
        raise RuntimeError('Exact GCP Linux home required')
    opener = urllib.request.build_opener(urllib.request.ProxyHandler({}))
    def metadata(key):
        request = urllib.request.Request('http://metadata.google.internal/computeMetadata/v1/instance/' + key,
                                         headers={'Metadata-Flavor': 'Google'})
        with opener.open(request, timeout=10) as response:
            if response.headers.get('Metadata-Flavor') != 'Google':
                raise RuntimeError('Unauthenticated metadata')
            return response.read().decode()
    if metadata('id') != '7237681467779354904' or metadata('name') != 'quantyra-lean-builder-02':
        raise RuntimeError('Foreign VM')
    for entry in Path('/proc').iterdir():
        if not entry.name.isdigit() or int(entry.name) == os.getpid():
            continue
        try:
            name = (entry / 'comm').read_text().strip()
            argv = (entry / 'cmdline').read_bytes().replace(b'\0', b' ').decode(errors='replace')
        except (FileNotFoundError, PermissionError):
            continue
        if name in ('lean', 'lake', 'cp', 'tar') or (name == 'python3' and
                any(token in argv for token in ('_worker.py', 'cloud_capture.py', 'full109_verify.py'))):
            raise RuntimeError('Compiler/copy/worker active: ' + str(entry))
    if (HOME / 'full109-consumption-v3-launch-once.json').exists():
        raise RuntimeError('Full109 trace already launched')
    run = HOME / RUN
    if digest(run / 'capture-manifest.json') != MANIFEST_SHA:
        raise RuntimeError('Settled full89 source capture identity changed')
    if digest(HOME / (RUN + '_evidence.tar.gz')) != ARCHIVE_SHA:
        raise RuntimeError('Original failed evidence archive changed')
    manifest = json.loads((run / 'capture-manifest.json').read_bytes())
    if manifest['cache_provenance']['run'] != WARM:
        raise RuntimeError('Foreign warm baseline')
    old = run / '.lake/packages'
    canonical = HOME / WARM / '.lake/packages'
    if old.is_symlink() or canonical.is_symlink():
        raise RuntimeError('Unexpected package-root symlink')
    old = old.resolve(strict=True)
    canonical = canonical.resolve(strict=True)
    if not old.is_relative_to(run.resolve()) or not canonical.is_relative_to((HOME / WARM).resolve()):
        raise RuntimeError('Root escape')
    return old, canonical


def plan():
    old, canonical = guards()
    if (CONTROL / 'plan.json').exists():
        raise RuntimeError('Existing plan; inspect it rather than overwrite')
    candidates = []
    for path in old.rglob('*'):
        if path.is_symlink() or not path.is_file():
            continue
        rel = path.relative_to(old)
        if not any(path.name.endswith(suffix) for suffix in ('.olean', '.olean.private', '.olean.server', '.ilean')):
            continue
        if not {'.lake', 'build', 'lib', 'lean'} <= set(rel.parts):
            continue
        info = path.stat()
        if info.st_nlink == 1 and info.st_size >= 1:
            candidates.append((info.st_blocks * 512, rel, info.st_size))
    rows, blocks, mismatches = [], 0, 0
    for allocated, rel, size in sorted(candidates, reverse=True):
        destination = canonical / rel
        if not destination.is_file() or not destination.resolve().is_relative_to(canonical):
            continue
        if destination.stat().st_size != size:
            mismatches += 1
            continue
        pin = digest(old / rel)
        if digest(destination) != pin:
            mismatches += 1
            continue
        rows.append({'relative': rel.as_posix(), 'sha256': pin, 'bytes': size, 'allocated_bytes': allocated})
        blocks += allocated
        if len(rows) % 20 == 0:
            print(json.dumps({'identical_candidates_verified': len(rows), 'allocated_bytes': blocks}), flush=True)
        if blocks >= TARGET:
            break
    if blocks < TARGET:
        raise RuntimeError('Insufficient identical dependency-object copies; no changes made')
    value = {'schema': 'full95-settled-dependency-cache-repoint-plan-v1', 'old_root': str(old),
             'canonical_root': str(canonical), 'rows': rows, 'allocated_bytes': blocks,
             'hash_or_size_mismatches_skipped': mismatches, 'disk_before_bytes': shutil.disk_usage(HOME).free,
             'original_archive_sha256': ARCHIVE_SHA, 'compiler_invoked': False, 'executed': False}
    write_new(CONTROL / 'plan.json', value)
    print(json.dumps({'plan': str(CONTROL / 'plan.json'), 'verified_files': len(rows),
                      'allocated_bytes': blocks, 'disk_before_bytes': value['disk_before_bytes'], 'executed': False}), flush=True)


def execute():
    old, canonical = guards()
    value = json.loads((CONTROL / 'plan.json').read_bytes())
    if value['old_root'] != str(old) or value['canonical_root'] != str(canonical):
        raise RuntimeError('Foreign plan roots')
    write_new(CONTROL / 'execute-once.json', {'plan_sha256': digest(CONTROL / 'plan.json'), 'compiler_invoked': False})
    receipt = {'schema': 'full95-settled-dependency-cache-repoint-execution-v1', 'applied': [],
               'disk_before_bytes': shutil.disk_usage(HOME).free, 'warm_files_written': False,
               'source_or_project_object_files_changed': False, 'failed_evidence_archive_changed': False,
               'compiler_invoked': False}
    for row in value['rows']:
        rel = Path(row['relative'])
        if rel.is_absolute() or '..' in rel.parts:
            raise RuntimeError('Unsafe relative path')
        path, destination = old / rel, canonical / rel
        if path.is_symlink() or not path.resolve().is_relative_to(old) or not destination.resolve().is_relative_to(canonical):
            raise RuntimeError('Symlink or root drift')
        info = path.stat()
        if not stat.S_ISREG(info.st_mode) or info.st_nlink != 1 or digest(path) != row['sha256'] or digest(destination) != row['sha256']:
            raise RuntimeError('Duplicate content identity changed')
        backup = path.with_name(path.name + '.full95-repoint-backup')
        if backup.exists():
            raise RuntimeError('Unexpected backup; inspect it')
        path.rename(backup)
        try:
            path.symlink_to(destination)
            if digest(path) != row['sha256'] or digest(destination) != row['sha256']:
                raise RuntimeError('Repointed content mismatch')
        except BaseException:
            if path.is_symlink():
                path.unlink()
            backup.rename(path)
            raise
        backup.unlink()
        receipt['applied'].append(row)
        (CONTROL / 'partial-execution.json').write_text(json.dumps(receipt, indent=2) + '\n')
    if digest(HOME / (RUN + '_evidence.tar.gz')) != ARCHIVE_SHA:
        raise RuntimeError('Original evidence archive drift')
    receipt['disk_after_bytes'] = shutil.disk_usage(HOME).free
    receipt['content_identity_verified_after_repoint'] = True
    receipt['reversible_by_copying_identical_canonical_bytes'] = True
    write_new(CONTROL / 'receipt.json', receipt)
    if receipt['disk_after_bytes'] <= receipt['disk_before_bytes']:
        raise RuntimeError('No actual space recovered; preserve repoint receipt')
    print(json.dumps({'repointed_files': len(receipt['applied']), 'disk_after_bytes': receipt['disk_after_bytes'],
                      'receipt_sha256': digest(CONTROL / 'receipt.json'), 'compiler_invoked': False}), flush=True)


if __name__ == '__main__':
    if sys.argv[1:] == ['--plan']:
        plan()
    elif sys.argv[1:] == ['--execute']:
        execute()
    else:
        raise SystemExit('Use --plan or --execute')
