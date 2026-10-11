"""Preserve exact settled text originals, then compress without changing their bytes."""
import ctypes
import gzip
import hashlib
import io
import json
from pathlib import Path
import shutil
import subprocess
import tarfile
from custody_checks import digest

HERE = Path(__file__).resolve().parent
BASE = Path('C:/Users/dfred/.quantyra/builder02').resolve()


def main():
    prior = HERE / 'full112-settled-originals-committed-lossless-v1/result.json'
    value = json.loads(prior.read_bytes())
    allocated = ctypes.windll.kernel32.GetCompressedFileSizeW
    allocated.argtypes = [ctypes.c_wchar_p, ctypes.POINTER(ctypes.c_uint32)]
    allocated.restype = ctypes.c_uint32
    candidates = []
    for row in value['skipped_unmatched']:
        path = Path(row['path']).resolve(strict=True)
        assert path.is_relative_to(BASE)
        resource = BASE / path.parts[len(BASE.parts)]
        number = int(resource.name.split('-')[0][4:])
        assert 83 <= number <= 110
        if not (resource / 'launch-once.json').is_file():
            continue  # Original unlaunched Full84 directory is not a settled native run.
        marker = json.loads((resource / 'launch-once.json').read_bytes())
        check = Path(marker['preflight'])
        receipt = json.loads((check / 'terminal-custody.json').read_bytes())
        assert receipt['run'] == marker['run'] and receipt['terminal']['native_terminal']
        assert path.suffix in ('.json', '.jsonl', '.stdout', '.stderr', '.txt', '.log', '.patch', '.csv')
        high = ctypes.c_uint32(); low = allocated(str(path), ctypes.byref(high))
        assert low != 0xffffffff
        size = (high.value << 32) + low
        if size > path.stat().st_size * .8:
            candidates.append((size, path, digest(check / 'terminal-custody.json')))
    selected = []; logical = 0
    for size, path, terminal in sorted(candidates, reverse=True):
        if logical + path.stat().st_size > 120 * 1024**2:
            continue
        selected.append(dict(original=str(path), member=f'{len(selected):03d}-' + path.name,
            bytes=path.stat().st_size, sha256=digest(path), allocated_before=size, settled_terminal_custody_sha256=terminal))
        logical += path.stat().st_size
    assert selected and shutil.disk_usage(HERE).free >= 1536 * 1024**2 + logical + 8 * 1024**2
    target = HERE / 'full113-prior-text-preserved-lossless-v2'
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    (target / 'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
    (target / 'before.json').open('x').write(json.dumps(dict(files=selected, prior_exclusion_record=str(prior), prior_exclusion_sha256=digest(prior)), indent=2) + '\n')
    archive = target / 'complete-originals.tar.gz'
    with archive.open('xb') as raw:
        with gzip.GzipFile(filename='', mode='wb', fileobj=raw, mtime=0) as compressed:
            with tarfile.open(fileobj=compressed, mode='w') as tar:
                for row in selected:
                    data = Path(row['original']).read_bytes()
                    assert len(data) == row['bytes'] and hashlib.sha256(data).hexdigest().upper() == row['sha256']
                    member = tarfile.TarInfo(row['member']); member.size = len(data); member.mode = 0o644
                    tar.addfile(member, io.BytesIO(data))
    with tarfile.open(archive, 'r:gz') as tar:
        assert len(tar.getmembers()) == len(selected)
        for row in selected:
            assert tar.extractfile(row['member']).read() == Path(row['original']).read_bytes()
    archive_pin = digest(archive)
    (target / 'custody-before-compression.json').open('x').write(json.dumps(dict(files=selected,
        payload=dict(file=archive.name, bytes=archive.stat().st_size, sha256=archive_pin), every_original_roundtrip_equal=True), indent=2) + '\n')
    before = shutil.disk_usage(HERE).free; commands = []
    for i, row in enumerate(selected):
        path = Path(row['original']); assert digest(path) == row['sha256']
        argv = ['compact.exe', '/C', '/F', '/EXE:LZX', str(path)]
        child = subprocess.run(argv, capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
        for stream, data in [('stdout', child.stdout), ('stderr', child.stderr)]:
            (target / f'{i}.{stream}').open('xb').write(data)
        commands.append(dict(argv=argv, native_exit=child.returncode, stdout_sha256=digest(target / f'{i}.stdout'), stderr_sha256=digest(target / f'{i}.stderr')))
        (target / 'commands.json').write_text(json.dumps(commands, indent=2) + '\n')
        assert child.returncode == 0 and digest(path) == row['sha256'] and path.stat().st_size == row['bytes']
    assert digest(archive) == archive_pin
    for row in selected:
        assert digest(Path(row['original'])) == row['sha256']
    after = shutil.disk_usage(HERE).free
    (target / 'result.json').open('x').write(json.dumps(dict(files=selected, free_before=before, free_after=after,
        complete_unique_originals_preserved_before_compression=True, all_logical_bytes_and_hashes_unchanged=True,
        active_full113_excluded=True, files_deleted=False, cloud_action=False, compiler_invoked=False), indent=2) + '\n')
    assert after >= 1536 * 1024**2
    print(json.dumps(dict(folder=str(target), files=len(selected), payload_bytes=archive.stat().st_size,
        payload_sha256=archive_pin, free_before=before, free_after=after)), flush=True)


if __name__ == '__main__':
    main()
