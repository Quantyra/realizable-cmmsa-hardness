"""Lossless compression of settled review-source copies verified against native custody."""
import ctypes
import hashlib
import io
import json
from pathlib import Path
import shutil
import subprocess
import tarfile
from custody_checks import digest, verify_local_custody

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
BASE = Path('C:/Users/dfred/.quantyra/builder02').resolve()
PARENT = BASE / 'full113-exact-real-complex-operators-repair3-resource02'


def main():
    marker = json.loads((PARENT/'launch-once.json').read_bytes())
    check = Path(marker['preflight'])
    custody = json.loads((check/'terminal-custody.json').read_bytes())['custody']
    assert custody['remote_sha256'] == '60ED6FF40DAE28268D1C52EF5ECD78B354BA3E8FE347E5AFF14986C53BE36213'
    verify_local_custody(custody['short_path'],custody['repository_path'],custody['remote_sha256'],custody['bytes'])
    pool = {}
    def ingest(archive, prefix):
        for member in archive.getmembers():
            if member.isfile() and member.name.endswith('.lean') and member.size >= 4096:
                raw = archive.extractfile(member).read()
                pin = hashlib.sha256(raw).hexdigest().upper()
                pool.setdefault(pin,dict(archive=prefix,member=member.name,bytes=len(raw)))
    with tarfile.open(custody['repository_path'],'r:gz') as native:
        for name in ('package-sources.tar.gz','core-sources.tar.gz'):
            raw = native.extractfile(name).read()
            with tarfile.open(fileobj=io.BytesIO(raw),mode='r:gz') as sources:
                ingest(sources,dict(native_archive_sha256=custody['remote_sha256'],member=name,sha256=hashlib.sha256(raw).hexdigest().upper()))
    assert digest(PARENT/'input-archive.tar.gz') == 'BE67B48A7D6AA2745A1D28B99953E29B5764686EECFE4EDCFA01908872DE7EC2'
    with tarfile.open(PARENT/'input-archive.tar.gz','r:gz') as sources:
        ingest(sources,dict(input_archive=str(PARENT/'input-archive.tar.gz'),sha256=digest(PARENT/'input-archive.tar.gz')))
    allocated = ctypes.windll.kernel32.GetCompressedFileSizeW
    allocated.argtypes = [ctypes.c_wchar_p, ctypes.POINTER(ctypes.c_uint32)]
    allocated.restype = ctypes.c_uint32
    rows=[]; excluded=[]
    for number in (89,90,95,97,100,103,105,107):
        root, = [p for p in BASE.glob('full'+str(number)+'-*') if (p/'launch-once.json').is_file()]
        run=json.loads((root/'launch-once.json').read_bytes()); oldcheck=Path(run['preflight'])
        terminal=json.loads((oldcheck/'terminal-custody.json').read_bytes())
        assert terminal['run']==run['run'] and terminal['terminal']['native_terminal']
        for review in root.glob('consumption*/qualification*/review-sources'):
            assert review.resolve(strict=True).is_relative_to(root.resolve())
            for path in review.rglob('*.lean'):
                if not path.is_file() or path.stat().st_size<4096: continue
                assert path.resolve(strict=True).is_relative_to(review.resolve())
                high=ctypes.c_uint32();low=allocated(str(path),ctypes.byref(high));assert low!=0xffffffff
                size=(high.value<<32)+low
                if size<=path.stat().st_size*.8: continue
                pin=digest(path)
                if pin not in pool:
                    excluded.append(dict(path=str(path),sha256=pin));continue
                assert path.stat().st_size==pool[pin]['bytes']
                rows.append(dict(path=str(path),bytes=path.stat().st_size,sha256=pin,allocated_before=size,exact_source_custody=pool[pin],settled_run=run['run']))
    assert rows and len({r['path'] for r in rows})==len(rows)
    out=HERE/'full114-settled-review-sources-lossless-v1';out.mkdir(exist_ok=False)
    (out/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    (out/'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
    before=shutil.disk_usage(HERE).free
    (out/'before.json').open('x').write(json.dumps(dict(files=rows,unmatched_excluded=excluded),indent=2)+'\n')
    commands=[]
    for start in range(0,len(rows),24):
        batch=rows[start:start+24];assert all(digest(r['path'])==r['sha256'] for r in batch)
        argv=['compact.exe','/C','/F','/EXE:LZX',*[r['path'] for r in batch]]
        child=subprocess.run(argv,capture_output=True,creationflags=subprocess.CREATE_NO_WINDOW)
        for stream,data in [('stdout',child.stdout),('stderr',child.stderr)]:
            (out/f'{start}.{stream}').open('xb').write(data)
        commands.append(dict(argv=argv,native_exit=child.returncode,stdout_sha256=digest(out/f'{start}.stdout'),stderr_sha256=digest(out/f'{start}.stderr')))
        (out/'commands.json').write_text(json.dumps(commands,indent=2)+'\n')
        assert child.returncode==0 and all(digest(r['path'])==r['sha256'] for r in batch)
        if start%480==0: print(json.dumps(dict(compressed_through=start+len(batch),total=len(rows))),flush=True)
    assert all(digest(r['path'])==r['sha256'] for r in rows)
    after=shutil.disk_usage(HERE).free
    report=dict(files=len(rows),unmatched_excluded=len(excluded),free_before=before,free_after=after,
        concurrent_disk_activity_means_free_delta_is_not_exclusive_savings=True,
        all_logical_bytes_unchanged=True,all_sources_match_preserved_native_or_input_archive=True,
        only_settled_review_copies_modified_physically=True,files_deleted=False,compiler_invoked=False)
    (out/'result.json').open('x').write(json.dumps(report,indent=2)+'\n')
    assert after>=1536*1024**2
    print(json.dumps(report),flush=True)


if __name__=='__main__':main()
