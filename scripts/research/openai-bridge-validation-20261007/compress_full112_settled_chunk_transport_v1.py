"""Compress settled raw chunk transports only after checking their exact archive ranges."""
import base64,ctypes,hashlib,json,shutil,subprocess
from pathlib import Path
from custody_checks import digest
HERE=Path(__file__).resolve().parent
BASE=Path('C:/Users/dfred/.quantyra/builder02')
def main():
    allocated=ctypes.windll.kernel32.GetCompressedFileSizeW
    allocated.argtypes=[ctypes.c_wchar_p,ctypes.POINTER(ctypes.c_uint32)];allocated.restype=ctypes.c_uint32
    rows=[];sources=[]
    for n in (103,105):
        root,=BASE.glob('full'+str(n)+'-*')
        mark=json.loads((root/'launch-once.json').read_bytes());check=Path(mark['preflight'])
        custody=json.loads((check/'terminal-custody.json').read_bytes())
        stop=json.loads((check/'vm-termination.json').read_bytes())
        assert custody['run']==mark['run']==stop['run'] and custody['terminal']['native_terminal']
        assert stop['independent']['status']=='TERMINATED'
        archive=Path(custody['custody']['repository_path']);pin=custody['custody']['remote_sha256']
        assert digest(archive)==pin
        sources.append(dict(run=mark['run'],archive=str(archive),sha256=pin,custody_sha256=digest(check/'terminal-custody.json')))
        with archive.open('rb') as original:
            for folder in (check/'custody-chunk-recovery').iterdir():
                if not folder.is_dir() or not (folder/'commands.json').is_file():continue
                commands=json.loads((folder/'commands.json').read_bytes())
                for command in commands:
                    path=Path(command['stdout_path'])
                    if not path.is_absolute():path=folder/path
                    if not path.is_file() or path.stat().st_size<128000:continue
                    assert path.resolve().is_relative_to(check.resolve())
                    high=ctypes.c_uint32();low=allocated(str(path),ctypes.byref(high));size=(high.value<<32)+low
                    assert low!=0xffffffff
                    if size<=path.stat().st_size*.8:continue
                    assert digest(path)==command['stdout_sha256']
                    lines=path.read_bytes().splitlines()
                    assert len(lines)==2
                    metadata=json.loads(lines[0]);payload=base64.b64decode(lines[1],validate=True)
                    assert metadata['run']==mark['run'] and metadata['archive_sha256']==pin
                    assert len(payload)==metadata['bytes'] and hashlib.sha256(payload).hexdigest().upper()==metadata['chunk_sha256']
                    assert 0<=metadata['offset'] and metadata['offset']+len(payload)<=archive.stat().st_size
                    original.seek(metadata['offset']);assert original.read(len(payload))==payload
                    rows.append(dict(path=str(path),bytes=path.stat().st_size,sha256=digest(path),allocated_before=size,
                        original_transport_exit=command['native_exit'],archive=str(archive),archive_range=metadata))
    assert rows and len({r['path'] for r in rows})==len(rows)
    target=HERE/'full112-settled-chunk-transport-lossless-v1';target.mkdir(exist_ok=False)
    (target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    (target/'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
    (target/'before.json').open('x').write(json.dumps(dict(files=rows,sources=sources),indent=2)+'\n')
    before=shutil.disk_usage(HERE).free;commands=[]
    for i,row in enumerate(rows):
        path=Path(row['path']);assert digest(path)==row['sha256']
        argv=['compact.exe','/C','/F','/EXE:LZX',str(path)]
        child=subprocess.run(argv,capture_output=True,creationflags=subprocess.CREATE_NO_WINDOW)
        for s,data in [('stdout',child.stdout),('stderr',child.stderr)]:(target/f'{i}.{s}').open('xb').write(data)
        commands.append(dict(argv=argv,native_exit=child.returncode,stdout_sha256=digest(target/f'{i}.stdout'),stderr_sha256=digest(target/f'{i}.stderr')))
        (target/'commands.json').write_text(json.dumps(commands,indent=2)+'\n')
        assert child.returncode==0 and digest(path)==row['sha256'] and path.stat().st_size==row['bytes']
    after=shutil.disk_usage(HERE).free
    result=dict(files=rows,sources=sources,free_before=before,free_after=after,
        complete_original_archive_ranges_verified=True,all_logical_sizes_and_hashes_unchanged=True,
        original_transport_exit_codes_unchanged=True,files_deleted=False,cloud_action_performed=False,compiler_invoked=False)
    (target/'result.json').open('x').write(json.dumps(result,indent=2)+'\n')
    assert after>=1536*1024**2
    print(json.dumps(dict(folder=str(target),files=len(rows),free_before=before,free_after=after)),flush=True)
if __name__=='__main__':main()

