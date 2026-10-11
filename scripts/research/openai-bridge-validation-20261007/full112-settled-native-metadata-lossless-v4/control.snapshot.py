"""Losslessly compress settled native text only after exact original archive checks."""
import ctypes,hashlib,json,shutil,subprocess,tarfile
from pathlib import Path
from custody_checks import digest
HERE=Path(__file__).resolve().parent
BASE=Path('C:/Users/dfred/.quantyra/builder02')
NUMBERS=(83,84,85,86,87,88,89,90,91,92,95,97,100,101,102,103,105,107,108,109,110,111)

def main():
    allocated=ctypes.windll.kernel32.GetCompressedFileSizeW
    allocated.argtypes=[ctypes.c_wchar_p,ctypes.POINTER(ctypes.c_uint32)]
    allocated.restype=ctypes.c_uint32
    paths=[];records=[]
    for n in NUMBERS:
        resource,=[p for p in BASE.glob('full'+str(n)+'-*') if p.is_dir() and (p/'launch-once.json').is_file()]
        marker=json.loads((resource/'launch-once.json').read_bytes())
        check=Path(marker['preflight']).resolve(strict=True)
        assert check.is_relative_to((resource/'checks').resolve())
        stop=json.loads((check/'vm-termination.json').read_bytes())
        receipt=json.loads((check/'terminal-custody.json').read_bytes())
        assert marker['run']==stop['run']==receipt['run']
        assert receipt['terminal']['native_terminal'] and stop['independent']['status']=='TERMINATED'
        archive=Path(receipt['custody']['repository_path'])
        assert digest(archive)==receipt['custody']['remote_sha256']
        records.append(dict(number=n,run=marker['run'],archive=str(archive),sha256=digest(archive),
            terminal_custody_sha256=digest(check/'terminal-custody.json'),historical_stop_sha256=digest(check/'vm-termination.json')))
        with tarfile.open(archive,'r:gz') as tar:
            for member in tar.getmembers():
                if not member.isfile() or member.size<128000:continue
                path=check/'qualified-native'/marker['run']/'remote-evidence'/member.name
                if path.suffix not in ('.json','.jsonl','.stdout','.stderr','.txt','.log','.patch','.lean'):continue
                if not path.is_file():continue
                assert path.resolve(strict=True).is_relative_to(check)
                high=ctypes.c_uint32();low=allocated(str(path),ctypes.byref(high));size=(high.value<<32)+low
                assert low!=0xffffffff
                if size<=path.stat().st_size*0.8:continue
                with tar.extractfile(member) as stream:pin=hashlib.file_digest(stream,'sha256').hexdigest().upper()
                assert path.stat().st_size==member.size and digest(path)==pin
                paths.append(dict(path=str(path),bytes=member.size,sha256=pin,allocated_before=size,archive=str(archive),member=member.name))
    assert paths and len({r['path'] for r in paths})==len(paths)
    target=HERE/'full112-settled-native-metadata-lossless-v4';target.mkdir(exist_ok=False)
    (target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    (target/'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
    (target/'before.json').open('x').write(json.dumps(dict(files=paths,native_records=records),indent=2)+'\n')
    before=shutil.disk_usage(HERE).free;commands=[]
    for i,row in enumerate(paths):
        path=Path(row['path']);assert digest(path)==row['sha256']
        argv=['compact.exe','/C','/F','/EXE:LZX',str(path)]
        result=subprocess.run(argv,capture_output=True,creationflags=subprocess.CREATE_NO_WINDOW)
        for name,data in [('stdout',result.stdout),('stderr',result.stderr)]:(target/f'{i}.{name}').open('xb').write(data)
        commands.append(dict(argv=argv,native_exit=result.returncode,
            stdout_sha256=digest(target/f'{i}.stdout'),stderr_sha256=digest(target/f'{i}.stderr')))
        (target/'commands.json').write_text(json.dumps(commands,indent=2)+'\n')
        assert result.returncode==0 and digest(path)==row['sha256'] and path.stat().st_size==row['bytes']
    for row in paths:assert digest(Path(row['path']))==row['sha256']
    after=shutil.disk_usage(HERE).free
    report=dict(files=paths,native_records=records,free_before=before,free_after=after,
        original_archive_bytes_verified=True,all_logical_sizes_and_hashes_unchanged=True,
        historical_termination_not_current_VM_state=True,files_deleted=False,cloud_action_performed=False,compiler_invoked=False)
    (target/'result.json').open('x').write(json.dumps(report,indent=2)+'\n')
    assert after>=1536*1024**2
    print(json.dumps(dict(folder=str(target),files=len(paths),free_before=before,free_after=after)),flush=True)
if __name__=='__main__':main()

