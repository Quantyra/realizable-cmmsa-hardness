"""Compress settled original text copies only when exact committed blobs prove custody."""
import ctypes,hashlib,json,shutil,subprocess
from pathlib import Path
from custody_checks import digest
HERE=Path(__file__).resolve().parent
REPO=HERE.parents[2]
BASE=Path('C:/Users/dfred/.quantyra/builder02')
def main():
    def git(*args):return subprocess.check_output(['git',*args],cwd=REPO)
    head=git('rev-parse','HEAD').decode().strip();assert head.startswith('3f6dbacb')
    assert git('rev-parse','--show-object-format').decode().strip()=='sha1'
    blobs={}
    for entry in git('ls-tree','-r','-z','--long',head).split(b'\0'):
        if not entry:continue
        fields,path=entry.split(b'\t',1);mode,kind,oid,size=fields.split()
        if kind==b'blob' and int(size)>=128000:blobs.setdefault(oid.decode(),path.decode())
    allocated=ctypes.windll.kernel32.GetCompressedFileSizeW
    allocated.argtypes=[ctypes.c_wchar_p,ctypes.POINTER(ctypes.c_uint32)];allocated.restype=ctypes.c_uint32
    candidates=[]
    for root in BASE.glob('full*'):
        if not root.is_dir():continue
        number=root.name.split('-')[0][4:]
        if not number.isdigit() or not 83<=int(number)<=110:continue
        for path in root.rglob('*'):
            if not path.is_file() or path.stat().st_size<128000:continue
            if path.suffix not in ('.json','.jsonl','.stdout','.stderr','.txt','.log','.patch','.csv'):continue
            high=ctypes.c_uint32();low=allocated(str(path),ctypes.byref(high));size=(high.value<<32)+low
            assert low!=0xffffffff
            if size>path.stat().st_size*.8:candidates.append((size,path))
    rows=[];skipped=[];verified={}
    for size,path in sorted(candidates,reverse=True):
        raw=path.read_bytes()
        oid=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        if oid not in blobs:
            skipped.append(dict(path=str(path),reason='No exact current-HEAD blob; excluded'));continue
        sha=hashlib.sha256(raw).hexdigest().upper()
        if oid not in verified:
            committed=git('cat-file','blob',oid);assert committed==raw;verified[oid]=sha
        assert verified[oid]==sha
        rows.append(dict(path=str(path),bytes=len(raw),sha256=sha,allocated_before=size,
            committed_blob=oid,committed_path=blobs[oid]))
    assert rows and git('rev-parse','HEAD').decode().strip()==head
    target=HERE/'full112-settled-originals-committed-lossless-v1';target.mkdir(exist_ok=False)
    (target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    (target/'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
    (target/'before.json').open('x').write(json.dumps(dict(head=head,files=rows,skipped_unmatched=skipped),indent=2)+'\n')
    before=shutil.disk_usage(HERE).free;commands=[]
    for i,row in enumerate(rows):
        path=Path(row['path']);assert digest(path)==row['sha256']
        argv=['compact.exe','/C','/F','/EXE:LZX',str(path)]
        child=subprocess.run(argv,capture_output=True,creationflags=subprocess.CREATE_NO_WINDOW)
        for s,data in [('stdout',child.stdout),('stderr',child.stderr)]:(target/f'{i}.{s}').open('xb').write(data)
        commands.append(dict(argv=argv,native_exit=child.returncode,stdout_sha256=digest(target/f'{i}.stdout'),stderr_sha256=digest(target/f'{i}.stderr')))
        (target/'commands.json').write_text(json.dumps(commands,indent=2)+'\n')
        assert child.returncode==0 and digest(path)==row['sha256'] and path.stat().st_size==row['bytes']
    assert git('rev-parse','HEAD').decode().strip()==head
    for row in rows:assert digest(Path(row['path']))==row['sha256']
    after=shutil.disk_usage(HERE).free
    report=dict(head=head,files=rows,skipped_unmatched=skipped,free_before=before,free_after=after,
        every_original_matches_exact_committed_blob=True,all_logical_sizes_and_hashes_unchanged=True,
        active_full112_and_author_folders_excluded=True,files_deleted=False,cloud_action_performed=False,compiler_invoked=False)
    (target/'result.json').open('x').write(json.dumps(report,indent=2)+'\n')
    assert after>=1536*1024**2
    print(json.dumps(dict(folder=str(target),files=len(rows),excluded_unmatched=len(skipped),free_before=before,free_after=after)),flush=True)
if __name__=='__main__':main()

