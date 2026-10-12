from pathlib import Path
import ctypes,hashlib,json,shutil,subprocess
H=Path(__file__).resolve().parent
BASE=Path('C:/Users/dfred/.quantyra/builder02/full119-exact-real-complex-operators-repair9-resource02/settled-cache-recovery-v1/openssh-execute-20261012T062350898827Z')
OUT=H/'full119-retired-plan-journal-ntfs-compression-v1'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest().upper()
class Standard(ctypes.Structure):
 _fields_=[('allocation',ctypes.c_longlong),('eof',ctypes.c_longlong),('links',ctypes.c_ulong),('pending',ctypes.c_byte),('directory',ctypes.c_byte)]
k=ctypes.WinDLL('kernel32',use_last_error=True)
k.CreateFileW.argtypes=[ctypes.c_wchar_p,ctypes.c_ulong,ctypes.c_ulong,ctypes.c_void_p,ctypes.c_ulong,ctypes.c_ulong,ctypes.c_void_p];k.CreateFileW.restype=ctypes.c_void_p
k.GetFileInformationByHandleEx.argtypes=[ctypes.c_void_p,ctypes.c_int,ctypes.c_void_p,ctypes.c_ulong];k.GetFileInformationByHandleEx.restype=ctypes.c_int
k.CloseHandle.argtypes=[ctypes.c_void_p];k.CloseHandle.restype=ctypes.c_int
def allocation(p):
 handle=k.CreateFileW(str(p),0x80,7,None,3,0x80,None);assert handle not in (None,ctypes.c_void_p(-1).value)
 try:
  info=Standard();assert k.GetFileInformationByHandleEx(handle,1,ctypes.byref(info),ctypes.sizeof(info));assert info.eof==p.stat().st_size and not info.directory;return info.allocation
 finally:assert k.CloseHandle(handle)
def main():
 OUT.mkdir(exist_ok=False);(OUT/'.gitattributes').write_bytes(b'* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n');(OUT/'control.snapshot.py').write_bytes(Path(__file__).read_bytes());commands=json.loads((BASE/'transport/commands.json').read_bytes());rows=[]
 root=BASE.parent.parent
 for folder in ['20261012T054106917625Z-b8664de71a3e','20261012T062252307153Z-172311e55cc2','20261012T064720149482Z-e1b3fcbe8f2f']:
  v=json.loads((root/'research-resume-20261011'/folder/'command.json').read_bytes());assert v['native_exit']==0
 plan_base=BASE.parent/'openssh-plan-20261012T054326853342Z'
 audit=BASE.parent/'complete-audit-v1';report=json.loads((audit/'audit.json').read_bytes());assert report['all_rows_match']
 candidates=[]
 plan_commands=json.loads((plan_base/'transport/commands.json').read_bytes())
 for op in sorted(plan_base.glob('operation-*.json')):
  r=json.loads(op.read_bytes());p=Path(r['local_result']);native=[c for c in plan_commands if c.get('stdout_path')==str(p)];assert len(native)==1 and native[0]['native_exit']==0 and native[0]['argv'][-1].endswith('/plan.json')
  assert sha(p)==r['result_sha256']==native[0]['stdout_sha256'];v=json.loads(p.read_bytes());assert not v['executed'] and not v['compiler_invoked'];candidates.append((p,native[0],'retired-plan-output',r['number']))
 audit_commands=json.loads((audit/'transport/commands.json').read_bytes())
 for native in audit_commands:
  if native['argv'][-1].startswith('cat ') and native['argv'][-1].endswith('/execution-journal.jsonl'):
   p=Path(native['stdout_path']);assert native['native_exit']==0 and sha(p)==native['stdout_sha256'];matching=[r for r in report['files'] if r['path']==str(p)];assert len(matching)==1 and matching[0]['sha256']==sha(p);[json.loads(line) for line in p.read_bytes().splitlines()];candidates.append((p,native,'terminal-audit-journal',p.name))
 for p,native,kind,scope in candidates:
  assert p.resolve().is_relative_to(root.resolve()) and not p.is_symlink() and p.suffix=='.stdout'
  rows.append(dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p),allocation_before=allocation(p),native_receipt_process_pid=native['pid'],native_receipt_process_exit=0,scope=scope,kind=kind))
 assert rows;(OUT/'frozen-positive-plan.json').write_text(json.dumps(dict(files=rows,only_terminal_current_turn_receipt_outputs=True,source_and_config_and_live_logs_excluded=True,paths_deleted=False),indent=2)+'\n',encoding='utf8');before=shutil.disk_usage(H).free;results=[]
 for i,r in enumerate(rows):
  p=Path(r['path']);assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes'];argv=['compact.exe','/C','/Q','/I',str(p)]
  with (OUT/f'{i:03d}.stdout').open('xb') as out,(OUT/f'{i:03d}.stderr').open('xb') as err:code=subprocess.run(argv,stdout=out,stderr=err,creationflags=subprocess.CREATE_NO_WINDOW).returncode
  assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes'];assert all(json.loads(line) is not None for line in p.read_bytes().splitlines()) if r['kind']=='terminal-audit-journal' else json.loads(p.read_bytes())['executed'] is False;results.append(dict(**r,argv=argv,native_exit=code,allocation_after=allocation(p),readable_custody_and_content_unchanged=True));assert code==0
 report=dict(files=results,free_before=before,free_after=shutil.disk_usage(H).free,native_allocation_bytes_reclaimed=sum(r['allocation_before']-r['allocation_after'] for r in results),allocation_measurement='Win32 FileStandardInfo.AllocationSize',files_deleted=False,source_or_config_bytes_changed=False,compiler_invoked=False)
 (OUT/'receipt.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf8');print(json.dumps(dict(files=len(results),native_allocation_bytes_reclaimed=report['native_allocation_bytes_reclaimed'],free_after=report['free_after'],receipt_sha256=sha(OUT/'receipt.json'))))
if __name__=='__main__':main()
