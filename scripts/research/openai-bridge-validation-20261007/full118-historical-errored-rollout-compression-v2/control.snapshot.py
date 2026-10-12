"""Bounded reversible NTFS compression of two positively identified errored campaign logs."""
import json,hashlib,subprocess,ctypes,shutil,time
from pathlib import Path
H=Path(__file__).resolve().parent
S=Path('C:/Users/dfred/.codex/sessions/2026/10/11')
PARENT='01a12c54-2846-7e20-8448-d8b5899600ec'
ROWS=[('rollout-2026-10-11T11-05-40-01a12cc9-1d4d-7fe3-b1ec-294fc04f2e99.jsonl','/root/side_law_recovery'),('rollout-2026-10-11T09-44-30-01a12c7e-cd78-78e3-ae33-54ac6c602152.jsonl','/root/side_extension_recovery'),('rollout-2026-10-11T10-40-52-01a12cb2-671e-73b0-a034-015a439b9f69.jsonl','/root/refresh_counts')]
def hashed(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest().upper()
def allocated(p):
 high=ctypes.c_ulong();fun=ctypes.windll.kernel32.GetCompressedFileSizeW;fun.argtypes=[ctypes.c_wchar_p,ctypes.POINTER(ctypes.c_ulong)];fun.restype=ctypes.c_ulong;low=fun(str(p),ctypes.byref(high));return (high.value<<32)+low

def main():
 d=H/'full118-historical-errored-rollout-compression-v2';d.mkdir(exist_ok=False);beforefree=shutil.disk_usage(H).free;rows=[]
 for name,task in ROWS:
  p=S/name;q=p.resolve();assert q.parent==S.resolve() and not p.is_symlink() and not p.is_junction();assert task not in ['/root','/root/compiler_custody'];st=p.stat();assert time.time()-st.st_mtime>1800
  with p.open('r',encoding='utf-8') as f:m=json.loads(f.readline())['payload']
  a=m['source']['subagent']['thread_spawn'];assert a['agent_path']==task and a['parent_thread_id']==PARENT and m['parent_thread_id']==PARENT;assert m['cwd']==str(Path('C:/Users/dfred/Desktop/Projects/IGH/Quantyra-AI-Planning'))
  b=hashed(p);old=allocated(p);r=subprocess.run(['compact.exe','/C','/I','/Q','/A','/F',str(p)],capture_output=True);(d/(task.split('/')[-1]+'.stdout')).write_bytes(r.stdout);(d/(task.split('/')[-1]+'.stderr')).write_bytes(r.stderr);assert r.returncode==0;assert p.stat().st_size==st.st_size and hashed(p)==b
  rows.append(dict(path=str(p),agent_path=task,thread_id=m['id'],parent_thread_id=PARENT,closed_error_status_source='Root documented historical provider failures and closed successor handoff; exact session_meta task and same parent thread; active tree excludes these tasks',logical_bytes=st.st_size,sha256_before=b,sha256_after=b,allocated_before=old,allocated_after=allocated(p),native_exit=r.returncode,content_bytes_unchanged=True,deleted=False))
 j=dict(files=rows,free_before=beforefree,free_after=shutil.disk_usage(H).free,allocated_reclaimed_bytes=sum(r['allocated_before']-r['allocated_after'] for r in rows),active_root_and_compiler_logs_excluded=True,no_log_copy_or_deletion=True,no_source_or_archive_changes=True,compiler_invoked=False)
 (d/'receipt.json').write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8');(d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes());print(json.dumps(dict(receipt_sha256=hashed(d/'receipt.json'),allocated_reclaimed_bytes=j['allocated_reclaimed_bytes'],free_after=j['free_after'])))
if __name__=='__main__':main()
