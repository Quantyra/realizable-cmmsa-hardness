from pathlib import Path
import hashlib,json,shutil,subprocess,sys
H=Path(__file__).resolve().parent
sys.path.insert(0,str(H))
from compress_full119_retired_plans_journals_ntfs_v1 import allocation
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
def main():
 selected=[]
 for name in ['pinned-unused-small-residual-cache-scopes-compression-v1']:
  terminal=H/name;marker=json.loads((terminal/'original-handle-terminal.json').read_bytes());assert marker['native_exit']==0 and marker['terminal_verified'] and sha((terminal/'receipt.json').read_bytes())==marker['receipt_sha256']
  selected += [terminal/'receipt.json',terminal/'frozen-positive-plan.json']
 assert (H/'pinned-unused-small-residual-cache-scopes-plan-v1/frozen-positive-plan.json').read_bytes()==(terminal/'frozen-positive-plan.json').read_bytes()
 selected.append(H/'pinned-unused-small-residual-cache-scopes-plan-v1/frozen-positive-plan.json')
 out=H/'full120-terminal-capacity-evidence-ntfs-compression-v4';out.mkdir(exist_ok=False);(out/'.gitattributes').write_bytes(b'* -text\n');(out/'control.snapshot.py').write_bytes(Path(__file__).read_bytes());rows=[]
 for p in selected:
  if p.stat().st_file_attributes&0x800:continue
  assert p.is_file() and not p.is_symlink() and not(p.stat().st_file_attributes&0x400) and p.resolve().is_relative_to(H.resolve())
  b=p.read_bytes();json.loads(b);rows.append(dict(path=str(p),bytes=len(b),sha256=sha(b),allocation_before=allocation(p)))
 assert rows
 (out/'frozen-positive-plan.json').write_text(json.dumps(dict(files=rows,terminal_handles=[57471],source_program_config_and_active_inputs_excluded=True),indent=2)+'\n');before=shutil.disk_usage(H).free
 with (out/'stdout').open('xb') as stdout,(out/'stderr').open('xb') as stderr:code=subprocess.run(['compact.exe','/C','/Q','/I']+[r['path'] for r in rows],stdout=stdout,stderr=stderr,creationflags=subprocess.CREATE_NO_WINDOW).returncode
 assert code==0
 for r in rows:
  p=Path(r['path']);b=p.read_bytes();assert len(b)==r['bytes'] and sha(b)==r['sha256'];json.loads(b);r.update(allocation_after=allocation(p),native_exit=code,content_unchanged=True,json_readable=True)
 report=dict(files=rows,free_before=before,free_after=shutil.disk_usage(H).free,reclaimed=sum(r['allocation_before']-r['allocation_after'] for r in rows),compiler_invoked=False,files_deleted=False)
 (out/'receipt.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(files=len(rows),reclaimed=report['reclaimed'],free_after=report['free_after'],receipt_sha256=sha((out/'receipt.json').read_bytes()))))
if __name__=='__main__':main()
