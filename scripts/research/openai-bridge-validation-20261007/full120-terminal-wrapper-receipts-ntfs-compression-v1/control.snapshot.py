from pathlib import Path
import hashlib,json,shutil,subprocess,sys
H=Path(__file__).resolve().parent
sys.path.insert(0,str(H))
from compress_full119_retired_plans_journals_ntfs_v1 import allocation
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
def main():
 terminal=H/'pinned-unused-three-cache-scopes-ntfs-compression-v1'
 marker=json.loads((terminal/'original-handle-terminal.json').read_bytes());assert marker['native_exit']==0 and marker['terminal_verified'] and sha((terminal/'receipt.json').read_bytes())==marker['receipt_sha256']
 failure=H/'full120-recovery-local-capacity-failure-v1';index=json.loads((failure/'index.json').read_bytes());assert index['native_exit']==1 and index['remote_execute_marker_absent']
 selected=[]
 roots=[Path('C:/Users/dfred/.quantyra/builder02')/name/'research-resume-20261011' for name in ['full119-exact-real-complex-operators-repair9-resource02','full120-exact-real-complex-operators-warning-cleanup-resource02']]
 for root in roots:
  for folder in root.iterdir():
   command=folder/'command.json'
   if not command.is_file():continue
   record=json.loads(command.read_bytes())
   if 'native_exit' not in record:continue
   for name in ['stdout','stderr']:assert sha((folder/name).read_bytes())==record[name+'_sha256']
   selected.extend(folder.glob('actual*.json'))
 out=H/'full120-terminal-wrapper-receipts-ntfs-compression-v1';out.mkdir(exist_ok=False);(out/'.gitattributes').write_bytes(b'* -text\n');(out/'control.snapshot.py').write_bytes(Path(__file__).read_bytes());rows=[]
 for p in selected:
  if p.stat().st_file_attributes&0x800:continue
  assert p.is_file() and not p.is_symlink() and not(p.stat().st_file_attributes&0x400) and any(p.resolve().is_relative_to(root.resolve()) for root in roots)
  b=p.read_bytes();json.loads(b);rows.append(dict(path=str(p),bytes=len(b),sha256=sha(b),allocation_before=allocation(p)))
 assert rows
 (out/'frozen-positive-plan.json').write_text(json.dumps(dict(files=rows,terminal_command_and_stdout_stderr_pins_verified=True, terminal_handles=[95138,10933],source_program_config_and_active_inputs_excluded=True),indent=2)+'\n');before=shutil.disk_usage(H).free
 with (out/'stdout').open('xb') as stdout,(out/'stderr').open('xb') as stderr:code=subprocess.run(['compact.exe','/C','/Q','/I']+[r['path'] for r in rows],stdout=stdout,stderr=stderr,creationflags=subprocess.CREATE_NO_WINDOW).returncode
 assert code==0
 for r in rows:
  p=Path(r['path']);b=p.read_bytes();assert len(b)==r['bytes'] and sha(b)==r['sha256'];json.loads(b);r.update(allocation_after=allocation(p),native_exit=code,content_unchanged=True,json_readable=True)
 report=dict(files=rows,free_before=before,free_after=shutil.disk_usage(H).free,reclaimed=sum(r['allocation_before']-r['allocation_after'] for r in rows),compiler_invoked=False,files_deleted=False)
 (out/'receipt.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(files=len(rows),reclaimed=report['reclaimed'],free_after=report['free_after'],receipt_sha256=sha((out/'receipt.json').read_bytes()))))
if __name__=='__main__':main()
