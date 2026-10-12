"""Selective raw-byte Git preservation; disables automatic packing and preserves inherited dirt."""
from pathlib import Path
import json,hashlib,subprocess,shutil,sys
H=Path(__file__).resolve().parent;REPO=H.parents[2];sha=lambda b:hashlib.sha256(b).hexdigest().upper()
def git(args,**kw):return subprocess.check_output(['git','-c','core.longpaths=true','-c','gc.auto=0','-c','maintenance.auto=false',*args],cwd=REPO,**kw)
def main():
 sys.path.insert(0,str(H));import full119_authorized16_nested_custody_v3 as custody;custody.configured_guard().documents()
 manifest=H/'full118-focused-preservation-batch-v5.json';assert sha(manifest.read_bytes())=='532382C01983AE007178FE818B10266FEFF3CCB355BF28830F199F2BAADE8914';j=json.loads(manifest.read_bytes());rows=j['files'][:]
 for p in [manifest,Path(__file__)]:
  b=p.read_bytes();rows.append(dict(path=p.relative_to(REPO).as_posix(),sha256=sha(b),bytes=len(b)))
 assert not git(['diff','--cached','--name-only','-z']);head=git(['rev-parse','HEAD']).decode().strip();assert head=='50165032cbbc5ac9d871523bbc8a32f0d948ab38'
 free=shutil.disk_usage(H).free;rawbytes=sum(r['bytes'] for r in rows)
 if free-rawbytes-48*1024**2<1803550720:raise ValueError('Strong local reserve plus actual raw objects/index overhead fails')
 for r in rows:
  p=REPO/r['path'];assert p.is_file() and not p.is_symlink();b=p.read_bytes();assert len(b)==r['bytes'] and sha(b)==r['sha256']
 encoded='\n'.join(r['path'] for r in rows).encode()+b'\n';ids=git(['hash-object','-w','--no-filters','--stdin-paths'],input=encoded).decode().splitlines();assert len(ids)==len(rows)
 index=b''.join(('100644 '+oid+'\t'+r['path']).encode()+b'\0' for oid,r in zip(ids,rows));git(['update-index','-z','--index-info'],input=index)
 staged=set(git(['diff','--cached','--name-only','-z']).decode().strip('\0').split('\0'));assert staged=={r['path'] for r in rows}
 data=git(['cat-file','--batch'],input=b''.join((':'+r['path']+'\n').encode() for r in rows));pos=0
 for r in rows:
  end=data.index(b'\n',pos);header=data[pos:end].decode().split();assert header[1]=='blob';n=int(header[2]);b=data[end+1:end+1+n];assert n==r['bytes'] and sha(b)==r['sha256'];assert data[end+1+n:end+2+n]==b'\n';pos=end+2+n
 assert pos==len(data)
 d=H/'full118-focused-git-preservation-check-v5';d.mkdir(exist_ok=False);record=dict(previous_head=head,manifest_sha256=sha(manifest.read_bytes()),exact_raw_files=len(rows),raw_bytes=rawbytes,all_index_bytes_match_expected_sha256=True,inherited_dirt_staged=False,automatic_packing_disabled=True,free_before=free,free_after_objects=shutil.disk_usage(H).free,compiler_invoked=False);(d/'result.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8');(d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
 # Stage the verification record through the same no-filter path, then verify the record bytes.
 extras=[d/'result.json',d/'control.snapshot.py'];xids=git(['hash-object','-w','--no-filters','--stdin-paths'],input=('\n'.join(p.relative_to(REPO).as_posix() for p in extras)+'\n').encode()).decode().splitlines();git(['update-index','-z','--index-info'],input=b''.join(('100644 '+oid+'\t'+p.relative_to(REPO).as_posix()).encode()+b'\0' for oid,p in zip(xids,extras)))
 for p in extras:assert git(['show',':'+p.relative_to(REPO).as_posix()])==p.read_bytes()
 body=d/'commit-message.txt';body.write_text('Preserve Full118 failed native custody and exact authorized cleanup\n\nRetain native, stop and red audit evidence, Full119 source-only repair, actual cumulative archive custody tests, and frozen numerical offers. All numerical proof candidates remain uncompiled; no operator acceptance is claimed.\n',encoding='utf-8')
 result=git(['commit','-F',str(body)]).decode();print(result,flush=True);print(json.dumps(dict(head=git(['rev-parse','HEAD']).decode().strip(),free_after_commit=shutil.disk_usage(H).free,files=len(rows)+len(extras))),flush=True)
if __name__=='__main__':main()
