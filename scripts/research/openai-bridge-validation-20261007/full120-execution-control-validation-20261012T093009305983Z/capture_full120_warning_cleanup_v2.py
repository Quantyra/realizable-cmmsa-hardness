from pathlib import Path
import hashlib,json,re,difflib
H=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
def boundaries(text):return [line for line in text.splitlines() if re.match(r'^\s*(import|namespace|end)\b',line)]
def headers(text):
 starts=list(re.finditer(r'(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|public)\s+)*(?:theorem|lemma|def|abbrev)\s+\w+\b',text));return [text[a.start():text.find(':=',a.start())].strip() for a in starts]
def main():
 s=H/'full120-warning-cleanup-offer-v2';raw=(s/'manifest.json').read_bytes();m=json.loads(raw);assert sha((H/m['warning_packet']).read_bytes())==m['warning_packet_index_sha256'];data={'manifest.json':raw};diffs={}
 for r in m['files']:
  b=(s/r['path']).read_bytes();old=(H/'full119-review-source-capsule-v1'/r['path']).read_bytes();assert sha(b)==r['sha256'] and len(b)==r['bytes'];name=Path(r['path']).name
  if 'Full119_sha256' in r:
   assert sha(old)==r['Full119_sha256'];a=old.decode('utf8');z=b.decode('utf8');assert boundaries(a)==boundaries(z) and headers(a)==headers(z);assert not b.startswith(bytes.fromhex('efbbbf'));diffs[name]=''.join(difflib.unified_diff(a.splitlines(keepends=True),z.splitlines(keepends=True),fromfile='Full119/'+name,tofile='Full120/'+name))
  else:assert b==old
  if 'Full120_v1_sha256' in r:assert sha((H/'full120-warning-cleanup-capture-v1'/name).read_bytes())==r['Full120_v1_sha256']
  data[name]=b
 b=(s/'ARGUMENT.md').read_bytes();assert sha(b)==m['argument_sha256'] and len(b)==m['argument_bytes'];data['ARGUMENT.md']=b
 d=H/'full120-warning-cleanup-capture-v2';d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n');rows=[]
 for n,b in data.items():(d/n).write_bytes(b);rows.append(dict(path=n,bytes=len(b),sha256=sha(b)))
 (d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes());(d/'source-diffs.json').write_text(json.dumps(diffs,indent=2)+'\n',encoding='utf8');j=dict(files=rows,manifest_sha256=sha(raw),source_headers_preserved=True,imports_namespace_end_boundaries_preserved=True,checks_byte_identical=True,source_scope=5,compiler_invoked=False,accepted=False)
 (d/'index.json').write_text(json.dumps(j,indent=2)+'\n',encoding='utf8');print(json.dumps(dict(index_sha256=sha((d/'index.json').read_bytes()),manifest_sha256=sha(raw))))
if __name__=='__main__':main()
