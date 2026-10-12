from pathlib import Path
import hashlib,json,re,difflib
H=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
def boundaries(text):return [line for line in text.splitlines() if re.match(r'^\s*(import|namespace|end)\b',line)]
def headers(text):
 starts=list(re.finditer(r'(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|public)\s+)*(?:theorem|lemma|def|abbrev)\s+\w+\b',text));return [text[a.start():text.find(':=',a.start())].strip() for a in starts]
def main():
 s=H/'full120-warning-cleanup-offer-v1';raw=(s/'manifest.json').read_bytes();m=json.loads(raw);assert sha((H/m['warning_packet']).read_bytes())==m['warning_packet_index_sha256'];data={'manifest.json':raw};diffs={}
 for r in m['source_files']:
  b=(s/'lean/PvNP/RealizableHardness'/r['path']).read_bytes();old=(H/'full119-review-source-capsule-v1/lean/PvNP/RealizableHardness'/r['path']).read_bytes();assert sha(b)==r['successor_sha256'] and len(b)==r['successor_bytes'] and sha(old)==r['original_sha256'];a=old.decode('utf8');z=b.decode('utf8');assert boundaries(a)==boundaries(z) and headers(a)==headers(z);assert not b.startswith(bytes.fromhex('efbbbf'));data[r['path']]=b;diffs[r['path']]=''.join(difflib.unified_diff(a.splitlines(keepends=True),z.splitlines(keepends=True),fromfile='Full119/'+r['path'],tofile='Full120/'+r['path']))
 for n,pin in m['checks_sha256'].items():
  b=(s/'lean/PvNP/RealizableHardness'/n).read_bytes();assert sha(b)==pin and b==(H/'full119-review-source-capsule-v1/lean/PvNP/RealizableHardness'/n).read_bytes();data[n]=b
 b=(s/'ARGUMENT.md').read_bytes();assert sha(b)==m['argument_sha256'] and len(b)==m['argument_bytes'];data['ARGUMENT.md']=b
 d=H/'full120-warning-cleanup-capture-v1';d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n');rows=[]
 for n,b in data.items():(d/n).write_bytes(b);rows.append(dict(path=n,bytes=len(b),sha256=sha(b)))
 (d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes());(d/'source-diffs.json').write_text(json.dumps(diffs,indent=2)+'\n',encoding='utf8');j=dict(files=rows,manifest_sha256=sha(raw),source_headers_preserved=True,imports_namespace_end_boundaries_preserved=True,checks_byte_identical=True,source_scope=5,compiler_invoked=False,accepted=False)
 (d/'index.json').write_text(json.dumps(j,indent=2)+'\n',encoding='utf8');print(json.dumps(dict(index_sha256=sha((d/'index.json').read_bytes()),manifest_sha256=sha(raw))))
if __name__=='__main__':main()
