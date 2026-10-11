"""Full lexical preflight and derived requests after preserved partial failure."""
import hashlib,json,re
from pathlib import Path
H=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest().upper()
def main():
 p=H/'complete-numeric-source-only-inventory-v9.json';i=json.loads(p.read_bytes());rows=[]
 for r in i['selected_sources']:
  b=Path(r['captured_source']).read_bytes();t=b.decode('utf-8')
  assert not b.startswith(bytes.fromhex('efbbbf'))
  assert not re.search(r'\b(sorry|admit)\b|(?m:^\s*axiom\s)',t)
  assert sha(b)==r['sha256']
  rows.append(dict(path=r['path'],sha256=r['sha256'],utf8_without_bom=True,no_placeholder_or_new_axiom=True))
 assert len(rows)==i['selected_source_count']
 d=H/'numeric-full-closure-checks-inventory-v9-successor-v2';d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text\n')
 imports=sorted({r['path'].removeprefix('lean/').removesuffix('.lean').replace('/','.') for r in i['selected_sources'] if not r['path'].endswith('Checks.lean')})
 body='\n'.join('import '+x for x in imports)+'\n\n'+'\n'.join('#print axioms '+x for x in i['additional_requests'])+'\n'
 (d/'Checks.lean').write_bytes(body.encode());(d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
 result=dict(inventory_sha256=sha(p.read_bytes()),selected_sources=rows,selected_source_count=len(rows),additional_request_count=len(i['additional_requests']),checks_sha256=sha(body.encode()),source_only=True,compiler_invoked=False,accepted=False,observations=['Original direct tool6dd680 indentation mistake created checks-v9/index with only1 lexical source verified; second loop iteration raised FileExistsError. Original partial folder retained unchanged. This disjoint successor validates every selected source before writing.'])
 (d/'index.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8');print(json.dumps(dict(sources=len(rows),requests=len(i['additional_requests']),checks_sha256=result['checks_sha256'])))
if __name__=='__main__':main()
