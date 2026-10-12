"""Static Full119 unchanged-scope preparation; no archive/compiler/cloud writes."""
from pathlib import Path
import json,hashlib,re,tarfile
H=Path(__file__).resolve().parent
ROOT=Path('C:/Users/dfred/.quantyra/builder02/full118-exact-real-complex-operators-repair8-resource02')
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
def surface(b):
 t=b.decode('utf-8');assert not b.startswith(b'\xef\xbb\xbf')
 return dict(headers=[re.sub(r'\s+',' ',x) for x in re.findall(r'(?ms)^(?:theorem|def)\s+\w+.*?(?=\s*:=)',t)],imports=re.findall(r'(?m)^import .*',t),options=re.findall(r'(?m)^set_option .*',t))
def gate(old,new,checks_old,checks_new):
 assert surface(old)==surface(new) and checks_old==checks_new
 assert new.count(b'    simp only [if_pos hi, if_neg hj, mul_zero]')==1
 assert new.replace(b'    simp only [if_pos hi, if_neg hj, mul_zero]',b'    simp [hi, hj]',1)==old
 assert not re.search(rb'\b(?:sorry|admit|axiom)\b',new)
def main():
 d=H/'full119-source-only-scope-preparation-v1';assert not d.exists()
 m=json.loads((ROOT/'capture-manifest.json').read_bytes());assert len(m['project_sources'])==369 and len(m['requested_axioms'])==347 and len(m['stages'])==7
 assert sha((H/'full119-rank-gram-capture-v1/index.json').read_bytes())=='F8DCB3605D36D5DFB41FE9102074D57D2EB796C8572BF43C8B41BECAB63E423D'
 replacement='lean/PvNP/RealizableHardness/ExactRealRankGram.lean';new=(H/'full119-rank-gram-capture-v1/ExactRealRankGram.lean').read_bytes();checks=(H/'full119-rank-gram-capture-v1/ExactRealRankGramChecks.lean').read_bytes();sources=[]
 with tarfile.open(ROOT/'input-archive.tar.gz','r:gz') as t:
  old=t.extractfile(replacement).read();checks_old=t.extractfile(replacement.replace('.lean','Checks.lean')).read();gate(old,new,checks_old,checks)
  for name,r in m['project_sources'].items():
   b=t.extractfile(name).read();assert sha(b)==r['sha256'] and len(b)==r['bytes'];out=new if name==replacement else b;sources.append(dict(path=name,sha256=sha(out),bytes=len(out),changed=name==replacement))
 tests=[]
 for label,b,c in [('wrong public header',new.replace(b'(hij : i',b'(hij : j',1),checks),('added import',b'import Mathlib\n'+new,checks),('heartbeat changed',b'set_option maxHeartbeats 400000\n'+new,checks),('checks changed',new,checks+b'\n#check True\n'),('unapproved proof edit',new.replace(b'mul_zero]',b'mul_zero, add_zero]',1),checks)]:
  try:gate(old,b,checks_old,c)
  except AssertionError:tests.append(dict(case=label,rejected=True))
  else:raise AssertionError(label)
 d.mkdir();(d/'.gitattributes').write_bytes(b'* -text\n');(d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
 j=dict(parent_input_sha256=sha((ROOT/'input-archive.tar.gz').read_bytes()),parent_manifest_sha256=sha((ROOT/'capture-manifest.json').read_bytes()),sources=sources,source_count=369,requested_axioms=m['requested_axioms'],request_count=347,stages=m['stages'],stage_count=7,unchanged_other_sources=368,public_headers=11,checks_imports_options_unchanged=True,negative_scope_checks=tests,execution_archive_created=False,cloud_operation=False,compiler_invoked=False,accepted=False,requires_full118_terminal_stop_audit_portable_custody_and_fresh_capacity_before_execution=True)
 (d/'result.json').write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8');print(json.dumps(dict(sha256=sha((d/'result.json').read_bytes()),sources=369,requests=347,stages=7,negative_checks=len(tests))))
if __name__=='__main__':main()
