from pathlib import Path
import json,hashlib,ast,subprocess
H=Path(__file__).resolve().parent
def main():
 record=json.loads((H/'full120-control-derivation-v1.json').read_bytes());repo=H.parents[2];prefix=H.relative_to(repo).as_posix()+'/'
 for r in record['records']:
  raw=(H/'full120-control-derivation-record-v1'/(r['source']+'.snapshot')).read_bytes();assert hashlib.sha256(raw).hexdigest().upper()==r['source_sha256'];assert raw==(H/r['source']).read_bytes();assert raw==subprocess.check_output(['git','cat-file','blob',record['source_base_git_head']+':'+prefix+r['source']],cwd=repo)
  text=raw.decode().replace('full119','full120').replace('Full119','Full120').replace('repair9','warning-cleanup').replace('prepare_builder02_full120','prepare_builder02_full120_v2').replace('full120_authorized16_nested_custody_v3','full119_authorized16_nested_custody_v3').replace('full120_pending16_nested_custody_v2','full119_pending16_nested_custody_v2')
  if r['source']=='validate_full119_execution_controls_v1.py':text=text.replace('full120_rank_gram_structure_v1.py','capture_full120_warning_cleanup_v2.py').replace('import full115_cumulative_actual_receipts_v1 as a','import full119_authorized16_nested_custody_v3 as a')
  b=text.encode();ast.parse(b);assert b==(H/r['target']).read_bytes() and hashlib.sha256(b).hexdigest().upper()==r['target_sha256']
 print(json.dumps(dict(controls=len(record['records']),exact_literal_derivations_verified=True,compiler_invoked=False,cloud_operation=False)))
if __name__=='__main__':main()
