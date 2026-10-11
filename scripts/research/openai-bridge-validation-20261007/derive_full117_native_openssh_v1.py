"""Exact transport successor; unchanged controller, resources and public scope."""
import ast,json
from pathlib import Path
from custody_checks import digest
H=Path(__file__).resolve().parent
def main():
 rows=[]
 for name in ('full116_openssh_control_v1.py','run_full116_native_openssh_v1.py','terminate_full116_after_custody_openssh_v1.py'):
  s=H/name;text=s.read_text().replace('full116','full117').replace('Full116','Full117')
  if name.startswith('run_'):
   text=text.replace('20261011T203824098617Z','20261011T220141729530Z').replace('D62820D741E64017093E3CED9ADBE47EE3D3D7DF09679DCE9860C165C891AE10','9A9C7210438CB043D089FC89C5984C9D325C627FFE6BAB62F458BBF9B3276C6C')
  ast.parse(text);p=H/name.replace('full116','full117');p.open('x',encoding='utf-8',newline='').write(text)
  rows.append(dict(source=name,source_sha256=digest(s),target=p.name,target_sha256=digest(p)))
 (H/'full117-native-openssh-derivation-v1.json').open('x').write(json.dumps(dict(records=rows,compiler_invoked=False,cloud_operation=False),indent=2)+'\n');print(json.dumps(rows))
if __name__=='__main__':main()
