"""Disjoint exact package/gate successor with recorded bounded substitutions."""
import ast,json
from pathlib import Path
from custody_checks import digest
H=Path(__file__).resolve().parent
def main():
 rows=[]
 for name in ('prepare_builder02_full117.py','full117_capture_gates.py'):
  s=H/name;text=s.read_text().replace('full117','full118').replace('Full117','Full118').replace('repair7','repair8')
  text=text.replace('full116','full117').replace('Full116','Full117')
  changes={}
  if name.startswith('prepare_'):
   changes={
    'full118_append_block_structure_v1':'full118_restricted_adjoint_structure_v3',
    'full118-append-block-repair-capture-v1':'full118-restricted-adjoint-repair-capture-v1',
    'B0A4DD9039A353E78C4BBB6974671BC40CCDE1ABD4BB93D0CF8283B71AA03190':'92173AE12954FA6BD317ACD02FF5BDAB7BDA8EEA5EAB7B6A02ABE005D861AC22',
    'ExactAppendBlockIdentity.lean':'ExactRestrictedAdjoint.lean',
    "path = base / row['copy']":"path = base / row.get('copy', 'offered.gitattributes' if row['path']=='.gitattributes' else row['path'])",
    "assert index['existing18_declarations_preserved_after_explicit_alias_qualification']":"assert index['immutable_capture'] and not index['accepted']",
    "assert index['imports_options_checks_preserved']":"assert not index['compiler_invoked']",
    'cmmsa_a8_output_20261011T212933Z_f9a386c2':'cmmsa_a8_output_20261011T231800Z_f8f19b01',
    'append-block-proof-repair':'restricted-adjoint-proof-repair',
    'all_existing_headers_preserved_except_disclosed_alias_qualification':'all_existing_headers_preserved_exactly',
   }
   for old,new in changes.items():assert old in text,old;text=text.replace(old,new)
   text=text.replace('append block proof repair with explicit alias qualification','restricted adjoint proof repair with every header exact')
   pin=digest(H/'full117-native-final-custody-v1/index.json')
   before="    validate_successor()\n    marker ="
   assert before in text;text=text.replace(before,"    validate_successor()\n    assert digest(HERE/'full117-native-final-custody-v1/index.json')=='"+pin+"'\n    marker =")
  else:
   text=text.replace('append block proof repair with disclosed alias qualification','restricted adjoint proof repair with exact existing headers')
   text=text.replace('against every unchanged Full115 capture member','against every unchanged Full117 capture member')
  ast.parse(text);p=H/name.replace('full117','full118');p.open('x',encoding='utf-8',newline='').write(text)
  rows.append(dict(source=name,source_sha256=digest(s),target=p.name,target_sha256=digest(p),bounded_substitutions=changes))
 (H/'full118-preparation-derivation-v1.json').open('x').write(json.dumps(dict(records=rows,compiler_invoked=False,cloud_operation=False),indent=2)+'\n');print(json.dumps(rows))
if __name__=='__main__':main()
