"""Derive a no-start stage successor with exact completed-parent custody."""
import ast,json
from pathlib import Path
from custody_checks import digest
H=Path(__file__).resolve().parent
def main():
 s=H/'stage_full116_openssh_v2.py';text=s.read_text()
 text=text.replace('full116','full117').replace('Full116','Full117')
 substitutions={
 'full115-exact-real-complex-operators-repair5-resource02':'full116-exact-real-complex-operators-repair6-resource02',
 '20261011T201255199859Z':'20261011T212845260237Z',
 '9495001F3BA6C4194E4DB4BB8563BE399E48FD8D7CDED513395EEF16021C612A':'D6903AB914994BDB6B7C7750D8956C06611CBFE7ACDAEA8E96058DD2F1B1EB2C',
 'full115-native-final-custody-v1':'full116-native-final-custody-v1',
 '8BB7BD5C36A62CBBC0CE1C96787EDF487B53276F78D775BC1E8D34B142344B1D':'7C3B8FC2E4F2CC8D42295712BCE8968B54606C452A867BE05F75EB438B1B5519',
 'cmmsa_a8_output_20261011T201326Z_31fcd86a':'cmmsa_a8_output_20261011T212933Z_f9a386c2',
 "digest(here/'stage_full117_openssh_v1.py')":"digest(here/'start_inspect_full117_owned_capacity_v2.py')",
 }
 for old,new in substitutions.items():assert old in text,old;text=text.replace(old,new)
 old="    assert digest(here/'full117-staging-capacity-failure-record-v1/complete-originals.tar.gz')=='587B9CACCDA3C380546D502D42DC7573C25E615B10156EDE48C0620841E1807E'"
 assert old in text
 text=text.replace(old,"    from start_inspect_full117_owned_capacity_v2 import verify_cleanup_receipt\n    verify_cleanup_receipt()\n    assert digest(here/'full117-owned-capacity-inspection-record-v1/index.json')=='BB3EDE3E20F8EC86CC8C5A4E69001465FDEC03AE5F0281E26F064B515CABFA5F'")
 ast.parse(text);p=H/'stage_full117_openssh_v1.py';p.open('x',encoding='utf-8',newline='').write(text)
 r=dict(source=str(s),source_sha256=digest(s),target=str(p),target_sha256=digest(p),substitutions=substitutions,compiler_invoked=False,cloud_operation=False,VM_start_performed=False)
 (H/'full117-openssh-stage-derivation-v1.json').open('x').write(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
if __name__=='__main__':main()
