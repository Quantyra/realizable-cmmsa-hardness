"""One proof-line replacement only; every original header/import/option remains exact."""
import hashlib,re
from full114_gl_repair_structure_v1 import declarations
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
def validate(old,new):
 assert sha(old)=='FF8981B60487A904F74F58903636FC7501E804247D5FDF45A8B9737F9246E06D'
 assert sha(new)=='5D27B30545FFF4E73A042F6CBE3D379BF5D21AC5D1B79B9314CF41333987CA7F'
 before=b'    simp [hi, hj]\n';after=b'    simp only [if_pos hi, if_neg hj, mul_zero]\n'
 assert new.count(after)==1 and new.replace(after,before,1)==old
 a,b=declarations(old),declarations(new);assert len(a)==11 and a==b
 for pattern in [rb'^import .+$',rb'^set_option .+$']:assert re.findall(pattern,old,re.M)==re.findall(pattern,new,re.M)
 new.decode('utf-8');assert not new.startswith(bytes.fromhex('efbbbf'))
 return dict(declarations=11,headers_imports_options_exact=True,heartbeat_default_preserved=True,exact_one_proof_line_changed=True)
