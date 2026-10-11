"""Exact declaration parser check for the routine restricted-adjoint repair."""
import re
from full114_gl_repair_structure_v1 import declarations
def validate(old,new):
 before,after=declarations(old),declarations(new)
 assert len(before)==8 and list(before)==list(after)
 assert before==after,'Existing public declaration header changed'
 for pattern in (rb'^import .+$',rb'^set_option .+$'):
  assert re.findall(pattern,old,re.M)==re.findall(pattern,new,re.M)
 assert old.count(b'\r\n')>0 and new.count(b'\r\n')>0
 assert old.decode('utf-8') and new.decode('utf-8')
 assert not new.startswith(bytes.fromhex('efbbbf'))
 return dict(declarations=8,headers_imports_options_exact=True,heartbeat_default_preserved=True,source_line_endings_preserved=True)
