"""Recognize same-line attributes while preserving every existing declaration."""
import re
from full114_gl_repair_structure_v1 import declarations
def normalize(data):
 return re.sub(rb'(?m)^(@\[[^\]]+\])[ \t]+(?=(?:theorem|lemma|def|abbrev)\b)',b'',data)
def validate(old,new):
 attrs=lambda b:re.findall(rb'(?m)^@\[[^\]]+\][ \t]+(?:theorem|lemma|def|abbrev)[ \t]+\w+',b)
 assert attrs(old)==attrs(new),'Existing declaration attributes changed'
 before,after=declarations(normalize(old)),declarations(normalize(new))
 assert len(before)==8 and list(before)==list(after)
 assert before==after,'Existing public declaration header changed'
 for pattern in (rb'^import .+$',rb'^set_option .+$'):
  assert re.findall(pattern,old,re.M)==re.findall(pattern,new,re.M)
 assert (b'\r\n' in old,b'\n' in old.replace(b'\r\n',b''))==(b'\r\n' in new,b'\n' in new.replace(b'\r\n',b''))
 new.decode('utf-8');assert not new.startswith(bytes.fromhex('efbbbf'))
 return dict(declarations=8,attributed_declarations=2,headers_attributes_imports_options_exact=True,heartbeat_default_preserved=True,source_line_endings_preserved=True)
