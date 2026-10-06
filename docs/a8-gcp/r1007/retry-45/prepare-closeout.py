"""Prepare scoped recovery closeout scripts without staging or compilation."""
from pathlib import Path
import ast
p=Path(__file__).resolve().parent.parent
s=(p/'retry-44/stage-current-preservation.py').read_text(encoding='utf-8')
s=s.replace("roots=['retry-44','captures/capture-integrated-44','runs/cmmsa_a8_output_20261006T021553Z_24b467f2']", "roots=['retry-45','captures/capture-integrated-45','runs/cmmsa_a8_output_20261006T023135Z_1fc1ec5c']")
s=s.replace("offers=['successor-native-44-endpoint-repair']", "offers=['successor-native-45-a11-first-repair','successor-native-45-a11-second-repair','successor-native-45-a11-coherent-repair','successor-native-45-a11-coherent-recovery']")
s=s.replace("+['retry-45']", "+['retry-46']").replace('retry-44/current-stage-pathspec.nul','retry-45/current-stage-pathspec.nul')
ast.parse(s); (p/'retry-45/stage-current-preservation.py').write_bytes(s.encode('utf-8'))
s=(p/'retry-45/check-authorized-preservation.py').read_text(encoding='utf-8')
s=s.replace("json.loads((run/'terminal.json').read_bytes())['inherited_dirt_preserved']", "None")
s=s.replace("'raw_red_audit_preserved':True", "'raw_red_audit_preserved':True,'raw_terminal_zero_bytes_preserved':True,'raw_flag_unavailable_due_disk_full':True")
ast.parse(s); (p/'retry-45/check-recovered-preservation.py').write_bytes(s.encode('utf-8'))
