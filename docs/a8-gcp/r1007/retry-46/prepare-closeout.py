"""Prepare focused current-turn stage scope; no Git writes or compilation."""
from pathlib import Path
import ast
p=Path(__file__).resolve().parent.parent
s=(p/'retry-45/stage-current-preservation.py').read_text(encoding='utf-8')
s=s.replace("roots=['retry-45','captures/capture-integrated-45','runs/cmmsa_a8_output_20261006T023135Z_1fc1ec5c']", "roots=['retry-46','captures/capture-integrated-46','runs/cmmsa_a8_output_20261006T030313Z_2f112c58']")
s=s.replace("offers=['successor-native-45-a11-first-repair','successor-native-45-a11-second-repair','successor-native-45-a11-coherent-repair','successor-native-45-a11-coherent-recovery']", "offers=['successor-native-46-a11-repair']")
s=s.replace("+['retry-46']", "+['retry-47']").replace('retry-45/current-stage-pathspec.nul','retry-46/current-stage-pathspec.nul')
ast.parse(s); (p/'retry-46/stage-current-preservation.py').write_bytes(s.encode('utf-8'))
sh=(p/'retry-45/verify-staged-parity.py').read_bytes(); (p/'retry-46/verify-staged-parity.py').write_bytes(sh)
