"""Prepare exact proof/evidence/review stage enumeration without Git mutation."""
from pathlib import Path
import ast
p=Path(__file__).resolve().parent.parent
s=(p/'retry-46/stage-current-preservation.py').read_text(encoding='utf-8')
s=s.replace("roots=['retry-46','captures/capture-integrated-46','runs/cmmsa_a8_output_20261006T030313Z_2f112c58']", "roots=['retry-47','captures/capture-integrated-47','runs/cmmsa_a8_output_20261006T031832Z_31df8fff']")
s=s.replace("offers=['successor-native-46-a11-repair']", "offers=['successor-native-47-a11-repair','successor-post-a8-review-header-reconciliation']")
s=s.replace("+['retry-47']", "+['retry-48']").replace('retry-46/current-stage-pathspec.nul','retry-47/current-stage-pathspec.nul')
s=s.replace("attrs=REPO/'.gitattributes';", "review=json.loads((PACKAGE/'retry-47/completed-review-file-pins.json').read_bytes())['files']\nassert len(review)==17 and all(hashlib.sha256((REPO/n).read_bytes()).hexdigest().upper()==h for n,h in review.items())\npaths+=list(review)\nattrs=REPO/'.gitattributes';")
s=s.replace("attrs.write_bytes((text+'\\n').encode('utf-8'));", "for n in review:\n    rule=n+' -text'\n    if rule not in text: text+='\\n'+rule\nattrs.write_bytes((text+'\\n').encode('utf-8'));")
ast.parse(s); (p/'retry-47/stage-current-preservation.py').write_bytes(s.encode('utf-8'))
(p/'retry-47/verify-staged-parity.py').write_bytes((p/'retry-46/verify-staged-parity.py').read_bytes())
