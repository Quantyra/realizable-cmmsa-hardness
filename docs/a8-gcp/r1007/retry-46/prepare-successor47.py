"""Prepare identical full seven-stage successor harness; Python only."""
from pathlib import Path
import ast,shutil
p=Path(__file__).resolve().parent; target=p.parent/'retry-47'
target.mkdir()
for name in ['controller.py','finish-native.py','associate-offer.py','check-authorized-preservation.py','compare-native.py','full-original-a8-native-gates.py','pin-current-axiom-owners.py','register-captured-successors.py']:
    text=(p/name).read_text(encoding='utf-8').replace('retry-46','retry-47').replace('integrated46_import','integrated47_import').replace('finish46_import','finish47_import').replace('capture-integrated-46','capture-integrated-47')
    ast.parse(text); (target/name).write_bytes(text.encode('utf-8'))
for name in ['accepted-a9-dependency.json','accepted-a9-source.lean.snapshot','axiom-declaration-owner-map.json','author-report.md']:
    shutil.copyfile(p/name,target/name)
print('Prepared same215/14/49 seven-stage47; no compilation or launch')
