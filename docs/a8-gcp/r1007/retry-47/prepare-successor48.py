"""Prepare same full seven-stage harness for exact owned successors, Python only."""
from pathlib import Path
import ast,shutil
p=Path(__file__).resolve().parent; target=p.parent/'retry-48'; target.mkdir()
for name in ['controller.py','finish-native.py','associate-offer.py','check-authorized-preservation.py','compare-native.py','full-original-a8-native-gates.py','pin-current-axiom-owners.py','register-captured-successors.py']:
    text=(p/name).read_text(encoding='utf-8').replace('retry-47','retry-48').replace('integrated47_import','integrated48_import').replace('finish47_import','finish48_import').replace('capture-integrated-47','capture-integrated-48')
    ast.parse(text); (target/name).write_bytes(text.encode('utf-8'))
for name in ['accepted-a9-dependency.json','accepted-a9-source.lean.snapshot','axiom-declaration-owner-map.json','author-report.md']:
    shutil.copyfile(p/name,target/name)
print('Same215/14/49 seven-stage48 prepared, Python syntax only')
