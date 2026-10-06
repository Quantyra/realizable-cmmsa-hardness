"""Add bounded GCP A11 profiling before unchanged standard certification gates."""
from pathlib import Path
import ast,shutil
p=Path(__file__).resolve().parent; target=p.parent/'retry-49'; target.mkdir()
for name in ['controller.py','finish-native.py','associate-offer.py','check-authorized-preservation.py','compare-native.py','full-original-a8-native-gates.py','pin-current-axiom-owners.py','register-captured-successors.py']:
    text=(p/name).read_text(encoding='utf-8').replace('retry-48','retry-49').replace('integrated48_import','integrated49_import').replace('finish48_import','finish49_import').replace('capture-integrated-48','capture-integrated-49')
    if name=='controller.py':
        text=text.replace("{'index':4,'name':'original-weighted-A11-A7-source'", "{'index':4,'name':'bounded-A11-native-profiling','argv':['lake','env','lean','--profile',SOURCE]},\n        {'index':5,'name':'original-weighted-A11-A7-source'")
        text=text.replace("{'index':5,'name':'original-weighted-A11-A7-checks'", "{'index':6,'name':'original-weighted-A11-A7-checks'")
        text=text.replace("{'index':6,'name':'fresh-all49-integrated-axioms'", "{'index':7,'name':'fresh-all49-integrated-axioms'")
    if name=='finish-native.py':
        text=text.replace("for i in range(7):", "for i in range(8):").replace('axiom_profiles(alltext[6])','axiom_profiles(alltext[7])')
    ast.parse(text); (target/name).write_bytes(text.encode('utf-8'))
for name in ['accepted-a9-dependency.json','accepted-a9-source.lean.snapshot','axiom-declaration-owner-map.json']:
    shutil.copyfile(p/name,target/name)
(target/'author-report.md').write_bytes(b'Full original215-source/14-owned/all49-request scope retained. Eight stages: originalA8 gates0-3, bounded900s GCP A11 --profile diagnostic stage4, standard fullA11 source5 and Checks6, original fresh49 gate7. Profiling supplies no acceptance, writes no object output, and cannot substitute for standard source/Checks/axiom gates. Compiler help verified --profile; existing70min resource hardstop, custody, cache400, inherited state and ownedwarning gates unchanged. No local Lean compilation.\n')
print('Prepared fullscope49 bounded profiling+standard gates, Python AST only')
