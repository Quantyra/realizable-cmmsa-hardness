"""Preserve prior executed harness; prepare same full original candidate successor."""
from pathlib import Path
import ast,shutil
HERE=Path(__file__).resolve().parent; PACKAGE=HERE.parent
t=(PACKAGE/'retry-21/controller.py').read_text(encoding='utf-8').replace('integrated21_import','integrated22_import').replace('capture-integrated-21','capture-integrated-22').replace('retry-21/','retry-22/').replace('prepare21','prepare22')
ast.parse(t); (HERE/'controller.py').write_bytes(t.encode()); (HERE/'control').mkdir()
for n in ['accepted-a9-source.lean.snapshot','accepted-a9-dependency.json']:
    shutil.copyfile(PACKAGE/'retry-21'/n,HERE/n)
(HERE/'author-report.md').write_bytes(b'# Full original A8 and A11/A7 native successor\n\nExact native21 API repairs ED94F463/49C3548D reindex normalized sums on actual Finset univs and reduce exact denominators to Nat.card_congr. No mathematical statement, mean, carrier or premise changes. Same054/F981 original A11/A7 consumer, full fourteen owned modules and49 fresh axiom requests. AcceptedA9 exact5B4958 rebuilt after own lib/ir invalidation; all400 unchanged cached dependency objects tracked. Strict decoded archive lengths and full remote/short/repository SHA custody, nonzero raw transport receipts preserved separately. No local Lean or helper acceptance.\n')
