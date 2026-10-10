"""Prepare contingent full-scope trace derivation; no execution before qualification."""
from pathlib import Path
import ast
import hashlib
import json
here=Path(__file__).parent
source=here/'derive_full108_consumption_controls.py'
text=source.read_text().replace('full108','full109').replace('Full108','Full109')
text=text.replace('full109-exact-crosslevel-product','full109-exact-crosslevel-warning-repair')
text=text.replace('from prepare_full109_crosslevel_product_scope import additions as SPECTRAL_ADDITIONS',
                  'from prepare_full108_crosslevel_product_scope import additions as SPECTRAL_ADDITIONS')
assert 'from prepare_builder02_full109 import OUTPUT' in text
assert 'from prepare_full108_crosslevel_product_scope import additions as SPECTRAL_ADDITIONS' in text
assert "qualified['full109_expanded_native_gates_green']" in text
ast.parse(text)
target=here/'derive_full109_consumption_controls.py'
with target.open('x',encoding='utf-8',newline='\n') as stream:stream.write(text)
record=dict(source_sha256=hashlib.sha256(source.read_bytes()).hexdigest().upper(),
 target_sha256=hashlib.sha256(target.read_bytes()).hexdigest().upper(),
 contingent_only=True,actual_qualified_custody_required=True,
 controls_not_derived=True,project_sources=348,requested_roots=261,focused_consumers=93,
 compiler_invoked=False,probe_executed=False,accepted=False)
(here/'full109-consumption-deriver-preparation.json').open('x').write(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
