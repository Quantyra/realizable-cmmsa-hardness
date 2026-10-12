"""Read-only source inspection; this is not a Lean elaboration check."""
from pathlib import Path
import hashlib, json, re, sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
from lean_source_static_preflight_v1 import code_only
S = Path(__file__).resolve().parent
inventory = S/'complete-numeric-source-only-inventory-v18.json'
raw = inventory.read_bytes()
data = json.loads(raw)
sha = lambda b: hashlib.sha256(b).hexdigest().upper()
findings = []
for row in data['selected_sources']:
    path = Path(row['captured_source'])
    source = path.read_bytes()
    assert sha(source) == row['sha256']
    code = code_only(source.decode('utf-8'))
    opened = set()
    for line in re.findall(r'(?m)^open (?!scoped )([^\n]+)', code):
        opened.update(line.split())
    missing = []
    for name, namespace in [('decay', 'DropTailParameters'), ('qdecay', 'ZoomOutPosterior')]:
        uses = re.findall(r'(?<![\w.])'+name+r'(?![\w])', code)
        if uses and namespace not in opened and not any(x.endswith('.'+namespace) for x in opened):
            missing.append(dict(name=name, namespace=namespace, unqualified_occurrences=len(uses)))
    if missing:
        findings.append(dict(path=row['path'], captured_source=str(path), sha256=row['sha256'],
            capture=row['capture'], capture_index_sha256=row['capture_index_sha256'], missing=missing))
out = S/'numeric-decay-namespace-inspection-v1'
out.mkdir(exist_ok=False)
report = dict(schema=out.name, read_only=True, compiler_invoked=False, accepted=False,
    inventory=str(inventory), inventory_sha256=sha(raw), inspected_sources=len(data['selected_sources']),
    declaration_sources={'decay':'DropTailParameters.lean:13','qdecay':'ZoomOutPosterior.lean:13'},
    alias_search='rg found no other def, abbrev or export for these symbols in the research source tree',
    limitations='Lexical missing-open inspection, not a complete namespace or elaboration audit.',
    findings=findings)
(out/'result.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(report_sha256=sha((out/'result.json').read_bytes()), findings=findings)))
