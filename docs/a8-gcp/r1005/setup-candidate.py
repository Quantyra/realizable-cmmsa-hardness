"""Offline r1004 harness adaptation for the exact Luna candidate; no compiler calls."""
from pathlib import Path
import hashlib, json, shutil, re, unicodedata

PACKAGE = Path(__file__).resolve().parent
REPO = PACKAGE.parents[2]
PRIOR = PACKAGE.with_name('r1004')
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest().upper()
for p in PRIOR.iterdir():
    if p.name in {'common.py', 'prepare.py', 'runner.py', 'audit.py', 'cloud_capture.py',
                  'validate.py', 'preserve-incomplete.py', 'remote-template.sh', 'README.md',
                  '.gitattributes', '.gitignore', 'prospective-audit.py', 'observe.py',
                  'closeout.py', 'deliver.py', 'setup.py', 'workflow-protocol.snapshot',
                  'warning-baseline-seal.json', 'static-inspection.json'}:
        shutil.copyfile(p, PACKAGE / p.name)
shutil.copytree(PRIOR / 'warning-baseline', PACKAGE / 'warning-baseline')
routes = PACKAGE / 'author-route'
routes.mkdir()
for name in ['a8-domain-square-sol.md', 'a8-domain-square-luna-final.md']:
    shutil.copyfile(Path('C:/a8reviews') / name, routes / name)
luna = routes / 'a8-domain-square-luna-final.md'
assert digest(luna) == '2EDFA351E99DC145B9F917F486E93871522E37258940872376E150D537BCC5FE'
assert not any(unicodedata.category(c) == 'Cf' for c in luna.read_text(encoding='utf-8'))
for name in ['three-lens-closeout.md', 'completion-report.md']:
    shutil.copyfile(PRIOR / name, routes / ('r1004-' + name))
source = 'lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A8OutputCoordinateTransport.lean'
checks = 'lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A8OutputCoordinateTransportChecks.lean'
report = 'docs/a8-gcp/r1005/statement-fidelity.md'
(REPO / report).write_text('Luna exact authored two-file patch, artifact SHA256 '+digest(luna)+'.\n'
    'Theorem semantics and proof unchanged. Sole added import: ActualBinaryMatrixHC46A9AmbientFiber.\n'
    'Compiler repair: import exposure only; zero helper/roadmap credit. BinaryMatrixA1NestedCarrier already transitive.\n'
    'Development candidate 2, unaccepted. Accepted helper count 1; retries zero; threshold not crossed.\n'
    'S3132 PARTIAL; analytic A8 OPEN; S3137 INCOMPLETE. Three-lens closeout required before acceptance/commit.\n', encoding='utf-8')
p = PACKAGE / 'common.py'
s = p.read_text(encoding='utf-8')
s = re.sub(r'^REPORT = .*$', 'REPORT = '+repr(report), s, flags=re.M)
s = re.sub(r'^FROZEN = .*$', 'FROZEN = '+repr({rel:digest(REPO / rel) for rel in [source,checks,report]}), s, flags=re.M)
s = s.replace("'a8_output_pair_component_nested_mean']]", "'a8_output_pair_component_nested_mean', 'a8_w6_domain_quotient_square']]")
s = re.sub(r'^CLAIM = .*$', "CLAIM = "+repr('Exact Luna domain quotient square, development candidate 2; unaccepted pending green GCP evidence and three-lens closeout. Accepted helper count 1; compiler/import repairs zero credit; threshold not crossed. S3132 partial / analytic A8 open; S3137 incomplete.'), s, flags=re.M)
p.write_text(s, encoding='utf-8')
p = PACKAGE / 'prepare.py'
s = p.read_text(encoding='utf-8')
s = s.replace('"statement-fidelity.md"]', '"statement-fidelity.md", "setup-candidate.py"]')
s = s.replace('    save("status-before.txt",', '    for route in sorted((PACKAGE / "author-route").iterdir()):\n        save("author-route/" + route.name, route.read_bytes())\n\n    save("status-before.txt",')
s = s.replace('"PvNP.RealizableHardness.ActualBinaryMatrixHC46A7Transfer"]}', '"PvNP.RealizableHardness.ActualBinaryMatrixHC46A7Transfer",\n            "PvNP.RealizableHardness.ActualBinaryMatrixHC46A9AmbientFiber"]}')
s = s.replace('This audit requires zero warnings in all new stages; no warning suppression is added.', 'Legacy audit stays zero-total RED; prospective audit compares frozen warning headers; no suppression.')
p.write_text(s, encoding='utf-8')
print(json.dumps({'frozen_candidate':{rel:digest(REPO / rel) for rel in [source,checks,report]}, 'local_compilation':False}, indent=2))
