"""Inspect downloaded GCP receipts only. No local Lean execution."""
from pathlib import Path
import hashlib,json,re,sys,tarfile
out=Path(__file__).resolve().parent
root=out.parents[2]
tag=sys.argv[1]; base=out/tag; receipt=base/'remote-evidence'
receipt.mkdir(exist_ok=True)
with tarfile.open(base/(tag+'-evidence.tar.gz')) as t: t.extractall(receipt,filter='data')
prep=json.loads((base/'preparation.json').read_bytes())
manifest=json.loads((out/'manifest.json').read_bytes())
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
assert sha((base/(tag+'.tar.gz')).read_bytes()) == prep['archive_sha'].upper()
def pins(path):
    return {line.split(None,1)[1].strip():line.split()[0].upper() for line in path.read_text().splitlines()}
before=pins(receipt/'source-before.sha256'); after=pins(receipt/'source-after.sha256')
expected={p:h.upper() for p,h in prep['overlay_pins'].items()}
assert all(before.get(p)==h and after.get(p)==h for p,h in expected.items()),'source custody'
assert all(before[p]==manifest['config'][p]['archive_sha256'] for p in ['lake-manifest.json','lean-toolchain'])
objects=pins(receipt/'object-after.sha256')
assert all('.lake/build/lib/lean/'+p.removeprefix('lean/').removesuffix('.lean')+'.olean' in objects for p in expected),'missing captured object'
all_dependency_sources=[]
for prefix in ['package','core']:
    hashes=json.loads((receipt/(prefix+'-source-hashes.json')).read_bytes())
    with tarfile.open(receipt/(prefix+'-sources.tar.gz')) as t:
        for p,h in hashes.items(): assert sha(t.extractfile(p).read())==h.upper(),p
    assert hashes, 'empty '+prefix+' source capture'
    all_dependency_sources.extend(hashes)
assert all(any(p.endswith('/'+n.replace('.','/')+'.lean') for p in all_dependency_sources)
    for n in manifest['external_imports']), 'uncaptured external import'
packages=json.loads((receipt/'package-identities.json').read_bytes())
lean_identity=(receipt/'toolchain.txt').read_text().strip()
assert 'version 4.34.0-rc2' in lean_identity and '6a10ac8c22beadecabdbb0919c2b50214762f91d' in lean_identity
config=json.loads((out/'inputs/lake-manifest.json').read_bytes())
assert all(packages[p['name']]==p['rev'] for p in config['packages']), 'package revision drift'
exits={str(i):int((receipt/f'stage-{i}.native-exit').read_text()) for i in [0,1]}
native=int((receipt/'native-exit').read_text()); aggregate=int((receipt/'aggregate.native-exit').read_text())
logs=(receipt/'stage-1.stdout').read_text(encoding='utf-8')
name='PvNP.RealizableHardness.ActualBinaryMatrixHC46A9FiberCount.a9_fixed_final_graph_census'
profiles=dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",logs))
assert name in profiles,'missing theorem axiom profile'
axioms=[a.strip() for a in profiles[name].split(',') if a.strip()]
assert not set(axioms)-{'propext','Classical.choice','Quot.sound'},axioms
assert 'theorem '+name in logs, 'missing #print theorem'
assert name in logs,'missing #check'
assert exits=={'0':0,'1':0} and native==aggregate==0,'nonzero compiler exit'
runtime=base/(tag+'-local-runtime')
commands=json.loads((runtime/'commands.json').read_bytes())
assert commands[-1]['native_exit_code']==0
assert (runtime/(str(len(commands)-1)+'.stdout')).read_bytes().strip()==b'TERMINATED','VM terminal state'
for p,h in manifest['offer'].items(): assert sha((root/p).read_bytes())==h,'offered file drift'
summary={'run':tag,'green':True,'source_sha256':expected['lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A9FiberCount.lean'],
    'archive_sha256':prep['archive_sha'].upper(),'project_modules':len(expected)-1,'check_modules':1,
    'stage_exits':exits,'native_exit':native,'aggregate_exit':aggregate,'axioms':axioms,
    'vm_terminal_state':'TERMINATED','package_identities':packages,
    'lean_identity':lean_identity,'local_compilation':False}
(out/'audit.json').write_text(json.dumps(summary,indent=2))
report=f'''A9 abstract graph-datum census: exact-source GCP compiler receipt

Initial immutable offers were verified and acknowledged before any successor edit:
source SHA256 {summary['source_sha256']}
author report SHA256 {manifest['offer']['docs/a7-certification-20261003/a9-author-report.md']}
Both offered files remain unchanged. No theorem repair, weakening, axiom or sorry added.
Git normalizes the published Markdown report to LF; the exact offered author-report
bytes are preserved separately in a9-gcp/author-report.md.snapshot (same offered hash).

GCP project quantyra-lean-cert-20260915; zone us-central1-a;
VM quantyra-lean-builder-01; authoritative run {tag}.
Input archive SHA256 {summary['archive_sha256']}
Fresh source workspace /home/dfredriksen_quantyra_org/{tag}.
Full recursive project closure: {len(expected)-1} source modules plus one capture-only check module.
All captured project .olean variants invalidated before rebuilding.
Captured before/after source hashes agree for every module; all resulting objects present.
Warm cache reused only for packages/build artifacts; project source bytes came from the
immutable archive. Package revisions match lake-manifest.json; changed tracked Lean
files were checked against revision contents after line-ending normalization. Package
line-ending/configuration/mode differences are retained as exact patches. Full package and core
source archives/hashes and cached object hashes retained.
Git-normalized configuration bytes match captured configurations after CRLF normalization;
both configuration identities retained in a9-gcp/manifest.json.

Lean: {summary['lean_identity']}
cslib: {packages['cslib']}
Source compile exit: {exits['0']}; #check/#print/axiom check exit: {exits['1']}.
Aggregate/native remote-shell exits: {aggregate}/{native}.
Theorem: {name}
Axiom profile: {', '.join(axioms)}. No nonstandard axioms or sorryAx observed.
Authoritative final VM state: TERMINATED, confirmed by the GCP describe receipt.
No local Lean/Lake command was executed.

Preservation: all immutable inputs, executed scripts, raw stdout/stderr, per-stage/native
exit receipts, package/core identities, source/object hashes, and GCP lifecycle/control
receipts are under a9-gcp/. The failed custody attempt cmmsa_analytic_20261004T001054Z
is retained: unrelated warm A7 bytes differed from the Git archive; no Lean invocation
occurred. Its stop API returned 502; subsequent observations confirmed TERMINATED.
Attempt cmmsa_analytic_20261004T001608Z passed project source custody but stopped on
an overly broad package-tree cleanliness gate before the compile stages. Its raw
receipt is preserved. The final gate verifies Lean source contents and preserves
package differences explicitly. These failures were infrastructure, not theorem failures.
Attempt cmmsa_analytic_20261004T002118Z stopped before Lean because of an escaping
error in the package-capture Python block. The raw failure is retained; the final
runner parses its emitted Python blocks locally before uploading, without running Lean.
Extracted package/core source archives are ignored duplicate copies: their exact bytes
are preserved inside the tracked native evidence archive. The evidence inventory lists
their hashes, and extracting that archive reconstructs them without using a warm workspace.

Certification scope: the abstract A9InitialDatum Gaussian-graph cardinality and
rank preservation for a9InitialMap. The captured closure includes inherited source
work preserved unchanged; only the owned A9 source/reports/evidence are Git-owned here.

Still open: actual fixed-final predecessor-fiber equivalence (both directions, final
datum preservation and unique reconstruction), A8 induction/T2 analytic bound,
analytic A9 finite-sum reindexing, A11 aggregate charge, positive-share discharge,
and the positive-degree manuscript theorem. The graph census does not discharge them.

Development verification only; no planning story or route-final acceptance closed.
| Lens | Verdict | Scope |
| Build/axiom audit | GO | Exact offered A9 source and captured closure |
| Proof-adversarial | INCOMPLETE | Route-final review debt |
| Complexity | INCOMPLETE | Route-final review debt |
| Non-claims | INCOMPLETE | Route-final review debt |
Required Claude Opus 5.5 and Gemini 3.1 Pro High reviews remain route-final debt.
'''
(out.parent/'a9-gcp-report.txt').write_text(report,encoding='utf-8')
inventory={str(p.relative_to(out)):sha(p.read_bytes()) for p in out.rglob('*') if p.is_file() and p.name!='evidence-hashes.json'}
(out/'evidence-hashes.json').write_text(json.dumps(inventory,indent=2))
print(json.dumps(summary,indent=2))
