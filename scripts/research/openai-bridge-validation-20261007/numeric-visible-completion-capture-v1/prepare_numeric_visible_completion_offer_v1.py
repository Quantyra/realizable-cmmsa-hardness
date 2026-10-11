from pathlib import Path
import hashlib
import json
import re
import tarfile

S = Path(__file__).resolve().parent
OUT = S/'numeric-visible-completion-offer-20261011-v1'
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PIN = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
REF = S/'full107-trace-qualified-source-record-v1/review-sources'
sha = lambda b: hashlib.sha256(b).hexdigest().upper()
assert not (OUT/'manifest.json').exists()
assert sha(ARCHIVE.read_bytes()) == PIN
deps = []
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    for name in ['ActualOccurrenceAllocation', 'ActualStarQuestionSupport', 'ActualStarSpanIntersection',
                 'ActualTaggedFixedCenterGeometry', 'ActualTaggedConcreteStarLaw',
                 'ActualTaggedPresentedSelection', 'ActualTaggedSelectedDecoderBridge']:
        member = 'lean/PvNP/RealizableHardness/'+name+'.lean'
        raw = archive.extractfile(member).read()
        assert raw == (REF/member).read_bytes()
        deps.append(dict(member=member, bytes=len(raw), sha256=sha(raw)))
candidate_deps = []
for folder, file, pin in [
    ('numeric-row-deletion-offer-20261011-v1', 'ActualTaggedRowDeletion.lean', 'F844D422FEF025399462872F9F59D6EC1E8BA41C28DCE4D95B20C463B876390B'),
    ('numeric-tagged-common-leaf-offer-20261011-v2', 'ActualTaggedCommonLeafCoherence.lean', '1BC581FC9F0BB3D5E6DAFCD96FAA88D773CD57BF1D749CE94011888BCF6A2D8A')]:
    path = S/folder/file
    raw = path.read_bytes()
    assert sha(raw) == pin
    candidate_deps.append(dict(path=str(path), module=path.stem, bytes=len(raw), sha256=pin, status='uncompiled'))
source = (OUT/'ActualVisibleQuestionCompletion.lean').read_bytes()
code = source.decode('utf-8')
assert not re.search(r'\b(?:sorry|admit|axiom)\b', code)
exports = re.findall(r'(?m)^theorem (\w+)', code)
definitions = re.findall(r'(?m)^def (\w+)', code)
assert len(exports) == 10, exports
assert len(definitions) == 6, definitions
checks = 'import PvNP.RealizableHardness.ActualVisibleQuestionCompletion\n\n'
checks += ''.join('#check PvNP.RealizableHardness.ActualVisibleQuestionCompletion.'+n+'\n' for n in definitions)
checks += ''.join('#print axioms PvNP.RealizableHardness.ActualVisibleQuestionCompletion.'+n+'\n' for n in exports)
(OUT/'Checks.lean').write_text(checks, encoding='utf-8', newline='\n')
argument = '''# Visible-question completion and total second-prover table

E002/S3137. The complete construction and equality argument was recorded in the planning numeric obligations note, section 2026-10-11 Visible-question completion and table argument, before source translation. This is an uncompiled candidate.

Reachable(X) is existence of an actual good J-row question whose support contains the visible set X of tagged variables. completion(X) is chosen once from that existential, indexed solely by X. Equal visible sets yield equal completions by proof irrelevance, even when certified by different original questions. For any actual deletion draw, every retained variable is some position of an original row; hence its retained set is contained in that question's support and is reachable. The visible coordinate space consists of globally supported vectors vanishing off X. It is exactly the image of actualRetained under the original coordinate-space inclusion, proved in both directions for each draw.

For any X and ambient submodule L, visibleLeafTable is a linear functional on L: when X is unreachable it is zero; otherwise it is the globally selected canonical domain label on L+H_completion restricted to L if transverse to H_completion, and zero if nontransverse. It is total on all inputs. Its defining arguments contain no original sampled U, row enumeration or other hidden data.

If X is contained in the support of a good U, and L is a 2h-dimensional subspace of visibleCoordinateSpace(X), then L lies in the coordinate spaces of both U and completion(X). If L is transverse to both equation spaces, these give actual TaggedPresentedLeaf structures with the same L. The captured canonical_table_agrees_on_shared_leaf theorem for the SAME raw table and global representative choice identifies the restrictions of their canonical domain labels to L. Thus visibleLeafTable agrees with the original-U canonical table on exactly the doubly transverse entries. There is no assertion about nontransverse entries; the explicit exceptional-mass costs in the manuscript remain mandatory.

Seven project sources match Full114 and two candidate dependencies are exact-byte pinned. Ten public axiom requests and six definition checks are included. No local Lean/Lake ran. Full114 is unaccepted, and eventual GCP verification must rebind the complete scope to the accepted operator successor.

This constructs the visible-question table and its required coherence, not the entire decoder strategy or probability bound. Posterior completion-dependent exceptions, maximal-list selection, random-extension success, independent-vector advice correction, outer source-game marginal/NO, runtime and certification remain open.

Remaining to-do list: GCP kernel/axiom/warning verification; actual posterior exception charges and complete legitimate decoder; source NO, runtime, random-history and all certification gates.
'''
(OUT/'ARGUMENT.md').write_text(argument, encoding='utf-8', newline='\n')
(OUT/'.gitattributes').write_text('* -text\n', encoding='utf-8', newline='\n')
files = []
for path in sorted(OUT.iterdir()):
    raw = path.read_bytes()
    assert not raw.startswith(b'\xef\xbb\xbf') and '\ufffd' not in raw.decode('utf-8')
    files.append(dict(path=path.name, bytes=len(raw), sha256=sha(raw)))
manifest = dict(schema=OUT.name, author='/root', story='E002/S3137', accepted=False, compiler_invoked=False,
    full114_archive=dict(path=str(ARCHIVE), sha256=PIN), dependencies=deps, candidate_dependencies=candidate_deps,
    mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2', public_axiom_requests=exports,
    checked_definitions=definitions, files=files)
(OUT/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(source), checks_sha256=sha(checks.encode()),
    manifest_sha256=sha((OUT/'manifest.json').read_bytes()), exports=exports), indent=2))
