"""Freeze the complete exact-energy/operator argument and relevant source bodies."""
import json
from pathlib import Path
import subprocess
import tarfile
from custody_checks import digest
from prepare_builder02 import sha
from prepare_builder02_full101 import OUTPUT, PARENT
from prepare_full100_spectral_argument_review import PROJECT, PLANNING, ARGUMENT

HERE = Path(__file__).parent
ROOT = OUTPUT / 'exact-spectral-operator-review-v1'
EXTERNAL = ['LinearAlgebra/Matrix/GeneralLinearGroup/Card.lean', 'LinearAlgebra/Dimension/Finite.lean',
    'LinearAlgebra/Dual/Defs.lean', 'LinearAlgebra/Dual/Lemmas.lean', 'LinearAlgebra/Matrix/ToLin.lean',
    'LinearAlgebra/Matrix/Rank.lean', 'FieldTheory/Finiteness.lean', 'Data/Matrix/Diagonal.lean',
    'LinearAlgebra/Matrix/Trace.lean']


def main():
    argument = subprocess.check_output(['git', 'show', 'HEAD:' + ARGUMENT], cwd=PLANNING)
    assert (PLANNING / ARGUMENT).read_bytes().replace(b'\r\n', b'\n') == argument
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=PLANNING).decode().strip()
    manifest = json.loads((PARENT / 'capture-manifest.json').read_bytes())
    successor = json.loads((OUTPUT / 'capture-manifest.json').read_bytes())
    marker = json.loads((PARENT / 'launch-once.json').read_bytes())
    native = Path(marker['preflight']) / 'qualified-native' / marker['run'] / 'material-expanded-native-report.json'
    assert digest(native) == '4D580EA63CF139E497FF366D007B5E8FB94B2AB9C6DB0DCE1FFF67D34A1883A4'
    pieces = [b'''EXACT ACTUAL SPECTRAL ENERGY / MANUSCRIPT OPERATOR ARGUMENT REVIEW; NOT FINAL ACCEPTANCE.
Independently derive or refute the entire exact manuscript route in the complete argument: actual unconditional append, fixed-image exact retained/full counts, G(c,i)/G(d,i)=G(d-i,s)/G(d,s), natural/real zero-factor conversion, uniform GL completion marginals in both directions, G T F=Phi F with unrestricted B independent of full-row-rank C, character kernel-frame eigenvalue, restricted adjoint on invariant first argument, cross-level orthogonality and exact energy equality. Preserve arbitrary invariant real functions, paired inverse changes on all matrices, all zero-width/rank/impossible/empty branches, normalization and every original contract/source guard. Check completion cardinalities and inverse distributions, not just symmetry assertions. The exact-energy Lean candidate is uncompiled translation, not kernel evidence. All eleven recovered sources in Full101 are uncompiled in this lineage; Full100 native GREEN covers only its327 captured sources. Do not upgrade informal source inspection to proof acceptance.
Proof-adversarial: read all supplied bodies, verify both inverse directions/finite carrier assumptions/transpose orientations and every step of the exact operator argument, including the n=0,c=0,s=0,i=0,i>c,i>n boundaries. Distinguish mathematical errors, missing source/native transports, and harmless elaboration uncertainty. Assess whether this route proves every exact manuscript equality and the unchanged guarded inequality, not an easier inequality surrogate.
Complexity: distinguish finite existence/counting and classical choices from actual algorithms, encoded witnesses, sampler/runtime/learning complexity. Keep numeric NO, source/star/robust8S/pre-draw/sampling/reduction/runtime/upstream debt open, including R14 HIGH. A complete spectral argument does not imply hardness or a runtime witness.
Non-claims: audit source/native/planning/review evidence tiers, exact scope and omissions. Attribute classical results to MZ Lemma4.7/MZ24 AppendixA and existing Mathlib counts. No novelty/priority, unconditional source/runtime result, fresh-checkout replay, full340-body review, manuscript acceptance or publication GO is claimed. Existing warnings/provider/final QA gates remain open.
No tools, writes, Lean/Lake or subagents. Report all inspected/skipped supplied bodies and each step's sufficiency, severity, evidence and required action. Give argument sufficiency separately from candidate-native readiness and overall manuscript readiness. End with remaining to-do list.
''', b'\nCOMPLETE ARGUMENT SHA256 ' + sha(argument).encode() + b'\n' + argument,
              b'\nCOMPLETE FULL100 NATIVE REPORT SHA256 ' + digest(native).encode() + b'\n' + native.read_bytes()]
    rows = []

    def add(path, data, kind, native_status):
        rows.append(dict(path=path, source_kind=kind, sha256=sha(data), bytes=len(data), native_status=native_status))
        pieces.append(('\n=== COMPLETE FILE ' + path + ' SHA256 ' + sha(data) + ' NATIVE_STATUS ' + native_status + ' ===\n').encode() + data + b'\n=== END COMPLETE FILE ===\n')

    with tarfile.open(PARENT / 'input-archive.tar.gz') as archive:
        for module in PROJECT + ['GrassmannCounting']:
            rel = 'lean/PvNP/RealizableHardness/' + module + '.lean'
            data = archive.extractfile(rel).read()
            assert (sha(data), len(data)) == (manifest['project_sources'][rel]['sha256'], manifest['project_sources'][rel]['bytes'])
            add(rel, data, 'Full100 project', 'Full100 qualified native; exact upstream statement scope only')
    recovery = json.loads((HERE / 'existing-spectral-candidate-recovery-v1/recovery.json').read_bytes())
    with tarfile.open(OUTPUT / 'input-archive.tar.gz') as archive:
        for row in recovery['recovered_modules']:
            rel = row['path']
            data = archive.extractfile(rel).read()
            assert sha(data) == row['sha256'] == successor['project_sources'][rel]['sha256']
            add(rel, data, 'Recovered spectral candidate', 'Full101 frozen/unlaunched; no native acceptance')
    candidate = HERE / 'spectral-exact-energy-candidate-v1'
    for row in json.loads((candidate / 'candidate.json').read_bytes())['files']:
        data = (candidate / row['path'].rsplit('/', 1)[1]).read_bytes()
        assert sha(data) == row['sha256'] and len(data) == row['bytes']
        add(row['path'], data, 'Exact-energy candidate', 'Outside Full101; uncompiled/unaccepted')
    corpus = PARENT / 'consumption-v2/qualification/review-sources/external/Mathlib'
    frozen = Path('C:/Users/dfred/.quantyra/resume-workspaces/full81/realizable-cmmsa-hardness/.lake/packages/mathlib/Mathlib')
    for rel in EXTERNAL:
        p = next(p for p in [corpus / rel, frozen / rel] if p.is_file())
        data = p.read_bytes()
        key = '.lake/packages/mathlib/Mathlib/' + rel
        assert sha(data) == manifest['cache_provenance']['package_sources'][key]
        add(key, data, 'Pinned Mathlib', 'Pinned imported library source; no fresh whole-package replay')
    packet = b''.join(pieces)
    assert len(rows) == 33 and len(packet) < 1800000
    ROOT.mkdir()
    p = ROOT / 'complete-argument-and-sources.txt'
    with p.open('xb') as stream:
        stream.write(packet)
    value = dict(schema='complete-exact-actual-spectral-operator-review-v1',
        required_lenses=['proof-adversarial', 'complexity', 'non-claims'],
        packets=[dict(path=str(p), sha256=sha(packet), bytes=len(packet), files=rows)],
        planning_head=head, argument_sha256=sha(argument), native_report_sha256=digest(native),
        complete_project_bodies=24, complete_Mathlib_bodies=9,
        fresh_native_candidate_verification=False, full340_body_review_claimed=False,
        accepted=False, full_goal_complete=False)
    with (ROOT / 'manifest.json').open('x', encoding='utf-8', newline='\n') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')
    print(json.dumps(dict(packet_sha256=sha(packet), bytes=len(packet), complete_bodies=33, accepted=False)))


if __name__ == '__main__':
    main()
