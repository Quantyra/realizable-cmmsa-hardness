"""Freeze complete critical argument and pinned bodies for independent assessment."""
import hashlib
import json
from pathlib import Path
import subprocess
import tarfile
from full100_consumption_v2_controller import ROOT, ready

HERE = Path(__file__).parent
PLANNING = Path('C:/Users/dfred/Desktop/Projects/IGH/Quantyra-AI-Planning')
ARGUMENT = 'docs/research/pvnp/actual-append-spectral-image-fibre-argument-2026-10-09.md'
PROJECT = ['ActualFixedFunctionalAppendOperator','ActualAppendFourierCrossLevelOrthogonality',
 'BinaryMatrixFourier','ActualSelectedComplementSourceSizeAnalyticMoment',
 'BinaryMatrixRightOrbit','BinaryMatrixRightFourierCovariance',
 'BinaryMatrixSameRangeOrbit','MatrixLiftAffineTarget','SourceSizeContractBridge',
 'ActualSelectedComplementAnalyticMoment']
EXTERNAL = ['LinearAlgebra/Matrix/GeneralLinearGroup/Card.lean',
 'LinearAlgebra/Dimension/Finite.lean','LinearAlgebra/Dual/Defs.lean',
 'LinearAlgebra/Dual/Lemmas.lean','LinearAlgebra/Matrix/ToLin.lean']

def sha(data): return hashlib.sha256(data).hexdigest().upper()

def main():
    loaded, runner, binding = ready()
    argument = subprocess.check_output(['git','show','HEAD:'+ARGUMENT],cwd=PLANNING)
    assert (PLANNING/ARGUMENT).read_bytes().replace(b'\r\n',b'\n') == argument
    head = subprocess.check_output(['git','rev-parse','HEAD'],cwd=PLANNING).decode().strip()
    base = ROOT.parent
    manifest = json.loads((base/'capture-manifest.json').read_bytes())
    marker = json.loads((base/'launch-once.json').read_bytes())
    native = Path(marker['preflight'])/'qualified-native'/marker['run']/'material-expanded-native-report.json'
    assert sha(native.read_bytes()) == binding['qualified_report_sha256']
    pieces = [b'''FULL100 ACTUAL SPECTRAL CRITICAL-ARGUMENT REVIEW, NOT FINAL ACCEPTANCE.
Assess the complete supplied image-fibre argument against the exact original Spectral47ExactContract and actual unconditional append operator. All n,c,s,i and right-basis invariant real F, deficient/zero matrices, impossible dimensions, normalization, every original parity/height/rho/source guard, and both inverse directions of each proposed bijection remain in scope. Native GREEN verifies existing helper declarations; the full coefficient/count/energy/gain/contract transports are still proposals awaiting translation. Exact consumption trace and fresh integration body review are pending. Do not treat this packet as full327 source coverage or overall manuscript review.
Proof-adversarial lens: independently derive or refute the whole argument, including Fourier covariance transpose direction, same-image coefficient constancy, zero-tail image/rank preservation, coefficient/Parseval normalization, fixed-image surjection/duality/frame bijections and their inverse laws, finite cardinality assumptions, image-fibre grouping and representative existence, positive denominators, all zero/impossible branches, real-valued gain inequality and original contract transfer. Read every complete source supplied. Distinguish a sound informal argument from missing native API transports. Identify any hidden assumption or changed target.
Complexity lens: assess whether the argument targets the actual operator/dimensions and scope; separate finite mathematical identities from constructive algorithms and encoded runtime. No source/sampler/selection/reduction/learning runtime witness or numeric NO is supplied or claimed. Preserve that open debt; do not demand an unrelated conditional surrogate in place of the universal spectral target.
Non-claims lens: audit all claims and coverage. Existing Mathlib frame cardinality is not new counting novelty. Native helpers and source availability are not a full contract inhabitant. The original source/star/robustness/pre-draw witnesses, physical sampling, numeric NO, encoded runtime, upstream bridges, warning/fresh-checkout certification, novelty/citations/PDF and publication remain open. There is no overall GO, manuscript acceptance, unconditional hardness result or priority claim.
No tools, writes, Lean/Lake or subagents. State inspected/skipped complete bodies, step-specific severity/evidence/disposition/actions, and whether the whole argument is sufficient, requires repair or is inconclusive. Report argument sufficiency separately from native/final readiness. End with remaining to-do list.
''']
    pieces += [b'\nCOMPLETE ARGUMENT '+sha(argument).encode()+b'\n'+argument,
               b'\nQUALIFIED NATIVE REPORT '+binding['qualified_report_sha256'].encode()+b'\n'+native.read_bytes()]
    rows = []
    with tarfile.open(base/'input-archive.tar.gz') as archive:
        for module in PROJECT:
            rel = 'lean/PvNP/RealizableHardness/'+module+'.lean'
            data = archive.extractfile(rel).read(); row = manifest['project_sources'][rel]
            assert (sha(data),len(data)) == (row['sha256'],row['bytes'])
            rows.append(dict(path=rel,source_kind='project',sha256=sha(data),bytes=len(data)))
            pieces.append(('\n=== COMPLETE FILE '+rel+' SHA256 '+sha(data)+' ===\n').encode()+data+b'\n=== END COMPLETE FILE ===\n')
    corpus = base.parent/'full97-spectral-bridge-utf8-section-repair-resource02/consumption-v1/qualification/review-sources/external/Mathlib'
    frozen = Path('C:/Users/dfred/.quantyra/resume-workspaces/full81/realizable-cmmsa-hardness/.lake/packages/mathlib/Mathlib')
    for rel in EXTERNAL:
        path = next((p for p in [corpus/rel,frozen/rel] if p.is_file()),None)
        assert path is not None, rel
        data = path.read_bytes(); key = '.lake/packages/mathlib/Mathlib/'+rel
        assert sha(data) == manifest['cache_provenance']['package_sources'][key]
        rows.append(dict(path=key,source_kind='Mathlib',sha256=sha(data),bytes=len(data)))
        pieces.append(('\n=== COMPLETE FILE '+key+' SHA256 '+sha(data)+' ===\n').encode()+data+b'\n=== END COMPLETE FILE ===\n')
    packet = b''.join(pieces); assert len(packet)<1800000 and len(rows)==15
    destination = ROOT/'spectral-argument-review-v1'; destination.mkdir()
    path = destination/'argument-and-complete-sources.txt'
    with path.open('xb') as stream: stream.write(packet)
    value = dict(schema='full100-complete-spectral-critical-argument-review-v1',
        required_lenses=['proof-adversarial','complexity','non-claims'],
        packets=[dict(path=str(path),sha256=sha(packet),bytes=len(packet),files=rows)],
        planning_head=head,argument_path=ARGUMENT,argument_sha256=sha(argument),
        native_run=binding['run'],native_report_sha256=binding['qualified_report_sha256'],
        capture_manifest_sha256=binding['capture_manifest_sha256'],
        complete_project_bodies=10,complete_Mathlib_bodies=5,
        full327_body_review_claimed=False,exact_trace_pending=True,
        universal_native_proof=False,accepted=False,full_goal_complete=False)
    with (destination/'manifest.json').open('x',encoding='utf-8') as stream:
        json.dump(value,stream,indent=2);stream.write('\n')
    print(json.dumps(dict(packet_sha256=sha(packet),bytes=len(packet),complete_bodies=15,accepted=False)))

if __name__ == '__main__': main()
