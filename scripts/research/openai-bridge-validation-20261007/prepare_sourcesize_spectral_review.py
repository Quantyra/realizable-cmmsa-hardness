"""Freeze an actual-consumer review addendum with complete prior context."""
import hashlib
import json
from pathlib import Path
from prepare_sourcesize_spectral_application import ROOT as CANDIDATE, HERE
from prepare_spectral_manuscript_crosswalk_review import ROOT as PRIOR

ROOT = PRIOR.parent / 'sourcesize-spectral-application-review-v1'


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    old = json.loads((PRIOR / 'manifest.json').read_bytes())['packets'][0]
    previous = Path(old['path']).read_bytes()
    assert sha(previous) == old['sha256']
    pieces = [b'''SOURCE SIZE MATERIAL / MANUSCRIPT DYADIC SPECTRAL DISCHARGE REVIEW; NOT FINAL ACCEPTANCE.
Freshly review both complete new candidate files and their derivation. Verify the actual complete original SourceSize material and manuscript dyadic signatures in the prior packet; only theorem names and hSpectral premises may change. Check independent rows versus fixed leaf arity m, common I/copies/U/A/C/T/f, selector/height/parity/rho/split/dimension/failed-zoom/positive-parameter/dyadic guards and every conclusion. Check exact argument order and namespace resolution; no legacy material consumer is acceptable. The original consumer supplies original_HC46_exact and this successor supplies the recovered Spectral47 inhabitant through the legacy-to-SourceSize native Iff bridge. Review the explicit SourceSize-shaped example and axiom checks. Both new candidates are UNCOMPILED; static reconstruction is not kernel evidence. Frozen Full101 is unchanged and must compile as captured before any diagnostics repair. Exact eigenvalue/operator, scalar/source/runtime/upstream, R14 HIGH and final manuscript/publication gates remain open.
The full prior packet and all three complete terminal reviews are supplied for context, with41 prior bodies explicitly labelled reuse rather than fresh full-body review. Acceptance scope is only these two new candidate bodies and actual consumer composition, not a full343-source or whole-manuscript review. Distinguish mathematical implication, elaboration risks, native obligations and claims boundaries. Inventory missing load-bearing bodies and whether prior exact-body review reuse could discharge that coverage. Use no tools, writes, Lean/Lake or subagents. Give findings with severity and a remaining to-do list. No overall GO.
''', previous]
    for lens in ['proof-adversarial', 'complexity', 'non-claims']:
        p = HERE / 'spectral-manuscript-crosswalk-reports' / (lens + '-01.md')
        receipt = json.loads(p.with_suffix('.json').read_bytes())
        data = p.read_bytes()
        assert sha(data) == receipt['report_sha256'] and receipt['native_exit'] == 0
        pieces.append(('\nCOMPLETE PRIOR REVIEW ' + lens + ' SHA256 ' + sha(data) + '\n').encode() + data)
    # Supply the actual full captured bridge, not a handwritten signature.
    import tarfile
    from prepare_sourcesize_spectral_application import PARENT
    with tarfile.open(PARENT / 'input-archive.tar.gz') as t:
        rel = 'lean/PvNP/RealizableHardness/SourceSizeContractBridge.lean'
        bridge = t.extractfile(rel).read()
    manifest = json.loads((PARENT / 'capture-manifest.json').read_bytes())
    assert sha(bridge) == manifest['project_sources'][rel]['sha256']
    pieces.append(('\nCOMPLETE CAPTURED CONTRACT BRIDGE SHA256 ' + sha(bridge) + '\n').encode() + bridge)
    rows = [dict(r, review_disposition='prior body available in full; identity reuse') for r in old['files']]
    rows.append(dict(path=rel, bytes=len(bridge), sha256=sha(bridge), review_disposition='fresh complete bridge body'))
    derivation = json.loads((CANDIDATE / 'derivation.json').read_bytes())
    for row in derivation['files']:
        data = (CANDIDATE / Path(row['path']).name).read_bytes()
        assert sha(data) == row['sha256']
        rows.append(dict(row, review_disposition='fresh complete uncompiled candidate'))
        pieces.append(('\nCOMPLETE NEW CANDIDATE ' + row['path'] + ' SHA256 ' + sha(data) + '\n').encode() + data)
    pieces.append(b'\nCOMPLETE STATIC DERIVATION\n' + (CANDIDATE / 'derivation.json').read_bytes())
    data = b''.join(pieces)
    ROOT.mkdir()
    path = ROOT / 'packet.txt'
    path.write_bytes(data)
    value = dict(schema='sourcesize-spectral-consumer-review-v1', required_lenses=['proof-adversarial', 'complexity', 'non-claims'],
                 packets=[dict(path=str(path), bytes=len(data), sha256=sha(data), files=rows)],
                 fresh_candidate_bodies=2, fresh_bridge_bodies=1, prior_body_reuse=41,
                 native_verified=False, accepted=False, overall_GO=False)
    (ROOT / 'manifest.json').write_text(json.dumps(value, indent=2)+'\n', encoding='utf-8')
    destination = HERE / 'sourcesize-spectral-review-record-v1'
    destination.mkdir()
    (destination / 'manifest.json').write_bytes((ROOT / 'manifest.json').read_bytes())
    print(json.dumps(dict(bytes=len(data), sha256=sha(data), files=len(rows))))


if __name__ == '__main__':
    main()
