"""Bounded v1-to-v2 consumer delta review, retaining original terminal findings."""
import json
import tarfile
from pathlib import Path
from custody_checks import digest
from prepare_sourcesize_spectral_application import HERE, ROOT as CANDIDATE, PARENT, sha
from prepare_sourcesize_spectral_review import ROOT as PRIOR

ROOT = PRIOR.parent / 'sourcesize-spectral-application-delta-review-v2'


def main():
    pieces = [b'''FOCUSED SOURCE SIZE SPECTRAL CONSUMER V1-TO-V2 DELTA REVIEW; NOT FINAL ACCEPTANCE.
Read the complete two v1 and two v2 candidate bodies, both complete original consumers and captured contract bridge. Check that the four split identifiers are joined correctly, the material/dyadic statements and proof applications remain unchanged in meaning, and the named SourceSize inhabitant and direct axiom checks are correctly typed. Verify rows remain independent of m and the common actual source/tables/functionals plus every selector, failed-zoom, height/split/dimension/positive-parameter/dyadic guard are retained. Retain previous three complete consumer reviews, including all native and semantic debt. The exact11-body inhabitant proof and earlier full-source reviews are prior coverage, not fresh rereading in this packet. Both v2 files and Full101 remain UNCOMPILED. This review can close a static syntax/composition finding, never native acceptance. The named-body custody audit supplies exact per-lens prior receipts for49 prerequisite bodies; it resolves never-supplied claims for its enumerated unchanged sources, while preserving all conditional findings and R14 HIGH. Do not demand duplicate complete-body reviews without an actual identity/context/scope gap. State any genuine remaining gap precisely. Text hashes are not elaborated types. Each exact wrapper application still requires kernel elaboration, profiles and actual consumption trace. Check the adequacy of direct dependency axiom checks; do not require speculative meta-programming solely to mirror these applications. Use no tools, writes, Lean/Lake or subagents. Give per-finding disposition and remaining to-do list; no overall GO or whole-manuscript review.
''']
    rows = []

    def add(name, data, kind):
        rows.append(dict(path=name, bytes=len(data), sha256=sha(data), source_kind=kind))
        pieces.append(('\nCOMPLETE FILE ' + name + ' SHA256 ' + sha(data) + '\n').encode() + data)

    for version in ['v1', 'v2']:
        folder = HERE / ('sourcesize-spectral-application-candidate-' + version)
        record = json.loads((folder / 'derivation.json').read_bytes())
        for row in record['files']:
            data = (folder / Path(row['path']).name).read_bytes()
            assert sha(data) == row['sha256']
            add(version + '/' + row['path'], data, 'preserved v1' if version == 'v1' else 'fresh v2')
        add(version + '/derivation.json', (folder / 'derivation.json').read_bytes(), 'static derivation')
    capture = json.loads((PARENT / 'capture-manifest.json').read_bytes())
    with tarfile.open(PARENT / 'input-archive.tar.gz') as archive:
        for module in ['ActualSelectedComplementSourceSizeOriginalApplication',
                       'ActualSelectedComplementManuscriptDyadicMoment', 'SourceSizeContractBridge']:
            rel = 'lean/PvNP/RealizableHardness/' + module + '.lean'
            data = archive.extractfile(rel).read()
            assert sha(data) == capture['project_sources'][rel]['sha256']
            add(rel, data, 'captured Full100 original')
    for lens in ['proof-adversarial', 'complexity', 'non-claims']:
        p = HERE / 'sourcesize-spectral-review-reports' / (lens + '-01.md')
        receipt = json.loads(p.with_suffix('.json').read_bytes())
        assert digest(p) == receipt['report_sha256'] and receipt['native_exit'] == 0
        add('prior-reports/' + p.name, p.read_bytes(), 'complete prior terminal review')
    for name in ['spectral-prerequisite-review-coverage-v2.json',
                 'mz24-appendix-numbering-audit-v1.json']:
        p = HERE / name
        add(name, p.read_bytes(), 'root bounded custody/source audit; not native acceptance')
    data = b''.join(pieces)
    ROOT.mkdir()
    packet = ROOT / 'packet.txt'
    packet.write_bytes(data)
    value = dict(schema='sourcesize-spectral-consumer-delta-review-v2',
                 required_lenses=['proof-adversarial', 'complexity', 'non-claims'],
                 packets=[dict(path=str(packet), bytes=len(data), sha256=sha(data), files=rows)],
                 accepted=False, native_verified=False, full_goal_complete=False)
    (ROOT / 'manifest.json').write_text(json.dumps(value, indent=2)+'\n', encoding='utf-8')
    record = HERE / 'sourcesize-spectral-delta-review-record-v2'
    record.mkdir()
    (record / 'manifest.json').write_bytes((ROOT / 'manifest.json').read_bytes())
    print(json.dumps(dict(bytes=len(data), sha256=sha(data), files=len(rows))))


if __name__ == '__main__':
    main()
