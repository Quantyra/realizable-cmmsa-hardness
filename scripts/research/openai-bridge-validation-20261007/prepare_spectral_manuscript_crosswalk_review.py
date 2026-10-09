"""Supply the manuscript/primary-source/caller bodies omitted from the prior review."""
import json
from pathlib import Path
import subprocess
import tarfile
from custody_checks import digest
from prepare_builder02 import sha
from prepare_builder02_full101 import OUTPUT, PARENT
from prepare_exact_spectral_operator_review import ROOT as BASE, PLANNING, ARGUMENT

HERE = Path(__file__).parent
ROOT = OUTPUT / 'spectral-manuscript-crosswalk-review-v1'
PRIMARY = Path('C:/Users/dfred/.quantyra/source-verification/spectral-primary-20261009-v1')


def main():
    previous = json.loads((BASE / 'manifest.json').read_bytes())
    row = previous['packets'][0]
    packet = Path(row['path']).read_bytes()
    assert sha(packet) == row['sha256'] == '7F2CAE47E70FB6C6C6F32F06D919F358CB96551FA326926486B58B6117EE2BF5'
    reconciliation = (HERE / 'exact-spectral-operator-reports/root-reconciliation-v1.json').read_bytes()
    assert sha(reconciliation) == 'BB18C27E63668FD255DA7B8AF1811568CA999E4795098DB760EA6BC8D003E430'
    pieces = [b'''SPECTRAL MANUSCRIPT / PRIMARY-SOURCE / ACTUAL-CALLER CROSSWALK REVIEW; NOT FINAL ACCEPTANCE.
Resolve the precise M1 omission raised by the prior exact-operator reviews. The complete current manuscript, version-pinned primary TeX members, coordinate-equivalence defining source, source-alignment audit, actual SourceSize/dyadic callers and frozen Full101 selected-leaf application/Checks are now supplied. Read every newly supplied complete body. Compare the actual finite-spectral lemma/proof and cited MZ Section4.2/Lemma4.7/MZ24 AppendixA.10-A.13 to the complete argument and captured contract. Check exact unconditional T, independent unrestricted B/full-row-rank C, uniform injection G, restricted adjoint, squared normalization, exact versus weaker eigenvalue, parameter mapping and every standing/source hypothesis. The exact count formula is our independent reconstruction, not a quotation of A.13. Do not silently normalize source G/H/dimension or transpose notation; state precisely how the typed reconstruction resolves it or leaves it open.
Inspect original selected-leaf application versus complete original SourceSize and dyadic callers. State which spectral premises are actually removed by the frozen offered candidate and which downstream premises remain. Do not relabel a selected-leaf wrapper as full source/table/runtime completion. Preserve the actual common I/copies/U/A/C/T/f, independent source-row count, fixed m/arity, source-height/parity/rho/split/ambient guards and actual original HC46 consumption. Check natural/real rank-product zero cases, and ordinary versus squared contraction.
The prior33 bodies are supplied again byte-identically for access, with prior three complete reports and reconciliation. Separate fresh review of the8 new bodies from identity reuse of the33 earlier supplied bodies; do not invent fresh full340 coverage. The manuscript body is supplied in full, but this review's acceptance scope is only the spectral statement/operator/analytic-caller crosswalk, not complete manuscript validity or novelty. Explicitly inventory any unsupplied import/primary-source prerequisites that affect this scope.
All recovered Full101 sources and the exact-energy candidate remain uncompiled in this lineage. GCP authentication is pending. A sound informal/source crosswalk cannot close native compilation, exact trace, axiom/warning/custody/replay gates. Keep numeric NO, source/star/robust8S/pre-draw/sampler/encoded reduction/runtime/learning/upstream debt, R14 HIGH, novelty/citations/PDF/final-provider/publication obligations open. No overall GO.
Use no tools, writes, Lean/Lake or subagents. Give per-finding severity, exact body evidence, disposition and remaining actions. Distinguish M1 source-shape alignment, sufficiency of the full exact mathematical argument, actual consuming application and native/manuscript final readiness. End with remaining to-do list.
''', b'\nCOMPLETE PREVIOUS PACKET (33 BODIES) SHA256 ' + sha(packet).encode() + b'\n' + packet,
              b'\nCOMPLETE ROOT RECONCILIATION SHA256 ' + sha(reconciliation).encode() + b'\n' + reconciliation]
    for lens in ['proof-adversarial', 'complexity', 'non-claims']:
        p = HERE / 'exact-spectral-operator-reports' / (lens + '-01.md')
        receipt = json.loads(p.with_suffix('.json').read_bytes())
        assert digest(p) == receipt['report_sha256'] and receipt['native_exit'] == 0 and receipt['actual_packet_context_fit']
        pieces.append(('\nCOMPLETE PRIOR REVIEW ' + lens + ' SHA256 ' + digest(p) + '\n').encode() + p.read_bytes())
    argument = subprocess.check_output(['git', 'show', 'HEAD:' + ARGUMENT], cwd=PLANNING)
    assert (PLANNING / ARGUMENT).read_bytes().replace(b'\r\n', b'\n') == argument
    pieces.append(b'\nCOMPLETE CURRENT ARGUMENT SHA256 ' + sha(argument).encode() + b'\n' + argument)
    rows = [dict(r, review_disposition='prior exact-body identity reuse; available in full') for r in row['files']]
    new_rows = []

    def add(path, data, kind, status):
        record = dict(path=path, source_kind=kind, sha256=sha(data), bytes=len(data), native_status=status,
                      review_disposition='new complete body; fresh scoped review required')
        rows.append(record)
        new_rows.append(record)
        pieces.append(('\n=== NEW COMPLETE FILE ' + path + ' SHA256 ' + sha(data) + ' ===\n').encode() + data + b'\n=== END NEW COMPLETE FILE ===\n')

    paper = subprocess.check_output(['git', 'show', 'HEAD:paper/submission-manuscript.md'])
    assert sha(paper) == '6F8D65349C36E10E294B26860ACAA81F7103401C272CF84B23DF35D75C10B98A'
    add('paper/submission-manuscript.md', paper, 'Current manuscript', 'Unaccepted manuscript; bounded spectral/caller scope only')
    audit = json.loads((HERE / 'spectral-primary-source-version-audit-v1.json').read_bytes())
    for item in audit['proof_members']:
        archive_path = PRIMARY / item['archive']
        assert digest(archive_path) == item['archive_sha256']
        with tarfile.open(archive_path) as archive:
            data = archive.extractfile(item['member']).read()
        assert sha(data) == item['member_sha256'] and len(data) == item['bytes']
        add('primary/' + item['archive'] + '/' + item['member'], data, 'Version-pinned primary source',
            'Unmodified source text; notation issues retained; no imported Lean theorem')
    manifest = json.loads((PARENT / 'capture-manifest.json').read_bytes())
    with tarfile.open(PARENT / 'input-archive.tar.gz') as archive:
        for module in ['ActualFixedFunctionalBinaryMatrixMoment', 'ActualSelectedComplementSourceSizeOriginalApplication',
                       'ActualSelectedComplementManuscriptDyadicMoment']:
            rel = 'lean/PvNP/RealizableHardness/' + module + '.lean'
            data = archive.extractfile(rel).read()
            assert sha(data) == manifest['project_sources'][rel]['sha256'] and len(data) == manifest['project_sources'][rel]['bytes']
            add(rel, data, 'Full100 project source', 'Native compiled exact source; spectral caller premises retained')
    successor = json.loads((OUTPUT / 'capture-manifest.json').read_bytes())
    with tarfile.open(OUTPUT / 'input-archive.tar.gz') as archive:
        for module in ['ActualSelectedComplementSpectral47OriginalApplication', 'ActualSelectedComplementSpectral47OriginalApplicationChecks']:
            rel = 'lean/PvNP/RealizableHardness/' + module + '.lean'
            data = archive.extractfile(rel).read()
            assert sha(data) == successor['project_sources'][rel]['sha256'] and len(data) == successor['project_sources'][rel]['bytes']
            add(rel, data, 'Full101 original selected-leaf application', 'Frozen/unlaunched; no native acceptance')
    alignment = (HERE / 'full100-actual-spectral-source-alignment-v1.json').read_bytes()
    assert sha(alignment) == '52295A1A03A87AF4B75CACC6C1D89451408093A2E7E69F8398B59D65C637F511'
    pieces.append(b'\nCOMPLETE SOURCE ALIGNMENT AUDIT SHA256 ' + sha(alignment).encode() + b'\n' + alignment)
    result = b''.join(pieces)
    assert len(rows) == 41 and len(new_rows) == 8 and len(result) < 1800000
    ROOT.mkdir()
    p = ROOT / 'crosswalk-and-complete-sources.txt'
    with p.open('xb') as stream:
        stream.write(result)
    value = dict(schema='spectral-manuscript-primary-caller-crosswalk-review-v1',
        required_lenses=['proof-adversarial', 'complexity', 'non-claims'],
        packets=[dict(path=str(p), sha256=sha(result), bytes=len(result), files=rows)],
        prior_packet_sha256=sha(packet), prior_reconciliation_sha256=sha(reconciliation),
        fresh_complete_bodies=new_rows, fresh_body_count=8, prior_body_identity_reuse_count=33,
        argument_sha256=sha(argument), manuscript_sha256=sha(paper), source_alignment_audit_sha256=sha(alignment),
        acceptance_scope='Spectral source/operator/analytic-caller crosswalk only',
        full_manuscript_or_full340_semantic_review_claimed=False, native_candidate_verified=False,
        accepted=False, overall_GO=False, full_goal_complete=False)
    with (ROOT / 'manifest.json').open('x', encoding='utf-8', newline='\n') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')
    print(json.dumps(dict(packet_sha256=sha(result), bytes=len(result), supplied=41, fresh=8, accepted=False)))


if __name__ == '__main__':
    main()
