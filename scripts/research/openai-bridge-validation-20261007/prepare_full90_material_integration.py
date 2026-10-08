"""Freeze complete material integration bodies/reports; never infer acceptance."""
import hashlib
import json
from pathlib import Path

BASE = Path('C:/Users/dfred/.quantyra/builder02/full90-material-resource02/consumption-v1/qualification')
PLANNING = Path('C:/Users/dfred/Desktop/Projects/IGH/Quantyra-AI-Planning/docs/research/pvnp')


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    packet_manifest = json.loads((BASE/'material-review-packets-v1/manifest.json').read_bytes())
    coverage_bytes = (BASE/'material-review-coverage-snapshot-v2.json').read_bytes()
    coverage = json.loads(coverage_bytes)
    assert not coverage['missing'] and len(coverage['completed']) == 15
    first = packet_manifest['packets'][0]
    packet = Path(first['path']).read_bytes()
    assert sha(packet) == first['sha256']
    common = packet.split(b'\nCURRENT PACKET 1/',1)[0]
    assert len(common) == packet_manifest['common_evidence_bytes']
    rows = [r for p in packet_manifest['packets'] for r in p['files']
            if r['source_kind'] == 'Complexitylib' or r['transitively_consumed']]
    assert len(rows) == 63 and sum(r['source_kind']=='project' for r in rows) == 40
    instructions = '''FULL90 WHOLE MATERIAL INTEGRATION REVIEW, superseding packet-only instructions below.
Read all 63 supplied complete bodies and all15 fresh reports; explicitly count inspected/skipped bodies. All319 project files have complete-body review coverage:169 prior bodies identity-eligible for reuse,150 new/changed bodies reviewed across5 packets, plus4 unchanged critical rereads. Reuse only the exact verified prior reports/native/source identities; do not claim rereading absent bodies. All40 freshly reviewed reached project modules and23 complete Complexitylib context bodies are together here. Integrate the SAME selected_actual_material_moment_bound_original export, I/copies/U/A/C/T/f, exact coordinates, unconditional moment/Grassmann laws, original A22/HC46 dependency and retained guards. No selected-leaf surrogate or narrowing the theorem.
Independently resolve all HIGH/Medium findings and cross-packet questions from all15 reports, using complete bodies and recorded constant scope. Author reconciliation notes are hypotheses to check, not independent evidence or votes. Check hsmall/dimension discharge and the actual reverse factor2 direction; selector existential output versus prescribed instance index; arbitrary classically chosen degree versus claimed blanket untagged-center vacuity; actual reached definitions versus source/star/expansion theorems. Audit the23 Complexitylib bodies and concrete algFamily/padding/RegGraph semantics separately from computability/runtime. The bounded recorded external boundary does not expand the whole external proof closure. Preserve the open Spectral47 contract; reviewer orbit sketch is not a machine proof or verified manuscript match. Useful e/hfail/a/numeric NO, full joint premise inhabitance, source/star/robust8S, encoded reduction/runtime/learning remain open.
No tools, writes, Lean/Lake or subagents. Native/compiler/custody facts are supplied evidence; do not invent results. Give a reconciled findings table with declarations, severity, disposition/evidence/remaining action, missing bodies or profiles, exact safe conditional claim and remaining to-do list. Separate material-statement/native integration verdict from unconditional material readiness and manuscript verdict. Any skipped required body or unresolved HIGH precludes an overall integration GO. Upstream selected build/profiles do not prove CMMSA bridges, and warning/fresh-checkout, novelty/citations/render/final provider gates remain open. No full manuscript acceptance.
'''
    text = instructions.encode()+b'\nPRESERVED NATIVE/REUSE EVIDENCE AND30 PRIOR REPORTS\n'+common
    text += b'\nEXACT FIFTEEN-REPORT COVERAGE SNAPSHOT\n'+coverage_bytes
    reports = Path(__file__).parent/'full90-material-review-reports'
    for row in coverage['completed']:
        data = (reports/(row['key']+'.md')).read_bytes()
        assert sha(data) == row['report_sha256']
        text += ('\nFULL FRESH REPORT '+row['key']+'\n').encode()+data
    index = json.loads((BASE/'reached-constant-index-v1.json').read_bytes())
    selected_modules = {r['path'].removeprefix('lean/').removesuffix('.lean').replace('/','.') for r in rows if r['source_kind']=='project'}
    # Whole constant names and focused-root membership; no cropped source bodies.
    scope = {m:[dict(name=r['name'],kind=r['kind'],focused_roots=r['focused_roots']) for r in rs]
             for m,rs in index['modules'].items() if m in selected_modules or m.startswith('Complexitylib.')}
    text += b'\nRECORDED REACHED CONSTANTS AND FOCUSED ROOT MEMBERSHIP\n'+json.dumps(scope,ensure_ascii=False).encode()
    notes = ['full90-exact-reached-constant-scope-2026-10-08.md',
             'full90-untagged-center-vacuity-degree-qualification-2026-10-08.md',
             'full90-selector-floor-existence-reconciliation-2026-10-08.md',
             'full90-material-rankloss-guard-reconciliation-2026-10-08.md',
             'full90-actual-rhs-numeric-no-obligations-2026-10-08.md',
             'upstream-seven-native-profile-custody-2026-10-08.json']
    for name in notes:
        text += ('\nAUTHOR RECONCILIATION OR BOUNDED RECEIPT '+name+'\n').encode()+(PLANNING/name).read_bytes()
    for row in rows:
        data = (Path(row['source_root'])/row['path']).read_bytes()
        assert len(data)==row['bytes'] and sha(data)==row['sha256']
        text += f'\n=== COMPLETE FILE {row["source_kind"]} {row["path"]} SHA256 {row["sha256"]} ===\n'.encode()+data+b'\n=== END COMPLETE FILE ===\n'
    assert len(text) < 1800000, 'Requires whole-body context strategy, never truncate'
    destination = BASE/'material-integration-v1'; destination.mkdir()
    path = destination/'integration.txt'; path.write_bytes(text)
    manifest = dict(schema='full90-material-integration-v1',required_lenses=packet_manifest['required_lenses'],
        packets=[dict(path=str(path),sha256=sha(text),bytes=len(text),files=rows)],
        fresh_report_count=15,prior_report_count=30,coverage_sha256=sha(coverage_bytes),
        complete_material_reached_project_bodies=40,complete_complexitylib_context_bodies=23,
        actual_provider_context_fit_verified=False,accepted=False)
    (destination/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(bytes=len(text),complete_bodies=63,sha256=sha(text))))


if __name__ == '__main__':
    main()
