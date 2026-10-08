"""Freeze complete fresh material bodies, prior reports and native/reuse evidence."""
import hashlib
import json
from pathlib import Path
import tarfile

ROOT = Path('C:/Users/dfred/.quantyra/builder02/full90-material-resource02')
BASE = ROOT/'consumption-v1/qualification'
OLD = ROOT.parent/'full89-resource02/consumption-v2/qualification'


def sha(data): return hashlib.sha256(data).hexdigest().upper()


def main():
    source = BASE/'review-sources'
    index_bytes = (source/'source-index.json').read_bytes(); index = json.loads(index_bytes)
    reuse_bytes = (BASE/'prior-review-reuse-audit.json').read_bytes(); reuse = json.loads(reuse_bytes)
    plan = json.loads((BASE/'complete-material-review-plan.json').read_bytes())
    library = BASE/'complexitylib-review-context-v1'
    library_index_bytes = (library/'source-index.json').read_bytes(); library_index = json.loads(library_index_bytes)
    if len(index['project_bodies']) != 319 or len(reuse['unchanged_prior_complete_bodies']) != 169:
        raise ValueError('Complete corpus/reuse scope changed')
    if reuse['new_source_index_sha256'] != sha(index_bytes): raise ValueError('Reuse/source binding mismatch')
    fresh = set(plan['fresh_project_paths'])
    rows = [dict(row, source_kind='project', source_root=str(source)) for row in index['project_bodies'] if row['path'] in fresh]
    rows += [dict(row, source_kind='Complexitylib', source_root=str(library)) for row in library_index['complete_sources']]
    if len(rows) != 154+23: raise ValueError('Fresh full-body scope differs')
    priority = ['ActualSelectedComplementHC46OriginalApplication','ActualSelectedComplementAnalyticMoment',
                'ActualSelectedComplementAppendMoment','ActualBinaryMatrixHC46OriginalExactInhabitant',
                'ActualLeafLabelRankImageAlignment']
    def order(row):
        stem = Path(row['path']).stem
        if stem in priority: return (0, priority.index(stem), row['path'])
        if row['source_kind'] == 'Complexitylib': return (1, 0, row['path'])
        return (2, 0, row['path'])
    rows.sort(key=order)
    chunks, current, size = [], [], 0
    for row in rows:
        data = (Path(row['source_root'])/row['path']).read_bytes()
        if sha(data) != row['sha256'] or len(data) != row['bytes']: raise ValueError('Source identity mismatch')
        if current and size+len(data) > 450000:
            chunks.append(current); current, size = [], 0
        current.append(row); size += len(data)
    if current: chunks.append(current)
    marker = json.loads((ROOT/'launch-once.json').read_bytes())
    check = Path(marker['preflight'])
    native_path = check/'qualified-native'/marker['run']/'material-expanded-native-report.json'
    native_bytes = native_path.read_bytes(); native = json.loads(native_bytes)
    if not native['full90_expanded_native_gates_green'] or native['expanded_requested_axiom_count'] != 173:
        raise ValueError('Expanded native qualification incomplete')
    custody = json.loads((check/'terminal-custody.json').read_bytes())['custody']
    if sha(Path(custody['repository_path']).read_bytes()) != custody['remote_sha256']: raise ValueError('Native custody drift')
    with tarfile.open(custody['repository_path']) as archive:
        stdout = archive.extractfile('stage-6.stdout').read()
    instructions = '''Independent Full90 material-consumer review, one partition of a complete review.
The complete project corpus is ALL319 captured files.169 prior complete bodies are identity-eligible for reuse;150 project bodies are new/changed, and four unchanged critical material/HC/leaf bodies are freshly re-read.23 complete Complexitylib public-import context files are also supplied across these packets. Every lens must inspect every fresh packet, with final integration before material review completion. No tools, writes, code, Lean/Lake or subagents.
Native scope: the unchanged original seven stages and172 requests plus the explicit selected_actual_material_moment_bound_original root,173 total. All stages zero; standard root axioms only; all319 sources/645 compiled objects preserved;566 unchanged warm objects; exact source/compiler/package/core/configuration identities and independently terminated dedicated02. Zero OWNED warnings and inherited regressions are distinct from zero TOTAL warnings; inherited debt remains open. Fresh trace:173 roots/focused-five,7979 exact type DAG/edge matches,194 consumed project modules,2738 external boundaries, zero unresolved nodes. Compilation does not imply a standard profile for every declaration in every compiled file. Only requested roots/reached constants carry the fresh transitive evidence.
Review the SAME material I/copies/U/A/C/T/f, coordinate tables/functional and moment/source mass identities. The explicit downstream export supplies original_HC46_exact to the identical original material theorem, removing ONLY hHC. hSpectral : Spectral47ExactContract, selector, failed-zoom, strict rank and positive-parameter premises remain. Verify the exact exported conclusion and guards; do not substitute the selected-leaf wrapper or a easier surrogate. Spectral47, useful numericNO, source/star/robust8S, encoded reduction/runtime/learning, original upstream builds/bridges, warning disposition, fresh checkout, manuscript fidelity/render/novelty/citations and final full-scope providers remain OPEN. No whole-manuscript verdict is requested.
Pinned Init/Mathlib/Batteries kernel/library trust is explicit, not newly reviewed proof. Complexitylib is a NEW boundary review obligation; its four directly reached modules and COMPLETE23-module public/private import context are supplied. Audit representations, assumptions, padding/reindexing, sampling, quantified family hypotheses and any claimed computational bounds. Do not silently treat it as previously reviewed or prove an assumed ExpanderFamily/other source interface by citation. All existing sources are pinned; source pinning is not independent review or proof acceptance.
Prior27 full packet reports and three full selected-leaf/native integration syntheses are preserved below. Reuse only under the exact verified169-source/7251-shared-node type-and-dependency/compiler identity audit; prior material readiness was INCOMPLETE. Report GO/GO-WITH-NOTES/NO-GO/INCOMPLETE FOR THIS PACKET ONLY, each complete supplied file inspected/skipped, precise declarations/severity/disposition/remaining questions and safe conditional claim. Any skipped required body is INCOMPLETE. Retain cross-packet questions for integration; never endorse Root's preparation as acceptance.
'''
    common = instructions+'\nCURRENT NATIVE QUALIFICATION\n'+native_bytes.decode()
    common += '\nEXACT FRESH173 STDOUT\n'+stdout.decode()
    common += '\nFULL CORPUS SOURCE PINS\n'+json.dumps(index['project_bodies'],separators=(',',':'))
    common += '\nVERIFIED PRIOR REUSE IDENTITY AUDIT\n'+reuse_bytes.decode()
    common += '\nCOMPLEXITYLIB CONTEXT IDENTITY\n'+library_index_bytes.decode()
    for lens in ['proof-adversarial','complexity','non-claims']:
        for number in range(1,10):
            folder = OLD/f'review-packets/{lens}-{number:02d}'
            raw = (folder/'stdout.json').read_bytes(); report = json.loads(raw)
            if int((folder/'native-exit.txt').read_text()) != 0 or report['is_error'] or not report['result'].strip():
                raise ValueError('Prior report absent')
            common += f'\nFULL PRIOR REPORT {lens} packet{number}; raw SHA {sha(raw)}\n'+report['result']+'\n'
        folder = OLD/f'integration-synthesis-v1/{lens}-01'
        raw = (folder/'stdout.json').read_bytes(); report = json.loads(raw)
        if int((folder/'native-exit.txt').read_text()) != 0 or report['is_error']: raise ValueError('Prior synthesis absent')
        common += f'\nFULL PRIOR SELECTED-LEAF/NATIVE SYNTHESIS {lens}; raw SHA {sha(raw)}\n'+report['result']+'\n'
    destination = BASE/'material-review-packets-v1'; destination.mkdir()
    packets = []
    for number, group in enumerate(chunks,1):
        text = common+f'\nCURRENT PACKET {number}/{len(chunks)}. FULL SOURCE ROOT {source}\n'
        for row in group:
            data = (Path(row['source_root'])/row['path']).read_bytes()
            text += f'\n=== COMPLETE FILE {row["source_kind"]} {row["path"]} SHA256 {row["sha256"]} ===\n'+data.decode()+'\n=== END COMPLETE FILE ===\n'
        data = text.encode()
        if len(data) >= 1300000: raise ValueError('Complete-body packet exceeds planned byte bound')
        path = destination/f'packet-{number:02d}.txt'; path.write_bytes(data)
        packets.append({'path':str(path),'sha256':sha(data),'bytes':len(data),'files':group})
    manifest = {'schema':'full90-complete-material-review-packets-v1','packets':packets,
                'required_lenses':['proof-adversarial','complexity','non-claims'],
                'complete_project_scope':319,'prior_unchanged_complete_bodies':169,'fresh_complete_project_bodies':154,
                'fresh_Complexitylib_complete_sources':23,'complete_prior_reports':30,
                'source_index_sha256':sha(index_bytes),'native_report_sha256':sha(native_bytes),
                'reuse_audit_sha256':sha(reuse_bytes),'common_evidence_bytes':len(common.encode()),
                'whole_files_no_truncation':True,'actual_provider_context_fit_verified':False,
                'all_packets_each_lens_required':True,'integration_required':True,'accepted':False,'full_goal_complete':False}
    (destination/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'packets':len(packets),'complete_fresh_files':len(rows),
                      'common_bytes':len(common.encode()),'max_packet_bytes':max(p['bytes'] for p in packets)}))


if __name__ == '__main__': main()
