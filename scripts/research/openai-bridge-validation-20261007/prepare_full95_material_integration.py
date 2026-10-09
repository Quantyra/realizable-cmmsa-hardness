"""Freeze full new-body/integration review on exact trace and verified prior coverage."""
import json
import hashlib
from pathlib import Path
from prepare_builder02_full95 import OUTPUT
HERE=Path(__file__).parent
BASE=OUTPUT/'consumption-v1/qualification'
OLD=OUTPUT.parent/'full90-material-resource02/consumption-v1/qualification'
PLANNING=Path('C:/Users/dfred/Desktop/Projects/IGH/Quantyra-AI-Planning/docs/research/pvnp')
def sha(data):return hashlib.sha256(data).hexdigest().upper()
def main():
    reuse=json.loads((BASE/'prior-review-reuse-audit.json').read_bytes())
    assert reuse['reuse_identity_eligible'] and len(reuse['unchanged_prior_complete_bodies'])==319
    assert len(reuse['new_or_changed_complete_bodies'])==4 and reuse['shared_native_constant_types_and_edges_unchanged']==7979
    index=json.loads((BASE/'review-sources/source-index.json').read_bytes())
    assert index['project_body_count']==323 and len(index['roots'])==181
    old=json.loads((OLD/'material-integration-v1/manifest.json').read_bytes())
    parent=old['packets'][0];raw=Path(parent['path']).read_bytes();assert sha(raw)==parent['sha256']
    text=b"""FULL95 COMPLETE NEW-BODY AND WHOLE MATERIAL INTEGRATION REVIEW.
These instructions supersede historical FULL90 instructions in the preserved packet below. Current scope is full323 capture, all181 requested profiles, exact181/focused13 trace. All319 prior complete bodies have verified per-lens review provenance and identical bytes, configuration, constant types and proof edges; this permits identity reuse, not a claim of rereading absent files or acceptance of new integration semantics. Inspect every supplied complete body, including all4 NEW sources. The packet supplies67 complete files:44 project and23 Complexitylib, with prior whole-material evidence and reports. Explicitly list inspected/skipped bodies and complete new declarations.
Review the same actual I/copies/U/A/C/T/f and source/star instance. Check m is leaf query count independently of source row count, actual SourceSize appendix dimensions, analyticSourceHeightFloor caller floor, all new height/rank/dimension guards, exact original HC46 inhabitant and named application, and the caller-chosen dyadic exponent without the obsolete k<8m ceiling. Determine whether every new proof and export faithfully consumes the actual definitions and inherited A22/HC46; native GREEN is not semantic or publication acceptance. Audit the exact material RHS, averaging order/normalization and preserved conditional spectral assumption. Do not substitute a selected-leaf surrogate or narrow the input/star scope.
Reconcile the15 prior packet and3 whole integration findings with the new bodies. The appended scalar-calibration and spectral-orbit notes are bounded/author evidence, not Lean certificates or independent review. Useful numeric NO, universal Spectral47, pre-draw selection/table, actual source arity, sampler, robust8S, encoded runtime/reduction/learning and final publication gates remain open until proved. Upstream selected native profiles are not CMMSA bridges. Existing inherited warning debt remains explicit.
No tools, writes, Lean/Lake or subagents. Report declaration-specific severity, evidence, disposition and remaining actions. Separate native/material conditional integration from unconditional theorem or manuscript readiness. Any skipped required body or unresolved HIGH bars overall GO. Inspect all4 complete new bodies before judging; no broad novelty, priority or final manuscript acceptance. End with remaining to-do list.
"""+('\nVERIFIED FULL90 HISTORICAL INTEGRATION PACKET SHA256 '+sha(raw)+'; full required bodies and15 packet/3 whole reports supplied below, without duplicate historical metadata.\n').encode()
    for path in sorted((HERE/'full90-material-review-reports').glob('*.md')):
        receipt=json.loads(path.with_suffix('.json').read_bytes());data=path.read_bytes();assert sha(data)==receipt['report_sha256']
        text+=('\nPRESERVED MATERIAL PACKET REPORT '+path.stem+'\n').encode()+data
    for lens in old['required_lenses']:
        path=HERE/'full90-material-integration-reports'/(lens+'-01.md')
        receipt=json.loads(path.with_suffix('.json').read_bytes());data=path.read_bytes();assert sha(data)==receipt['report_sha256']
        text+=('\nPRESERVED WHOLE MATERIAL REPORT '+lens+'\n').encode()+data
    marker=json.loads((OUTPUT/'launch-once.json').read_bytes())
    native=Path(marker['preflight'])/'qualified-native'/marker['run']/'material-expanded-native-report.json'
    for label,path in [('CURRENT QUALIFIED NATIVE REPORT',native),('CURRENT QUALIFIED TRACE',BASE/'qualification-summary.json'),('EXACT PRIOR BODY AND TYPE/PROOF REUSE AUDIT',BASE/'prior-review-reuse-audit.json')]:
        text+=('\n'+label+' SHA256 '+sha(path.read_bytes())+'\n').encode()+path.read_bytes()
    graphs=json.loads((BASE/'graphs/validated-graphs.json').read_bytes())
    text+=b'\nEXACT CURRENT ROOT SCOPE\n'+json.dumps({k:v['roots'] for k,v in graphs['graphs'].items()}).encode()
    for name in ['cmmsa-conditional-scalar-calibration-2026-10-08.md','cmmsa-append-spectral-orbit-gain-bounded-audit-2026-10-08.md','cmmsa-theorem-citation-scope-audit-2026-10-08.md']:
        data=(PLANNING/name).read_bytes();text+=('\nBOUNDED AUTHOR NOTE '+name+' SHA256 '+sha(data)+'\n').encode()+data
    for row in parent['files']:
        data=(Path(row['source_root'])/row['path']).read_bytes();assert sha(data)==row['sha256'] and len(data)==row['bytes']
        text+=('\n=== COMPLETE PRIOR FILE '+row['source_kind']+' '+row['path']+' SHA256 '+row['sha256']+' ===\n').encode()+data+b'\n=== END COMPLETE PRIOR FILE ===\n'
    rows=list(parent['files']);added={r['path']:r for r in index['project_bodies']}
    for path in reuse['new_or_changed_complete_bodies']:
        row=dict(added[path],source_kind='project',source_root=str(BASE/'review-sources'))
        data=(Path(row['source_root'])/path).read_bytes();assert sha(data)==row['sha256'] and len(data)==row['bytes']
        text+=('\n=== COMPLETE NEW FILE '+path+' SHA256 '+row['sha256']+' ===\n').encode()+data+b'\n=== END COMPLETE NEW FILE ===\n';rows.append(row)
    assert len(rows)==67 and sum(r['source_kind']=='project' for r in rows)==44
    for row in rows:
        data=(Path(row['source_root'])/row['path']).read_bytes();assert sha(data)==row['sha256'] and len(data)==row['bytes']
    assert len(text)<1800000,'Never truncate; revise complete-body context strategy'
    dest=BASE/'material-integration-v1';dest.mkdir();path=dest/'integration.txt';path.write_bytes(text)
    manifest=dict(schema='full95-full181-new-body-and-material-integration-v1',required_lenses=old['required_lenses'],packets=[dict(path=str(path),sha256=sha(text),bytes=len(text),files=rows)],
        prior_complete_project_bodies_identity_eligible=319,new_complete_project_bodies=4,complete_supplied_bodies=67,roots=181,focused=13,full_goal_complete=False,accepted=False,actual_provider_context_fit_verified=False)
    (dest/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8');print(json.dumps({'bytes':len(text),'complete_bodies':67,'new_complete_bodies':4,'sha256':sha(text)}))
if __name__=='__main__':main()
