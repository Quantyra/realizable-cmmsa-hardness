"""Prepare exact frozen full A11/A7 review inputs; never launch a review."""
from pathlib import Path
import json, hashlib, ast
REPO=Path(__file__).resolve().parents[4]
P=REPO/'docs/a8-gcp/r1007'
cap=P/'captures/capture-integrated-56'
run=P/'runs/cmmsa_a8_output_20261006T083408Z_44012904'
out=REPO/'docs/reviews/full-original-a11-a7-20261006T0845Z'
assert not out.exists()
gate=json.loads((run/'full-original-a11-native-gates.json').read_bytes())
assert gate['full_original_A11_native_gates_green'] and not gate['warning_regressions']
manifest=json.loads((cap/'manifest.json').read_bytes())
old=json.loads((REPO/'docs/reviews/full-original-a8-20261006T0316Z/scope.json').read_bytes())
selected=list(old['selected_sources'])
for name in ['ActualBinaryMatrixHC46A11WeightedAggregate.lean','ActualBinaryMatrixHC46A11WeightedAggregateChecks.lean','ActualBinaryMatrixHC46A9AmbientReindex.lean']:
    selected.append('lean/PvNP/RealizableHardness/'+name)
selected=list(dict.fromkeys(selected))
sha=lambda data:hashlib.sha256(data).hexdigest().upper()
sources={}
for name in selected:
    data=(cap/'inputs'/name).read_bytes()
    assert sha(data)==manifest['project_sources'][name]['sha256'].upper()
    sources[name]={'sha256':sha(data),'bytes':len(data)}
assert any(n.endswith('ActualBinaryMatrixHC46A7HybridW6Transport.lean') for n in selected)
paper=REPO/'paper/body.tex'; paperdata=paper.read_bytes(); lines=paperdata.decode('utf-8').splitlines(keepends=True)
ranges=[(999,1050),(1261,1337)]
excerpt=''.join('\nMANUSCRIPT paper/body.tex lines '+str(a)+'-'+str(b)+'\n'+''.join(lines[a-1:b]) for a,b in ranges)
targets=['a11_original_weighted_mixed_bound','a11_original_A7_positive_from_strict_IH','manuscript_A7_actual']
intro='''Review the full ORIGINAL weighted A11 hS and allspaces A7 milestone only, against the actual manuscript excerpts below. This is a separate review for the requested lens. Native kernel/source/Checks/axiom gates are green but do not substitute for mathematical or claims-boundary review. The three targets are a11_original_weighted_mixed_bound, a11_original_A7_positive_from_strict_IH, and manuscript_A7_actual in PvNP.RealizableHardness.ActualBinaryMatrixHC46A11WeightedAggregate. Review their EXACT general hypotheses and actual quantities. The hS target assumes positive D, original Fourier support, and legitimate strict simultaneous induction for every smaller degree on all finite spaces, with factor 2^(100*(D-t)^2); final manuscript_A7_actual must discharge induction and retain only the stated support hypothesis. No desired aggregate, desired equality, oracle, support-window conclusion or current-degree induction may be hidden as an assumption.

Audit canonical global initial/source bijections BOTH inverse directions; positive initial restriction and rank/cost recovery; original A8 output-Q actual ambient final-map transport; actual A9 fiber partition/count; complementary vanishing proving full a+b+k<=D support window; A10 saved exponent (full saving theorem is inside supplied A11 source); complete finite i/j geometric tails, including k=0 exclusion of i=j=0 only for the positive initial aggregate; rank-zero/all-Y inclusion when enlarging to the same-D W6 bound; original normalized averages and squared energies, no termwise fourth-power identity or lost factor; original A6 constant162, 24Dt, 100D^2, 1-31D and allspaces strong induction. Full actual A9AmbientReindex and A7HybridW6Transport sources are supplied. The manuscript A8 includes the strict-IH factor; the previously accepted A8 output-Q transport alone did not establish that full analytic claim. The present A11 consumer is responsible for that factor and complete weighted aggregation.

Inherited warning debt is recorded; zero new owned or inherited warning headers are required and observed. Diagnostic marked source is separate, never a proof owner or acceptance gate. Read only original frozen capture56 source below. The generic historical controller audit RED is preserved: its old four-stage/profile parser omitted23 A11 profiles and treated inherited warnings as failures; the explicit current eight-stage/full49 gate and raw evidence are authoritative. Do not infer universal HC46/Spectral47, pseudorandomness/Lp contract, outward/star construction, encoded reduction/runtime, hardness/learning or P-vs-NP/full manuscript certification from this milestone. Helper credit remains zero/count2.

Use only provided text. No tools, edits, compilation, cloud commands, delegation or publication. Other dependencies are exact indexed kernel inputs, not all independently re-proved in this bounded packet. If omissions prevent a verdict, return INCOMPLETE naming needed files. Provide substantive lens-specific analysis, absolute file/declaration and line references, blocking severity, explicit assumptions/limits, and a final verdict exactly GO, GO-WITH-NOTES, NO-GO or INCOMPLETE. Do not combine other lens verdicts.
'''
closure={n:manifest['project_sources'][n] for n in gate['project_closure']}
scope={'capture':str(cap),'run':str(run),'manifest_sha256':sha((cap/'manifest.json').read_bytes()),'input_archive_sha256':'165E4A7F97D2B3C4FE1D910DD62FB972EAAB9CEFF9B7358EEBFC5185E062E6D0','selected_sources':selected,'selected_source_identities':sources,'project_closure_index':closure,'targets':targets,'original_requested_axioms':49,'current_capture_owner_identities':gate['current_capture_owner_identities'],'manuscript':{'path':str(paper),'sha256':sha(paperdata),'line_ranges':ranges,'excerpt_sha256':sha(excerpt.encode())},'accepted':False,'reviews_launched':False,'helper_credit':0,'diagnostic_excluded':True,'scope':'Genuine original weighted hS, strict allspaces IH and final manuscript A7; no full manuscript certification'}
parts=[intro,'\nFULL ORIGINAL NATIVE GATE REPORT\n',json.dumps(gate,indent=2),'\nRESOURCE AND BYTE CUSTODY\n']
for name in ['custody.json','cache-comparison.json','authorized-successor-preservation.json','independent-termination/receipt.json']:
    parts+=['\n'+name+'\n',(run/name).read_text(encoding='utf-8')]
parts+=['\nEXACT PROJECT CLOSURE INDEX\n',json.dumps(closure,indent=2),'\nACTUAL MANUSCRIPT EXCERPTS\n',excerpt]
for name in selected:
    parts+=['\nFULL FROZEN SOURCE '+str(REPO/name)+' SHA256 '+sources[name]['sha256']+'\n',(cap/'inputs'/name).read_text(encoding='utf-8')]
packet=''.join(parts).encode('utf-8')
assert len(packet)<2000000
scope['packet_sha256']=sha(packet);scope['packet_bytes']=len(packet)
out.mkdir(parents=True)
(out/'common-source-packet.txt').write_bytes(packet)
(out/'scope.json').write_bytes(json.dumps(scope,indent=2).encode())
(out/'manuscript-excerpt.txt').write_bytes(excerpt.encode())
wrapper=(REPO/'docs/reviews/full-original-a8-20261006T0316Z/run-review.py').read_text(encoding='utf-8').replace('Full original A8 milestone; frozen46 packet','Full original weighted A11 hS and allspaces A7 milestone; frozen56 packet')
ast.parse(wrapper)
(out/'run-review.py').write_bytes(wrapper.encode())
print(json.dumps({'review_dir':str(out),'full_sources':len(selected),'packet_bytes':len(packet),'packet_sha256':sha(packet),'reviews_launched':False},indent=2))
