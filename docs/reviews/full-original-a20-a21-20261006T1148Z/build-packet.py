import pathlib,json,hashlib,datetime,tarfile,re
out=pathlib.Path(__file__).resolve().parent
repo=out.parents[2]
planning=pathlib.Path('C:/Users/Dan/Desktop/Projects/IGH/Quantyra-AI-Planning')
base=repo/'docs/a8-gcp/r1007'
cap=base/'captures/capture-integrated-64'
run=base/'runs/cmmsa_a8_output_20261006T113644Z_145e9858'
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
mb=(cap/'manifest.json').read_bytes()
assert sha(mb)=='4DBAC0F20748D819454288973CC8C5D5926E17AEA497C20650F774966AB3BF0B'
m=json.loads(mb)
g=json.loads((run/'full-original-a20-a21-native-gates.json').read_text())
assert g['full_original_A20_A21_native_gates_green'] and g['all_seven_stage_exits']==[0]*7
assert not g['bad_or_missing_axioms'] and not g['missing_compiled_objects'] and not g['warning_regressions']
assert len(g['axiom_profiles'])==85 and set(g['axiom_profiles'])==set(m['requested_axioms'])
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in g['axiom_profiles'].values())
term=json.loads((run/'independent-termination/control/000.stdout').read_text())
assert term['status']=='TERMINATED' and term['lastStopTimestamp']=='2026-10-06T04:47:05.909-07:00'
custody=json.loads((run/'custody.json').read_text());assert custody['before_stop']
arch='AF87E7754B7BC25C251D689064C1D410BED6D4AAD4E6677DBE3E171E20770EBD'
assert sha((run/(run.name+'-evidence.tar.gz')).read_bytes())==arch
assert sha(pathlib.Path(custody['short_path']).read_bytes())==arch
pre=json.loads((planning/'docs/research/pvnp/original-a20-a21-review-scope-preflight-2026-10-06.json').read_text())
assert pre['successor_captures'][-1]['capture']=='capture-integrated-64'
selected=[s['path'] for s in pre['sources'] if s['proposed_full_text']]
assert len(selected)==128
sources={}
for p,v in m['project_sources'].items():
 b=(cap/'inputs'/p).read_bytes();assert sha(b)==v['sha256'] and len(b)==v['bytes'],p
 sources[p]=b
assert len(sources)==221 and sum(len(sources[p]) for p in selected)==1640404
assert sha(sources['lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A20SquareGlobalness.lean'])=='435873CF57DFD307F6647A8FEFE15B2037922FF3A566787B9DBD5DC157E1B47F'
assert sha(sources['lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A21DyadicMoment.lean'])=='2B3FE7D965919ED6DD930EA4E8BF5A112523365B31B2A65FD08BCE790029330D'
prompt='''Review the REQUESTED LENS ONLY as a separate top-level mathematical reviewer.
Use only this frozen packet. No tools, source edits, compilation, cloud actions,
delegation, publication, or pseudo tool calls. Give substantive analysis with
source/declaration and line or recognizable proof block. Identify assumptions,
normalization, omitted dependencies, trust limits and severity. End with exactly
one verdict: GO, GO-WITH-NOTES, NO-GO, or INCOMPLETE. If needed critical proof
source is missing, say INCOMPLETE rather than inventing verification.

SCOPE: COMPLETE ORIGINAL A20 SQUARE-GLOBALNESS AND A21 ALL-DYADIC MOMENT,
including the full A17/A18 critical dependency proof, frozen Run64/capture64.
Native GREEN is necessary, not mathematical acceptance. Inspect full A18 proof
as newly consumed here: the earlier A12/A19 reviews did NOT accept its final
actual_A18_original_global theorem. A17/A18 are inspected as critical consumers;
no inferred standalone A13-A18 milestone or blanket imported-source acceptance.

A20 targets: a20_three_degree_global, manuscript_A20_raw_fourth_le,
manuscript_A20_square_supportedThrough and manuscript_A20_actual.
ONLY support-through-D and up-to-D actual norm-square globalness with eps may
be caller hypotheses. Derive influences2^(11D^2)*eps from accepted A16/A19 path,
then A18 with r=3D yields B=2^(41D^2)*eps. A raw actual quotient/subspace
restriction of cost<=2D retains degreeD and is up-to-D B-global via exact
outer+inner<=3D composition. A19 gives fourth<=2^(114D^2)*B*second<=
2^(114D^2)*B^2=2^(196D^2)*eps^2. Audit BOTH B factors and normalized carrier,
coordinate and actual-fibre means. Raw restriction commutes with square,
square has support2D, so f*f is actual-global through2D at2^(196D^2)*eps^2.
The raw fourth conclusion is derived, not assumed. No square-global oracle.

A21 target manuscript_A21_actual, arbitrary complex f/all n,d,D/eps,
p>=2 dyadic only, exact lpMoment p(norm f)<=2^(200D^2*p^2)*second*eps^(p/2-1).
Inspect a21_dyadic_strong with ALL dimensions/degree/parameter generalized.
Uniform stronger C_p=200p^2-100p is permitted bookkeeping: p2 exact second
weakened by factor>=1; p4 original A19; q>=4 dyadic uses IH on f*f with degree2D
and A20 parameter. Check4*C_q+196*(q/2-1)+114<=C_(2q), retaining degree factor4,
and1+2*(q/2-1)=(2q)/2-1. Natural subtraction/evenness bounds are internal.
Exact square-moment and square-second identities, coefficient signs and
internally derived eps>=0 must justify every inequality. ZeroD/eps/rows/columns
are included, without positive guards or divisions hiding zero cases. The
uniform proof must derive the ORIGINAL unrestricted result, not merely an
alternate conditional theorem. No A22/Holder bridge was used to prove A21.

A18 new critical proof: full original support and actual influence hypotheses
only, conclusion up-to-r squared-norm globalness2^(10D*r)*eps for every r.
Inspect strict internal degree/order induction; support0 constant and order0
seeds; rank-projection influence inheritance; order-one derivative support drop
and exact A1 normalized nesting; all-space reduced carrier IH. Inspect full
A17 parent estimate, both domain-positive and domainzero/codomain-positive
branches, no caller ambient or complement guard. Check actual affine fibres
are inhabited, smaller-order restrictions use the smaller-r induction rather
than a choice from an empty exact-order family. Audit actual L2 decomposition,
Parseval/orthogonality, top numerical absorption and lower-level geometric sum.
Do not accept a desired-globalness/influence premise masquerading as an IH.

LENSES: proof-adversarial tests vacuity, hypothesis direction, exact normalized
means, both inverse identities, proof dependencies and manuscript correspondence.
Complexity-theory tests allspace quantifiers, exponents, actual original logical
force and consistency with manuscript and accepted reuse. Non-claims-boundary
tests only bounded acceptance wording and every limitation against actual evidence.

PROPOSED WORDING (NOT YET ACCEPTED): original A20/A21 accepted WITH NOTES AT THE
FORMAL-STATEMENT LEVEL after three successful separate reviews of these exact
bytes, including inspected A17/A18 dependency as consumed. Prior original A7/A11
and A12/A19 acceptance WITH NOTES is reused only under its actual source/lineage
and comment-only identities. No general independent reproof of omitted imported
bodies, no HC46 inhabitant, real-q A22/A23, Spectral47, reduction, runtime,
learning lower bound, P-vs-NP, full manuscript certification, publication or release.
S3132 remains PARTIAL, S3137 INCOMPLETE. Compiler/helper credit is zero.

TRUST MAP:128 full critical source bodies, ALL221 current paths/HASHES/bytes
explicitly printed below;93 remaining bodies excluded and marked. Eight groups
of direct imports into supplied bodies are explicitly unprovided. Import absence
alone is not a consumed-lemma proof; inspect whether any is needed. Critical
ActualMZ24HyperplaneSupport and A18DerivativeRankProjection are NOW supplied in
full; no claim they were supplied/reviewed by the previous A12/A19 lens packet.
A7Transfer excerpts cover definitions and actual allspace consumer; full accepted
A7 graph is reused through its actual frozen56 reviews and comment-only succession,
not independently reaccepted here. Standard Mathlib library trust is explicit;
selected excerpts use exact archived CLOUD package bytes, not local line endings.
Missing necessary source must yield INCOMPLETE, not GO by assertion.

WARNINGS/PROVENANCE: zero new owned and inherited-regression warnings under exact
frozen baseline; inherited981/cslib debt remains S3137. Raw generic Run64 audit is
RED from inherited warnings and an old parser omitting17 new/critical profiles;
corrected gate and raw fresh85 independently show complete standard profiles.
The generic controller terminal1 is not a native compile failure and is preserved.
Historical60/61/62/63 source errors and owned warning62 remain raw preserved;
no backdated acceptance or rewriting. First invalid A20 glyph offer was captured
before repair, never cloud-compiled. Local64 receipt generation referenced an
absent top-level owned_sources key, then corrected explicit four new author paths
against project_sources; raw KeyError retained, no proof/capture change/restart.
Current source/Checks, cache400/compiler/package/core, inherited136 and frozen20
identities are preserved. Archive custody BEFORE one idle stop and fresh independent
TERMINATED are required and supplied. Final full certification remains incomplete.

Each COMPLETE SOURCE starts at original line1; frozen hashes identify original
source bytes. Text newline normalization is presentation only. Excerpts state
original inclusive ranges and full CLOUD source hashes. Actual CLI model/context
usage must be recorded; packet byte estimates are not context-fit proof.
'''
parts=[prompt];records=[]
def add(label,p):
 b=p.read_bytes();records.append({'label':label,'path':str(p),'sha256':sha(b),'bytes':len(b)})
 parts.append('\n=== '+label+' SHA256 '+sha(b)+' ===\n'+b.decode('utf-8')+'\n')
parts.append('\n=== COMPLETE CURRENT221 SOURCE HASH/COVERAGE INDEX ===\n')
for p,v in sorted(m['project_sources'].items()):
 parts.append(p+' SHA256 '+v['sha256']+' BYTES '+str(v['bytes'])+' '+('COMPLETE-BODY' if p in selected else 'EXCLUDED-BODY')+'\n')
parts.append('\n=== EXPLICIT UNPROVIDED DIRECT IMPORT EDGE GROUPS ===\n'+json.dumps(pre['unprovided_direct_import_edges'],indent=2))
compact={k:v for k,v in g.items() if k not in ['project_closure','current_capture_owner_identities']}
parts.append('\n=== FULL85 NATIVE GATE (REDUNDANT CLOSURE/OWNER MAP OMITTED; ALL221 HASHES ABOVE) ===\n'+json.dumps(compact,indent=2))
parts.append('\n=== FRESH INDEPENDENT VM TERMINATION ===\n'+json.dumps({k:term.get(k) for k in ['id','name','status','lastStopTimestamp']},indent=2))
for n in ['custody.json','cache-comparison.json','authorized-successor-preservation.json','settled-native-closeout.md']:
 add('Run64 '+n,run/n)
add('Actual raw85 fresh output',run/'remote-evidence/stage-6.stdout')
owner=json.loads((cap/'harness/retry-64/axiom-declaration-owner-map.json.snapshot').read_text())
assert len(owner['requests'])==85
parts.append('\n=== EXACT CURRENT85 REQUEST OWNER MAP (HISTORICAL COPIED SCOPE HEADER NOT AUTHORITATIVE) ===\n')
for row in owner['requests']:
 p=row['owner_file'];assert row['qualified'] in m['requested_axioms']
 parts.append(row['qualified']+' OWNER '+p+' CURRENT_SHA256 '+m['project_sources'][p]['sha256']+'\n')
for folder in ['full-original-a11-a7-20261006T0845Z','full-original-a12-a19-20261006T1010Z']:
 for n in ['review-verdicts.json','three-lens-closeout.md']:
  add('Prior bounded acceptance '+folder+'/'+n,repo/'docs/reviews'/folder/n)
add('Accepted A7 exact comment-only succession',base/'retry-56/comment-only-succession.md')
for p in selected:
 b=sources[p];records.append({'label':'complete critical source','path':p,'sha256':sha(b),'bytes':len(b)})
 parts.append('\n=== COMPLETE SOURCE '+p+' SHA256 '+sha(b)+' ===\n'+b.decode('utf-8')+'\n')
def excerpt(p,ranges,b):
 ls=b.decode('utf-8').splitlines();records.append({'label':'excerpt','path':p,'full_source_sha256':sha(b),'inclusive_ranges':ranges})
 for start,end in ranges:
  assert end<=len(ls)
  parts.append('\n=== EXCERPT '+p+' FULL_SOURCE_SHA256 '+sha(b)+' ORIGINAL_LINES '+str(start)+'-'+str(end)+' ===\n'+'\n'.join(ls[start-1:end])+'\n')
p='lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A7Transfer.lean';excerpt(p,[(1,75),(5320,5368)],sources[p])
p='paper/body.tex';b=(repo/p).read_bytes();assert sha(b)=='2CE0589F440C091033A8013C5DB1EEF0A07651309755C69CAA185EC45972C97F';excerpt(p,[(1334,1536)],b)
ph=json.loads((run/'remote-evidence/package-source-hashes.json').read_text())
with tarfile.open(run/'remote-evidence/package-sources.tar.gz') as t:
 for p,rr in [('.lake/packages/mathlib/Mathlib/LinearAlgebra/Projection.lean',[(135,205)]),('.lake/packages/mathlib/Mathlib/LinearAlgebra/Basis/VectorSpace.lean',[(255,300)]),('.lake/packages/mathlib/Mathlib/LinearAlgebra/FreeModule/Finite/Matrix.lean',[(1,85)]),('.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/ToLin.lean',[(359,407)])]:
  b=t.extractfile(p).read();assert sha(b)==ph[p];excerpt(p,rr,b)
packet='\n'.join(parts).encode('utf-8');assert len(packet)<1950000,len(packet)
assert not (out/'common-source-packet.txt').exists(),'Frozen packet already exists; do not replace.'
(out/'common-source-packet.txt').write_bytes(packet)
rec={'prepared_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'run':run.name,'manifest_sha256':sha(mb),'packet_sha256':sha(packet),'packet_bytes':len(packet),'complete_sources':128,'indexed_sources':221,'excluded_source_bodies':93,'complete_source_bytes':1640404,'input_records':records,'reviewed':False,'accepted':False,'context_fit':'Actual CLI modelUsage must establish fit; bytes are not proof.'}
(out/'packet-manifest.json').write_text(json.dumps(rec,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in rec.items() if k!='input_records'},indent=2))