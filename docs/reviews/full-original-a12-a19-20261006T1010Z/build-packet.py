import datetime, hashlib, json, pathlib, re, tarfile

out = pathlib.Path(__file__).resolve().parent
repo = out.parents[2]
planning = pathlib.Path(r'C:/Users/Dan/Desktop/Projects/IGH/Quantyra-AI-Planning')
base = repo / 'docs/a8-gcp/r1007'
capture = base / 'captures/capture-integrated-59'
run = base / 'runs/cmmsa_a8_output_20261006T095324Z_3ea31944'
sha = lambda b: hashlib.sha256(b).hexdigest().upper()
manifest_bytes = (capture / 'manifest.json').read_bytes()
assert sha(manifest_bytes) == '91E390F52A4D3B715B4F97B2977067A550FEA94B49F5DDC423386D9403B7324A'
manifest = json.loads(manifest_bytes)
gate = json.loads((run / 'full-original-a12-a19-native-gates.json').read_text(encoding='utf-8'))
assert gate['full_original_A12_A19_native_gates_green'] is True
assert gate['all_seven_stage_exits'] == [0] * 7
assert not gate['bad_or_missing_axioms'] and not gate['missing_compiled_objects'] and not gate['warning_regressions']
assert set(gate['axiom_profiles']) == set(manifest['requested_axioms'])
assert len(gate['axiom_profiles']) == 68
assert all(set(v) <= {'propext','Classical.choice','Quot.sound'} for v in gate['axiom_profiles'].values())
termination = json.loads((run / 'independent-termination/control/000.stdout').read_text(encoding='utf-8'))
assert termination['status'] == 'TERMINATED'
custody = json.loads((run / 'custody.json').read_text(encoding='utf-8'))
assert custody['before_stop'] is True
archive_sha = '221571B868E8FB0A568FDD942168760A25BC3F216BFCE813A7528C4A4E987106'
assert sha((run / (run.name + '-evidence.tar.gz')).read_bytes()) == archive_sha
assert sha(pathlib.Path(custody['short_path']).read_bytes()) == archive_sha
preflight = (planning / 'docs/research/pvnp/original-a12-a19-review-scope-preflight-2026-10-06.md').read_text(encoding='utf-8')
rows = re.findall(r'^\| (lean/[^|]+?) \| ([A-F0-9]{64}) \|$', preflight, re.M)
assert len(rows) == 92, len(rows)
selected = [p for p, _ in rows]
for extra in ['ActualBinaryMatrixHC46A7HybridW6Transport','ActualBinaryMatrixHC46A11WeightedAggregate']:
    p = 'lean/PvNP/RealizableHardness/' + extra + '.lean'
    if p not in selected: selected.append(p)
assert len(selected) == 94
source_bytes = {}
for p, meta in manifest['project_sources'].items():
    b = (capture / 'inputs' / p).read_bytes()
    assert sha(b) == meta['sha256'], p
    source_bytes[p] = b
assert len(source_bytes) == 217
for p, old in rows:
    assert manifest['project_sources'][p]['sha256'] == old or (p.endswith('/ActualBinaryMatrixHC46A12InfluenceBound.lean') and manifest['project_sources'][p]['sha256'] == '9AAFDAD108BB71735BB14E0033F7B6D37AF08C4D6E9EB9B4211B63B10FD5BAED')

prompt = '''Review the requested lens ONLY as a separate top-level mathematical reviewer.
Use only this provided packet. No tools, source edits, compilation, cloud operations,
delegation, publication, or pseudo tool calls. Write substantive analysis, naming
source/declaration and line or recognizable proof block for each concern. Classify
severity, assumptions, omitted dependencies and trust limits. Finish with exactly
one verdict: GO, GO-WITH-NOTES, NO-GO, or INCOMPLETE. If needed source is omitted,
say INCOMPLETE rather than inventing verification. Do not combine other lens verdicts.

SCOPE: full original arbitrary-complex manuscript A12 and A19, frozen capture59.
Native green is necessary, not mathematical acceptance. Prior A7 is accepted with
notes under its exact prior review lineage; this packet exposes current A7 Q and
normalization plus its accepted allspaces consumer. A16 has no inferred standalone
three-lens acceptance: inspect its complete critical proof path supplied here.

The exact targets to audit are manuscript_A12_actual and manuscript_A19_actual in
ActualBinaryMatrixHC46A12InfluenceBound. A12 must use ONLY rank support <=D and
OriginalActualInfluenceThrough D eta, and prove fourth moment <=2^(103D^2)*eta*second.
A19 must use ONLY rank support <=D and UpToActualNormSqGlobal D eps, and prove
fourth <=2^(114D^2)*eps*second. No Q oracle, current-degree induction premise,
extra A19 influence premise, Boolean shortcut, eta/eps<=1, positive D, ambient-width
or caller complement guard is allowed. Quantifiers include all n,d,D, complex f,
all subspace pairs and bases, D=0, eta=0, eps=0 and degenerate ambient spaces.

Audit Selected frequency pairs <-> ordered flags in range(Y), BOTH inverse laws,
kernel inclusion and range inclusion, rank-zero flags, internal complement choices,
surjective endomorphism-range realization, card(Submodule R)<=2^(rank R)^2,
actual selected-pair bound <=2^(3D^2), not an unrelated DR6 three-frequency count.
Audit all-pair E^2<=eta E, including above-support filter vanishing. Verify actual
normalized linear-map and matrix base means, Parseval and finite Fubini yielding
genuine original Q <=2^(3D^2)*eta*second. Combine accepted original A7 factor100
with count3 exactly to103. No hidden cardinality factor or changed Q definition.

Audit A16's full original-globalness path: canonical flags, original-to-typed bridge,
zero-cost normalized endpoint, below-carrier vanishing, tower energy bound10,
representation by residual-rank projections, orthogonality of distinct residual
ranks even for different preimages, reconstruction and finite energy sum,
(D+1)<=2^(D^2) including D=0, and internally derived parameter nonnegativity.
This yields all actual influences factor11 and then A19 exponent103+11=114.

Lenses: proof-adversarial checks vacuity, hypotheses, both directions, normalization,
exact theorem/manuscript correspondence and critical dependencies. Complexity-theory
checks honest quantifiers and ambient dimensions/exponents, intended original results,
counting and logical force without substituting a weaker theorem. Non-claims-boundary
checks proposed bounded acceptance wording and all limitations against actual results.

PROPOSED WORDING, NOT YET ACCEPTED: original A12/A19 certified with notes after
all three successful separate reviews over these exact bytes. This certifies only
the stated fourth-moment bounds and A16 consumer path. No HC46 inhabitant, LP theorem,
Spectral47, reduction, learning lower bound, P-vs-NP result, or full manuscript
certification, publication or release follows. S3132 remains PARTIAL and S3137
INCOMPLETE. Helper-credit zero for compiler retries and this review gate.

TRUST BOUNDARIES: 94 full project sources supplied; all217 sources exact-indexed.
The 64 omitted A16 umbrella-import sources in the preparation index are not claimed
independently reproved. Their kernel identities are known; inspect whether any is
critical to this milestone. Full accepted A7 proof graph is reused with explicit prior
three-lens lineage, not newly independently reproved. Selected Mathlib projection,
complement and finite-cardinality excerpts are library trust boundaries, not fresh
kernel axioms. All68 fresh profiles use only propext/Classical.choice/Quot.sound.

WARNING POLICY: zero new owned warnings and zero inherited regressions against
exact frozen baseline; inherited981 headers (and cslib header in relevant stages)
remain S3137 debt. Legacy zero-total/parser audit RED is preserved, including its
19 missing-profile parser diagnosis; corrected full gate independently covers all68.
Do not describe inherited warnings as discharged. NEW59 offline assertion incorrectly
expected200 total objects instead of215; failed before cloud launch. Captured harness
was corrected, exactly pinned but not pushed until after execution/termination;
the corrected harness and evidence are now pushed in f1a5895d. A receipt KeyError
was separately repaired with exact two authorized owned successor paths. Raw failures
remain preserved. No proof-source change or restart arose from either receipt repair.

SOURCE FORMAT: each full source below has its exact byte hash and full text. Line
numbers begin at1 per source; excerpts specify original inclusive lines. Text newline
normalization for this packet is explicit; frozen source hashes refer to original bytes.
'''
parts = [prompt, '\n=== Frozen preparation/omission index (historical statuses retained; gates below supersede) ===\n', preflight]
records = []
def add_file(label, p):
    b = p.read_bytes()
    records.append({'label':label,'path':str(p),'sha256':sha(b),'bytes':len(b)})
    parts.append('\n=== ' + label + ' SHA256 ' + sha(b) + ' ===\n' + b.decode('utf-8') + '\n')

compact_gate = dict(gate)
parts += ['\n=== Complete native gate including 217-source identities and all68 profiles ===\n', json.dumps(compact_gate, indent=2)]
parts += ['\n=== Independent termination essential fields ===\n',json.dumps({k:termination.get(k) for k in ['id','name','status','lastStopTimestamp']},indent=2)]
for name in ['custody.json','cache-comparison.json','authorized-successor-preservation.json','settled-native-closeout.md']:
    add_file('Run59 '+name, run/name)
add_file('Run59 raw fresh68 output',run/'remote-evidence/stage-6.stdout')
add_file('Run59 exact declaration-owner/source/signature map',capture/'harness/retry-59/axiom-declaration-owner-map.json.snapshot')
add_file('Preserved offline/receipt failures',base/'retry-59/offline-and-receipt-diagnostics.json')
previous = repo/'docs/reviews/full-original-a11-a7-20261006T0845Z'
for name in ['review-verdicts.json','three-lens-closeout.md']:
    add_file('Accepted original A7/A11 lineage '+name,previous/name)
add_file('Exact comment-only source succession',base/'retry-56/comment-only-succession.md')
for p in selected:
    b = source_bytes[p]
    records.append({'label':'complete critical source','path':p,'sha256':sha(b),'bytes':len(b)})
    parts.append('\n=== COMPLETE SOURCE '+p+' SHA256 '+sha(b)+' ===\n'+b.decode('utf-8')+'\n')

def excerpt(p, ranges, b=None):
    if b is None: b=(repo/p).read_bytes()
    lines=b.decode('utf-8').splitlines()
    records.append({'label':'excerpt','path':p,'full_source_sha256':sha(b),'inclusive_ranges':ranges})
    for start,end in ranges:
        assert end<=len(lines)
        parts.append('\n=== EXCERPT '+p+' FULL SOURCE SHA256 '+sha(b)+' ORIGINAL LINES '+str(start)+'-'+str(end)+' ===\n'+'\n'.join(lines[start-1:end])+'\n')

transfer='lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A7Transfer.lean'
excerpt(transfer,[(1,75),(5320,5368)],source_bytes[transfer])
assert sha((repo/'paper/body.tex').read_bytes()) == '2CE0589F440C091033A8013C5DB1EEF0A07651309755C69CAA185EC45972C97F'
excerpt('paper/body.tex',[(1334,1504)])
package_hashes=json.loads((run/'remote-evidence/package-source-hashes.json').read_text(encoding='utf-8'))
with tarfile.open(run/'remote-evidence/package-sources.tar.gz') as packages:
    for p,ranges in [('.lake/packages/mathlib/Mathlib/LinearAlgebra/Projection.lean',[(135,205)]),('.lake/packages/mathlib/Mathlib/LinearAlgebra/Basis/VectorSpace.lean',[(255,300)]),('.lake/packages/mathlib/Mathlib/LinearAlgebra/FreeModule/Finite/Matrix.lean',[(1,85)])]:
        b=packages.extractfile(p).read()
        assert sha(b)==package_hashes[p],p
        assert (repo/p).read_bytes().decode('utf-8').splitlines()==b.decode('utf-8').splitlines(),p
        excerpt(p,ranges,b)
packet='\n'.join(parts).encode('utf-8')
assert len(packet)<1750000, len(packet)
(out/'common-source-packet.txt').write_bytes(packet)
record={'prepared_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'run':run.name,'manifest_sha256':sha(manifest_bytes),'packet_sha256':sha(packet),'packet_bytes':len(packet),'complete_sources':len(selected),'indexed_sources':len(source_bytes),'complete_source_bytes':sum(len(source_bytes[p]) for p in selected),'input_records':records,'reviewed':False,'accepted':False,'context_fit':'Actual CLI input usage must be retained; byte estimate is not proof of context fit.'}
(out/'packet-manifest.json').write_text(json.dumps(record,indent=2),encoding='utf-8')
print(json.dumps({k:v for k,v in record.items() if k!='input_records'},indent=2))
