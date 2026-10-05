"""Retain exact requested declarations, qualify fresh/profile names by public owners."""
from pathlib import Path
import ast,json,re,hashlib,shutil
HERE=Path(__file__).resolve().parent; PACKAGE=HERE.parent; REPO=PACKAGE.parents[2]
capture=PACKAGE/'captures/capture-integrated-22'; manifest=json.loads((capture/'manifest.json').read_bytes())
owners=['ActualBinaryMatrixHC46A8'+n for n in ['OutputCoordinateTransport','AveragedTransport','AveragedAssembly','EnergyNaturality','PairAssembly','AmbientAssembly','Endpoint']]+['ActualBinaryMatrixHC46A11WeightedAggregate']
decls={}
for owner in owners:
    rel='lean/PvNP/RealizableHardness/'+owner+'.lean'
    data=(capture/'inputs'/rel).read_bytes(); source=data.decode('utf-8')
    namespaces=re.findall(r'^namespace\s+(\S+)',source,re.M); assert namespaces==['PvNP.RealizableHardness.'+owner],namespaces
    for match in re.finditer(r'^\s*(?:(?:noncomputable|protected)\s+)?(?:def|theorem|lemma|abbrev)\s+([A-Za-z_][A-Za-z0-9_\']*)\b',source,re.M):
        name=match.group(1); full=namespaces[0]+'.'+name
        decls.setdefault(name,[]).append({'qualified':full,'owner_file':rel,'owner_capture_sha256':hashlib.sha256(data).hexdigest().upper(),'owner_line':source[:match.start()].count('\n')+1})
rows=[]
for original in manifest['requested_axioms']:
    candidates=decls.get(original.rsplit('.',1)[-1],[])
    if '.' in original: candidates=[x for x in candidates if x['qualified']==original]
    assert len(candidates)==1,(original,candidates)
    rows.append({'original_request':original,**candidates[0]})
assert len(rows)==49 and len({x['qualified'] for x in rows})==49
assert all(any(x['qualified'].endswith('.'+n) for x in rows) for n in ['a11_original_weighted_mixed_bound','a11_original_A7_positive_from_strict_IH','manuscript_A7_actual'])
(HERE/'axiom-declaration-owner-map.json').write_bytes(json.dumps({'basis_capture':'capture-integrated-22','basis_manifest_sha256':hashlib.sha256((capture/'manifest.json').read_bytes()).hexdigest().upper(),'requests':rows,'original_request_count':49,'qualified_request_count':49,'private_or_ambiguous_declarations_rejected':True,'new_acceptance_credit':False},indent=2).encode())
t=(PACKAGE/'retry-22/controller.py').read_text(encoding='utf-8').replace('integrated22_import','integrated23_import').replace('capture-integrated-22','capture-integrated-23').replace('retry-22/','retry-23/').replace('prepare22','prepare23')
line=next(x for x in t.splitlines() if x.strip().startswith('common.REQUESTED_AXIOMS=list('))
replacement=line.replace('common.REQUESTED_AXIOMS=','raw_requests=')+"\n    owner_map=json.loads((HERE/'axiom-declaration-owner-map.json').read_bytes())['requests']\n    assert raw_requests==[row['original_request'] for row in owner_map]\n    common.REQUESTED_AXIOMS=[row['qualified'] for row in owner_map]\n    assert len(common.REQUESTED_AXIOMS)==49 and len(set(common.REQUESTED_AXIOMS))==49"
t=t.replace(line,replacement)
t=t.replace("SCRIPTS = ['retry-23/controller.py',", "SCRIPTS = ['retry-23/axiom-declaration-owner-map.json', 'retry-23/controller.py',")
ast.parse(t); (HERE/'controller.py').write_bytes(t.encode()); (HERE/'control').mkdir()
for n in ['accepted-a9-source.lean.snapshot','accepted-a9-dependency.json']:
    shutil.copyfile(PACKAGE/'retry-22'/n,HERE/n)
(HERE/'author-report.md').write_bytes(b'# Original full A8 plus A11/A7 coherent native successor\n\nSame14 owned modules/215 project closure, exact49 original declarations. Fresh requests and profile keys fully qualified via explicit public declaration-owner mapping (including inherited OutputCoordinateTransport owners). Local opens from Checks are not assumed. Full source and Checks native gates remain; original weighted hS and allspaces finalA7 unchanged. Same accepted A9 exact5B49 source rebuilt; all400 cache pins checked. Strict archive custody and raw nonzero transport receipts retained. No local Lean or helper acceptance.\n')
print('Qualified all49 exact public declaration/profile owners; no duplicate/private match.')
