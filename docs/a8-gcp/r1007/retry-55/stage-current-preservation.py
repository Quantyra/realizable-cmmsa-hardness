"""Stage only enumerated current-turn proof/custody files, preserving exact bytes."""
from pathlib import Path
import subprocess,json,hashlib
REPO=Path(__file__).resolve().parents[4]; PACKAGE=REPO/'docs/a8-gcp/r1007'
roots=['retry-55','captures/capture-integrated-55','runs/cmmsa_a8_output_20261006T081337Z_6df39b3b']
offers=['successor-native-55-a11-warning-repair']
roots+=['retry-16/'+n for n in offers]+['retry-56']
sources=['ActualBinaryMatrixHC46A8AmbientAssembly.lean','ActualBinaryMatrixHC46A8PairAssembly.lean','ActualBinaryMatrixHC46A8AveragedAssembly.lean','ActualBinaryMatrixHC46A8AveragedAssemblyChecks.lean','ActualBinaryMatrixHC46A8AveragedTransport.lean','ActualBinaryMatrixHC46A8EnergyNaturality.lean','ActualBinaryMatrixHC46A8Endpoint.lean','ActualBinaryMatrixHC46A11WeightedAggregate.lean','ActualBinaryMatrixHC46A11WeightedAggregateChecks.lean']
paths=[p.relative_to(REPO).as_posix() for n in roots for p in (PACKAGE/n).rglob('*') if p.is_file()]
paths+=['lean/PvNP/RealizableHardness/'+n for n in sources]
review=json.loads((PACKAGE/'retry-47/completed-review-file-pins.json').read_bytes())['files']
assert len(review)==17 and all(hashlib.sha256((REPO/n).read_bytes()).hexdigest().upper()==h for n,h in review.items())
paths+=list(review)
attrs=REPO/'.gitattributes'; text=attrs.read_text(encoding='utf-8')
for n in roots:
    rule='docs/a8-gcp/r1007/'+n+'/** -text'
    if rule not in text: text+='\n'+rule
for n in sources:
    rule='lean/PvNP/RealizableHardness/'+n+' -text'
    if rule not in text: text+='\n'+rule
for n in review:
    rule=n+' -text'
    if rule not in text: text+='\n'+rule
attrs.write_bytes((text+'\n').encode('utf-8')); paths+=['.gitattributes']
assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=REPO).strip()
spec=PACKAGE/'retry-55/current-stage-pathspec.nul'; spec.write_bytes(b'\0'.join(n.encode() for n in paths)+b'\0'); paths.append(spec.relative_to(REPO).as_posix())
subprocess.run(['git','add','--pathspec-from-file='+str(spec),'--pathspec-file-nul'],cwd=REPO,check=True)
subprocess.run(['git','add','--',str(spec)],cwd=REPO,check=True)
staged=subprocess.check_output(['git','diff','--cached','--name-only','-z'],cwd=REPO).decode().strip('\0').split('\0')
assert set(staged)<=set(paths)
index={x.split('\t',1)[1]:x.split()[1] for x in subprocess.check_output(['git','ls-files','--stage'],cwd=REPO).decode().splitlines()}
for n in staged:
    data=(REPO/n).read_bytes(); blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest(); assert index[n]==blob,n
print(json.dumps({'staged_files':len(staged),'exact_byte_parity':True,'source_sha256':{n:hashlib.sha256((REPO/'lean/PvNP/RealizableHardness'/n).read_bytes()).hexdigest().upper() for n in sources}},indent=2))
