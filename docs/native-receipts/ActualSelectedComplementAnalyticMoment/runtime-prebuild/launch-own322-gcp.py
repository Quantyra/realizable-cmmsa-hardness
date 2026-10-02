import pathlib,json,hashlib,sys,runpy
repo=pathlib.Path(__file__).resolve().parents[4];b=repo/'docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild'
pins=json.loads((b/'own320-gcp-pins.json').read_text());target='lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A7WeightedPredecessorChecks.lean'
pre=['ActualBinaryMatrixHC46A7WeightedPredecessor'];prefix='lean/PvNP/RealizableHardness/'
snaps={hashlib.sha256(p.read_bytes()).hexdigest().upper():p for p in (b/'source-snapshots').glob('*.snapshot')}
args=[str(b/'cmmsa_analytic_gcp_independent_batch.py'),'--source',target,'--expected-sha',pins[target],'--reuse-tag','cmmsa_analytic_20260930T040837Z']
for n in pre:args+=['--prebuild-source',prefix+n+'.lean']
for source,h in pins.items():
 if source==target:continue
 args+=['--dependency-source',source,'--dependency-sha',h]
 if h in snaps:args += ['--prebuild-snapshot' if source in [prefix+n+'.lean' for n in pre] else '--dependency-snapshot',source+'='+str(snaps[h].relative_to(repo))]
args+=['--direct-development']
args+=['--required-object-pin','.lake/build/lib/lean/PvNP/RealizableHardness/BinaryMatrixA1Complex.olean=7f1cbe43d6dad3c90d41b14ac3abab3fae85ccb401c3026e8587784854a50a3e']
args+=['--required-object-pin','.lake/build/lib/lean/PvNP/RealizableHardness/BinaryMatrixFourier.olean=a87215154de73ced8b9edc008074561239b38db1312ed61fd7a5bbd764e9e240']
args+=['--required-object-pin','.lake/build/lib/lean/PvNP/RealizableHardness/BinaryMatrixA1Phase.olean=9cd44a284d173a1b07367efde328aa4901423380f1bdf008e83fe5a2fac52fc1']
args+=['--required-object-pin','.lake/build/lib/lean/PvNP/RealizableHardness/BinaryMatrixA1CharacterBridge.olean=9d44d90306fda842a351b7468527ad38d5014548c164d259722ce8c4711d2fc3']
if '--execute' in sys.argv:args+=['--execute']
sys.argv=args;runpy.run_path(args[0],run_name='__main__')
