import pathlib,json,hashlib,sys,runpy
repo=pathlib.Path(__file__).resolve().parents[4];b=repo/'docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild'
pins=json.loads((b/'own320-gcp-pins.json').read_text());target='lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A7WeightedPredecessorChecks.lean'
pre=['BinaryMatrixA1Complex','BinaryMatrixFourier','BinaryMatrixA1Phase','BinaryMatrixA1CharacterBridge','ActualBinaryMatrixHC46A7WeightedPredecessor'];prefix='lean/PvNP/RealizableHardness/'
snaps={hashlib.sha256(p.read_bytes()).hexdigest().upper():p for p in (b/'source-snapshots').glob('*.snapshot')}
args=[str(b/'cmmsa_analytic_gcp_independent_batch.py'),'--source',target,'--expected-sha',pins[target],'--reuse-tag','cmmsa_analytic_20260930T040837Z']
for n in pre:args+=['--prebuild-source',prefix+n+'.lean']
for source,h in pins.items():
 if source==target:continue
 args+=['--dependency-source',source,'--dependency-sha',h]
 if h in snaps:args += ['--prebuild-snapshot' if source in [prefix+n+'.lean' for n in pre] else '--dependency-snapshot',source+'='+str(snaps[h].relative_to(repo))]
if '--execute' in sys.argv:args+=['--execute']
sys.argv=args;runpy.run_path(args[0],run_name='__main__')
