import pathlib,json,hashlib,subprocess,sys
repo=pathlib.Path(__file__).resolve().parents[4]
b=repo/'docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild'
pins=json.loads((b/'integration-twentieth-pins.json').read_text())
plan=['ActualFiniteDegreeFourierReconstruction', 'ActualFiniteDegreeFourierReconstructionChecks', 'ActualBinaryMatrixHC46A16Energy', 'ActualBinaryMatrixHC46A16EnergyChecks', 'ActualBinaryMatrixHC46TypedFourierTransport', 'ActualBinaryMatrixHC46TypedFourierTransportChecks', 'ActualFiniteDegreeFourierProduct', 'ActualFiniteDegreeFourierProductChecks', 'ActualFiniteAppendGlobalImageEnergy', 'ActualFiniteAppendGlobalImageEnergyChecks', 'ActualFiniteAppendSpectral47ExactInhabitant', 'ActualFiniteAppendSpectral47ExactInhabitantChecks']
pre='lean/PvNP/RealizableHardness/'
target=pre+plan[-1]+'.lean'
snapshots={hashlib.sha256(p.read_bytes()).hexdigest().upper():p for p in (b/'source-snapshots').glob('*.snapshot')}
args=[sys.executable,str(b/'cmmsa_analytic_gcp_independent_batch.py'),'--source',target,'--expected-sha',pins[target],'--reuse-tag','cmmsa_analytic_20260930T040837Z','--independent-batch']
for n in plan:
 source=pre+n+'.lean';args+=['--prebuild-source',source]
 if source!=target:args+=['--prebuild-snapshot',source+'='+str(snapshots[pins[source].upper()].relative_to(repo))]
for source,h in pins.items():
 if source==target:continue
 args+=['--dependency-source',source,'--dependency-sha',h]
 if source not in [pre+n+'.lean' for n in plan] and h.upper() in snapshots:args+=['--dependency-snapshot',source+'='+str(snapshots[h.upper()].relative_to(repo))]
if '--execute' in sys.argv:args+=['--execute']
sys.exit(subprocess.call(args,cwd=repo))
