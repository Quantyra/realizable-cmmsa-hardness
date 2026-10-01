import pathlib,json,subprocess,sys
repo=pathlib.Path(__file__).resolve().parents[4]
b=repo/'docs/native-receipts/ActualSelectedComplementAnalyticMoment'
pins=json.loads((b/'runtime-prebuild/analytic-engines-current-pins.json').read_text())
main='lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46.lean'
target=main.replace('.lean','Checks.lean')
args=[sys.executable,str(b/'runtime-prebuild/cmmsa_analytic_gcp_durable_prebuild.py'),'--source',target,'--expected-sha',pins[target],'--reuse-tag','cmmsa_analytic_20260930T040837Z','--prebuild-source',main,'--prebuild-snapshot',main+'=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/hc46-padding-78790D1A.lean.snapshot']
for source,pin in pins.items():
 if source!=target:args.extend(['--dependency-source',source,'--dependency-sha',pin])
args.extend(['--dependency-snapshot','lean/PvNP/RealizableHardness/ActualFiniteAppendSpectral47.lean=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/spectral47-engine-6F6883CC.lean.snapshot','--dependency-snapshot','lean/PvNP/RealizableHardness/ActualFiniteAppendSpectral47Checks.lean=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/spectral47-checks-EB96FB36.lean.snapshot'])
args.append('--execute')
sys.exit(subprocess.call(args,cwd=repo))
