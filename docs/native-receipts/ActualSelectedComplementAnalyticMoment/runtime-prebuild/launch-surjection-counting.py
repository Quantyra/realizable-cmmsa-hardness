import pathlib,json,subprocess,sys
repo=pathlib.Path(__file__).resolve().parents[4]
b=repo/'docs/native-receipts/ActualSelectedComplementAnalyticMoment'
pins=json.loads((b/'runtime-prebuild/surjection-counting-pins.json').read_text())
main='lean/PvNP/RealizableHardness/ActualFiniteBinarySurjectionCounting.lean'
target=main.replace('.lean','Checks.lean')
args=[sys.executable,str(b/'runtime-prebuild/cmmsa_analytic_gcp_durable_prebuild.py'),'--source',target,'--expected-sha',pins[target],'--reuse-tag','cmmsa_analytic_20260930T040837Z','--prebuild-source',main,'--prebuild-snapshot',main+'=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/surjection-counting-2A1629B2.lean.snapshot']
for source,pin in pins.items():
 if source!=target:args.extend(['--dependency-source',source,'--dependency-sha',pin])
args.extend(['--dependency-snapshot','lean/PvNP/RealizableHardness/ActualFiniteAppendSpectral47.lean=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/spectral47-engine-E0FF484C.lean.snapshot'])
args.extend(['--dependency-snapshot','lean/PvNP/RealizableHardness/ActualFiniteAppendSpectral47Checks.lean=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/spectral47-checks-EB96FB36.lean.snapshot'])
args.extend(['--dependency-snapshot','lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46.lean=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/hc46-padding-C4638DF7.lean.snapshot'])
args.extend(['--dependency-snapshot','lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46Checks.lean=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/hc46-checks-DA60196A.lean.snapshot'])
args.append('--execute')
sys.exit(subprocess.call(args,cwd=repo))
