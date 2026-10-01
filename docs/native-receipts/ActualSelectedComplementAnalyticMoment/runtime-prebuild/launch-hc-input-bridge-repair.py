import pathlib,json,subprocess,sys
repo=pathlib.Path(__file__).resolve().parents[4]
b=repo/'docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild'
pins=json.loads((b/'hc-input-bridge-repair-pins.json').read_text())
prefix='lean/PvNP/RealizableHardness/'
plan=[('ActualBinaryMatrixHC46Derivative','hc46-derivative-144A611E'),('ActualBinaryMatrixHC46DerivativeChecks','bridge-repair-D7709929'),('ActualBinaryMatrixHC46BooleanGlobalness','bridge-repair-165594A6'),('ActualBinaryMatrixHC46BooleanGlobalnessChecks','hc46-globalness-checks-36F10964')]
target=prefix+plan[-1][0]+'.lean'
args=[sys.executable,str(b/'cmmsa_analytic_gcp_independent_batch.py'),'--source',target,'--expected-sha',pins[target],'--reuse-tag','cmmsa_analytic_20260930T040837Z','--independent-batch']
for name,snapshot in plan:
 source=prefix+name+'.lean'
 args.extend(['--prebuild-source',source])
 if source!=target:args.extend(['--prebuild-snapshot',source+'=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/'+snapshot+'.lean.snapshot'])
for source,pin in pins.items():
 if source!=target:args.extend(['--dependency-source',source,'--dependency-sha',pin])
args.extend(['--dependency-snapshot','lean/PvNP/RealizableHardness/ActualFiniteBinarySurjectionCounting.lean=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/surjection-counting-10242EF8.lean.snapshot','--dependency-snapshot','lean/PvNP/RealizableHardness/ActualFiniteBinarySurjectionCountingChecks.lean=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/surjection-counting-checks-0ACAB9C4.lean.snapshot'])

args.extend(['--dependency-snapshot','lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46.lean=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/hc46-padding-D9AD6A98.lean.snapshot'])
args.extend(['--dependency-snapshot','lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46Checks.lean=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/hc46-checks-DA60196A.lean.snapshot'])
args.extend(['--dependency-snapshot','lean/PvNP/RealizableHardness/ActualFiniteAppendSpectral47.lean=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/spectral47-engine-2F08EFD0.lean.snapshot'])
args.extend(['--dependency-snapshot','lean/PvNP/RealizableHardness/ActualFiniteAppendSpectral47Checks.lean=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/spectral47-checks-EB96FB36.lean.snapshot'])
args.extend(['--dependency-snapshot','lean/PvNP/RealizableHardness/ActualFiniteBinaryImageFibres.lean=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/image-fibres-AC8EFE85.lean.snapshot'])
args.extend(['--dependency-snapshot','lean/PvNP/RealizableHardness/ActualFiniteBinaryImageFibresChecks.lean=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/image-fibres-checks-1BF676EF.lean.snapshot'])
if '--execute' in sys.argv:args.append('--execute')
sys.exit(subprocess.call(args,cwd=repo))
