import pathlib,json,subprocess,sys
repo=pathlib.Path(__file__).resolve().parents[4]
b=repo/'docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild'
pins=json.loads((b/'force-engines-third-batch-pins.json').read_text())
prefix='lean/PvNP/RealizableHardness/'
plan=[('ActualBinaryMatrixHC46BooleanGlobalness', 'force-repair-A6FB4CA9'), ('ActualBinaryMatrixHC46BooleanGlobalnessChecks', 'hc46-globalness-checks-36F10964'), ('ActualBinaryMatrixHC46FinitePeeling', 'force-repair-C6D9FD46'), ('ActualBinaryMatrixHC46FinitePeelingChecks', 'force-repair-81A27BF3'), ('ActualFiniteAppendSpectral47', 'spectral-image-repair-11BBD1D0'), ('ActualFiniteAppendSpectral47Checks', 'spectral47-checks-EB96FB36'), ('ActualFiniteBinaryImageFibres', 'spectral-image-repair-CDE36CD9'), ('ActualFiniteBinaryImageFibresChecks', 'image-fibres-checks-1BF676EF')]
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
args.extend(['--dependency-snapshot','lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46Derivative.lean=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/hc46-derivative-144A611E.lean.snapshot'])
args.extend(['--dependency-snapshot','lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46DerivativeChecks.lean=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/bridge-repair-D7709929.lean.snapshot'])
if '--execute' in sys.argv:args.append('--execute')
sys.exit(subprocess.call(args,cwd=repo))
