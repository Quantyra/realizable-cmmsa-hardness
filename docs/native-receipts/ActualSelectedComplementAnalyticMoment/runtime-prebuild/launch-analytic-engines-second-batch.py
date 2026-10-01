import pathlib,json,subprocess,sys
repo=pathlib.Path(__file__).resolve().parents[4]
b=repo/'docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild'
pins=json.loads((b/'analytic-engines-second-batch-pins.json').read_text())
prefix='lean/PvNP/RealizableHardness/'
plan=[('ActualBinaryMatrixHC46', 'hc46-padding-D9AD6A98'), ('ActualBinaryMatrixHC46Checks', 'hc46-checks-DA60196A'), ('ActualBinaryMatrixHC46Derivative', 'hc46-derivative-144A611E'), ('ActualBinaryMatrixHC46DerivativeChecks', 'hc46-derivative-checks-19BD3874'), ('ActualBinaryMatrixHC46BooleanGlobalness', 'hc46-globalness-229C3CC0'), ('ActualBinaryMatrixHC46BooleanGlobalnessChecks', 'hc46-globalness-checks-36F10964'), ('ActualFiniteAppendSpectral47', 'spectral47-engine-2F08EFD0'), ('ActualFiniteAppendSpectral47Checks', 'spectral47-checks-EB96FB36'), ('ActualFiniteBinaryImageFibres', 'image-fibres-AC8EFE85'), ('ActualFiniteBinaryImageFibresChecks', 'image-fibres-checks-1BF676EF')]
target=prefix+plan[-1][0]+'.lean'
args=[sys.executable,str(b/'cmmsa_analytic_gcp_independent_batch.py'),'--source',target,'--expected-sha',pins[target],'--reuse-tag','cmmsa_analytic_20260930T040837Z','--independent-batch']
for name,snapshot in plan:
 source=prefix+name+'.lean'
 args.extend(['--prebuild-source',source])
 if source!=target:args.extend(['--prebuild-snapshot',source+'=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/'+snapshot+'.lean.snapshot'])
for source,pin in pins.items():
 if source!=target:args.extend(['--dependency-source',source,'--dependency-sha',pin])
args.extend(['--dependency-snapshot','lean/PvNP/RealizableHardness/ActualFiniteBinarySurjectionCounting.lean=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/surjection-counting-10242EF8.lean.snapshot','--dependency-snapshot','lean/PvNP/RealizableHardness/ActualFiniteBinarySurjectionCountingChecks.lean=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/surjection-counting-checks-0ACAB9C4.lean.snapshot'])
if '--execute' in sys.argv:args.append('--execute')
sys.exit(subprocess.call(args,cwd=repo))
