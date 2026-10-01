import pathlib,json,subprocess,sys
repo=pathlib.Path(__file__).resolve().parents[4]
b=repo/'docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild'
pins=json.loads((b/'analytic-engines-current-pins.json').read_text())
prefix='lean/PvNP/RealizableHardness/'
plan=[('ActualBinaryMatrixHC46','hc46-padding-2AB4FDFA'),('ActualBinaryMatrixHC46Checks','hc46-checks-DA60196A'),('ActualFiniteAppendSpectral47','spectral47-engine-6F6883CC'),('ActualFiniteAppendSpectral47Checks','spectral47-checks-EB96FB36'),('ActualFiniteBinarySurjectionCounting','surjection-counting-10242EF8'),('ActualFiniteBinarySurjectionCountingChecks','surjection-counting-checks-0ACAB9C4')]
target=prefix+plan[-1][0]+'.lean'
args=[sys.executable,str(b/'cmmsa_analytic_gcp_independent_batch.py'),'--source',target,'--expected-sha',pins[target],'--reuse-tag','cmmsa_analytic_20260930T040837Z','--independent-batch']
for name,snapshot in plan:
 source=prefix+name+'.lean'
 args.extend(['--prebuild-source',source])
 if source!=target:args.extend(['--prebuild-snapshot',source+'=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/'+snapshot+'.lean.snapshot'])
for source,pin in pins.items():
 if source!=target:args.extend(['--dependency-source',source,'--dependency-sha',pin])
if '--execute' in sys.argv:args.append('--execute')
sys.exit(subprocess.call(args,cwd=repo))
