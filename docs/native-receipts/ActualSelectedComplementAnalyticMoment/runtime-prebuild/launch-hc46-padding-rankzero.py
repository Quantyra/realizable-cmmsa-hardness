import pathlib,json,subprocess,sys
repo=pathlib.Path(__file__).resolve().parents[4]
b=repo/'docs/native-receipts/ActualSelectedComplementAnalyticMoment'
pins=json.loads((b/'runtime-prebuild/hc46-padding-pins.json').read_text())
main='lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46.lean'
target=main.replace('.lean','Checks.lean')
args=[sys.executable,str(b/'runtime-prebuild/cmmsa_analytic_gcp_durable_prebuild.py'),'--source',target,'--expected-sha',pins[target],'--reuse-tag','cmmsa_analytic_20260930T235043Z','--prebuild-source',main,'--prebuild-snapshot',main+'=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/hc46-padding-231F1DDD.lean.snapshot']
for source,pin in pins.items():
 if source!=target:args.extend(['--dependency-source',source,'--dependency-sha',pin])
args.append('--execute')
sys.exit(subprocess.call(args,cwd=repo))
