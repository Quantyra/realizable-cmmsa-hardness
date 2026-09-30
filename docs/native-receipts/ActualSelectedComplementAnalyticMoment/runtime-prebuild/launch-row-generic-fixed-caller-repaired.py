import json, pathlib, subprocess, sys
repo=pathlib.Path(__file__).resolve().parents[4]
base=repo/'docs/native-receipts/ActualSelectedComplementAnalyticMoment'
pins=json.loads((base/'durable-runs/cmmsa_analytic_20260930T165755Z/preparation.json').read_text())['overlay_pins'].copy()
source='lean/PvNP/RealizableHardness/ActualOriginalFailureRowGenericFixedMomentCaller.lean'
target='lean/PvNP/RealizableHardness/ActualOriginalFailureRowGenericFixedMomentCallerChecks.lean'
main='lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMargin.lean'
high='lean/PvNP/RealizableHardness/ActualSelectedHighErrorSignalComparison.lean'
pins[source]='71D83E3D7FB09915ED5BEC3E05EA4553FADEB61EE77F580499FFD32CF18EE9A8'
pins[target]='B8EE0F47746576586AA9B51767103636E3E8EA66D36F01924D97871A6F969B0E'
pins[main]='0CD2626F2143F54976424BE41CD9FB8A51C3AB586F24D3D8A40AE2AF6A32657E'
args=[sys.executable,str(base/'runtime-prebuild/cmmsa_analytic_gcp_durable_prebuild.py'),'--source',target,'--expected-sha',pins[target],'--reuse-tag','cmmsa_analytic_20260930T040837Z','--prebuild-source',source,'--dependency-snapshot',main+'=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/margin-observed-0CD2626F.lean.snapshot','--dependency-snapshot',high+'=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/high-error-557ECCC6.lean.snapshot']
for path,sha in pins.items():
 if path!=target:args.extend(['--dependency-source',path,'--dependency-sha',sha])
args.append('--execute')
sys.exit(subprocess.call(args,cwd=repo))
