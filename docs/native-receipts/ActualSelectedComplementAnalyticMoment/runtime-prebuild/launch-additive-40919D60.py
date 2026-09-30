import json, pathlib, subprocess, sys

repo = pathlib.Path(__file__).resolve().parents[4]
base = repo / 'docs/native-receipts/ActualSelectedComplementAnalyticMoment'
prior = json.loads((base / 'durable-runs/cmmsa_analytic_20260930T130802Z/preparation.json').read_text())
pins = prior['overlay_pins'].copy()
pins['lean/PvNP/RealizableHardness/ActualSelectedHighErrorAdditiveSignal.lean'] = '40919D60EADEF876196B2142B458F09112E574B2AD48B5FB7F763F893205D07D'
target = 'lean/PvNP/RealizableHardness/ActualSelectedHighErrorAdditiveSignalChecks.lean'
main = 'lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMargin.lean'
high = 'lean/PvNP/RealizableHardness/ActualSelectedHighErrorSignalComparison.lean'
additive = 'lean/PvNP/RealizableHardness/ActualSelectedHighErrorAdditiveSignal.lean'
args = [sys.executable, str(base / 'runtime-prebuild/cmmsa_analytic_gcp_durable_prebuild.py'), '--source', target, '--expected-sha', pins[target], '--reuse-tag', 'cmmsa_analytic_20260930T040837Z', '--prebuild-source', additive, '--dependency-snapshot', main + '=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/margin-5535E33D.lean.snapshot', '--dependency-snapshot', high + '=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/high-error-557ECCC6.lean.snapshot']
for source, pin in pins.items():
    if source != target:
        args.extend(['--dependency-source', source, '--dependency-sha', pin])
args.append('--execute')
sys.exit(subprocess.call(args, cwd=repo))
