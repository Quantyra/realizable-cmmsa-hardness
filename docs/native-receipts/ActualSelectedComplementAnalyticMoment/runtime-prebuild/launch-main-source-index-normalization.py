import json, pathlib, subprocess, sys
repo = pathlib.Path(__file__).resolve().parents[4]
base = repo / 'docs/native-receipts/ActualSelectedComplementAnalyticMoment'
pins = json.loads((base / 'durable-runs/cmmsa_analytic_20260930T172705Z/preparation.json').read_text())['overlay_pins'].copy()
main = 'lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMargin.lean'
target = main.replace('.lean', 'Checks.lean')
high = 'lean/PvNP/RealizableHardness/ActualSelectedHighErrorSignalComparison.lean'
pins[main] = '44E91412EAAFA6E859B635CD6DE5165258F79DBF70A830F4DFF609488A9735CE'
args = [sys.executable, str(base / 'runtime-prebuild/cmmsa_analytic_gcp_durable_prebuild.py'), '--source', target, '--expected-sha', pins[target], '--reuse-tag', 'cmmsa_analytic_20260930T040837Z']
for module in ['ActualSelectedHighErrorAdditiveSignal', 'ActualSelectedHighErrorAdditiveSignalChecks', 'ActualOriginalFailureRowGenericFixedMomentCaller', 'ActualOriginalFailureRowGenericFixedMomentCallerChecks', 'ActualSelectedComplementAnalyticMargin']:
    args.extend(['--prebuild-source', 'lean/PvNP/RealizableHardness/' + module + '.lean'])
args.extend(['--prebuild-snapshot', main + '=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/margin-observed-44E91412.lean.snapshot', '--dependency-snapshot', high + '=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/high-error-557ECCC6.lean.snapshot'])
for source, pin in pins.items():
    if source != target:
        args.extend(['--dependency-source', source, '--dependency-sha', pin])
args.append('--execute')
sys.exit(subprocess.call(args, cwd=repo))
