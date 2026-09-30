import json, pathlib, subprocess, sys

repo = pathlib.Path(__file__).resolve().parents[4]
base = repo / 'docs/native-receipts/ActualSelectedComplementAnalyticMoment'
prior = json.loads((base / 'durable-runs/cmmsa_analytic_20260930T123142Z/preparation.json').read_text())
pins = prior['overlay_pins'].copy()
target = 'lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMarginChecks.lean'
main = 'lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMargin.lean'
high = 'lean/PvNP/RealizableHardness/ActualSelectedHighErrorSignalComparison.lean'
pins[target] = 'BCD2B00CF5D2C7ABBE6A83C35121812210BAF92CFF1B91E7D216144DABC3A111'
pins[main] = '1D8691E8E8C0C9EB6B5F01EA42058CBD175284B7C062C258B93562FB189D21CC'
pins[high] = '557ECCC674D31877E3DCE8D3D6D44DF5DCE91A9CFD78BBE6A5DE8C8967BCC4AE'
args = [sys.executable, str(base / 'runtime-prebuild/cmmsa_analytic_gcp_durable_prebuild.py'), '--source', target, '--expected-sha', pins[target], '--reuse-tag', 'cmmsa_analytic_20260930T040837Z', '--prebuild-source', main, '--prebuild-snapshot', main + '=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/margin-1D8691E8.lean.snapshot', '--dependency-snapshot', high + '=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/high-error-557ECCC6.lean.snapshot']
for source, pin in pins.items():
    if source != target:
        args.extend(['--dependency-source', source, '--dependency-sha', pin])
args.append('--execute')
sys.exit(subprocess.call(args, cwd=repo))
