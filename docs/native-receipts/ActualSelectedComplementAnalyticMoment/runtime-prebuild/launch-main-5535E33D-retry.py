import json, pathlib, subprocess, sys

repo = pathlib.Path(__file__).resolve().parents[4]
base = repo / 'docs/native-receipts/ActualSelectedComplementAnalyticMoment'
prior = json.loads((base / 'durable-runs/cmmsa_analytic_20260930T123142Z/preparation.json').read_text())
pins = prior['overlay_pins'].copy()
target = 'lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMarginChecks.lean'
main = 'lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMargin.lean'
high = 'lean/PvNP/RealizableHardness/ActualSelectedHighErrorSignalComparison.lean'
pins[target] = 'BCD2B00CF5D2C7ABBE6A83C35121812210BAF92CFF1B91E7D216144DABC3A111'
pins[main] = '5535E33DFD3F31782155653148621B6E35FB78230CAE48F6624338FB629431F5'
pins[high] = '557ECCC674D31877E3DCE8D3D6D44DF5DCE91A9CFD78BBE6A5DE8C8967BCC4AE'
pins['lean/PvNP/RealizableHardness/ActualSelectedHighErrorAdditiveSignal.lean'] = '6E5472AD41B491D53AAB4EDCBB01EA32C5795E3AA3D6F804755582FA85ECF338'
pins['lean/PvNP/RealizableHardness/ActualSelectedHighErrorAdditiveSignalChecks.lean'] = '3279C65C46676F95F3D1129EEDE791E6DF7C3160FA8C4442FE4777C8710571F3'
args = [sys.executable, str(base / 'runtime-prebuild/cmmsa_analytic_gcp_durable_prebuild.py'), '--source', target, '--expected-sha', pins[target], '--reuse-tag', 'cmmsa_analytic_20260930T040837Z', '--prebuild-source', main, '--prebuild-snapshot', main + '=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/margin-5535E33D.lean.snapshot', '--dependency-snapshot', high + '=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/high-error-557ECCC6.lean.snapshot']
for source, pin in pins.items():
    if source != target:
        args.extend(['--dependency-source', source, '--dependency-sha', pin])
args.append('--execute')
sys.exit(subprocess.call(args, cwd=repo))
