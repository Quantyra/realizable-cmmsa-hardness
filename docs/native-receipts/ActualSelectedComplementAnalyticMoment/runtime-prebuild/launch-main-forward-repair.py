import json, pathlib, subprocess, sys

repo = pathlib.Path(__file__).resolve().parents[4]
base = repo / 'docs/native-receipts/ActualSelectedComplementAnalyticMoment'
prior = json.loads((base / 'durable-runs/cmmsa_analytic_20260930T123142Z/preparation.json').read_text())
pins = prior['overlay_pins'].copy()
target = 'lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMarginChecks.lean'
main = 'lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMargin.lean'
high = 'lean/PvNP/RealizableHardness/ActualSelectedHighErrorSignalComparison.lean'
pins[target] = 'CF8E63970FD89732C1395A38E6D93C42E965E29B028489FABA3C9FA430A12101'
pins[main] = '1E72ACB2D6F914F11EB2E08BCEC27DBB6A7AD9DC51F89B29D2B91F74AC0965B8'
pins[high] = '557ECCC674D31877E3DCE8D3D6D44DF5DCE91A9CFD78BBE6A5DE8C8967BCC4AE'
pins['lean/PvNP/RealizableHardness/ActualSelectedHighErrorAdditiveSignal.lean'] = 'EF3601C6FF9A4DACE7FBD3B64AE5D7CD461666EB995B0C5E0FE0AC6B3D294C4E'
pins['lean/PvNP/RealizableHardness/ActualSelectedHighErrorAdditiveSignalChecks.lean'] = '3279C65C46676F95F3D1129EEDE791E6DF7C3160FA8C4442FE4777C8710571F3'
args = [sys.executable, str(base / 'runtime-prebuild/cmmsa_analytic_gcp_durable_prebuild.py'), '--source', target, '--expected-sha', pins[target], '--reuse-tag', 'cmmsa_analytic_20260930T040837Z', '--prebuild-source', 'lean/PvNP/RealizableHardness/ActualSelectedHighErrorAdditiveSignal.lean', '--prebuild-source', 'lean/PvNP/RealizableHardness/ActualSelectedHighErrorAdditiveSignalChecks.lean', '--prebuild-source', main, '--prebuild-snapshot', main + '=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/margin-1E72ACB2.lean.snapshot', '--dependency-snapshot', high + '=docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild/source-snapshots/high-error-557ECCC6.lean.snapshot']
for source, pin in pins.items():
    if source != target:
        args.extend(['--dependency-source', source, '--dependency-sha', pin])
args.append('--execute')
sys.exit(subprocess.call(args, cwd=repo))
