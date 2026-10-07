import pathlib
import subprocess
root = pathlib.Path(__file__).resolve().parents[1]
base = ["gcloud.cmd", "--project", "quantyra-lean-cert-20260915", "compute"]
vm = "quantyra-lean-builder-01"
zone = "us-central1-a"
remote = "/tmp/cmmsa-fixed-u-density-r1"
def run(args):
    p = subprocess.run(args, cwd=root, creationflags=subprocess.CREATE_NO_WINDOW,
                       capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=180)
    print("EXIT", p.returncode, p.stdout[-1000:], p.stderr[-1000:], flush=True)
    if p.returncode: raise SystemExit(p.returncode)
run(base + ["scp", str(root / "lean/PvNP/RealizableHardness/ActualTaggedFixedUDensityForceChecks.lean"),
    f"{vm}:{remote}/lean/PvNP/RealizableHardness/ActualTaggedFixedUDensityForceChecks.lean",
    "--zone", zone, "--quiet"])
cmd = (f"cd {remote}; nohup sh -c '/home/dfredriksen_quantyra_org/.elan/bin/lake build PvNP.RealizableHardness.ActualTaggedFixedUDensityForceChecks > /tmp/cmmsa-fixed-u-density-r3.log 2>&1; echo $? > /tmp/cmmsa-fixed-u-density-r3.exit' </dev/null >/dev/null 2>&1 & echo PID:$!")
run(base + ["ssh", vm, "--zone", zone, "--command", cmd, "--quiet"])
