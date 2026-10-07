import pathlib
import subprocess

root = pathlib.Path(__file__).resolve().parents[1]
base = ["gcloud.cmd", "--project", "quantyra-lean-cert-20260915", "compute"]
vm = "quantyra-lean-builder-01"
zone = "us-central1-a"
remote = "/tmp/cmmsa-mz-threshold-r1"

def run(args):
    p = subprocess.run(args, cwd=root, creationflags=subprocess.CREATE_NO_WINDOW,
                       capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=150)
    print("EXIT", p.returncode, p.stdout[-800:].encode("ascii", "backslashreplace").decode(),
          p.stderr[-500:], flush=True)
    if p.returncode:
        raise SystemExit(p.returncode)

for name in ("ActualTaggedFixedUDensityForce.lean", "ActualTaggedFixedUDensityForceChecks.lean"):
    run(base + ["scp", str(root / "lean/PvNP/RealizableHardness" / name),
                f"{vm}:{remote}/lean/PvNP/RealizableHardness/{name}",
                "--zone", zone, "--quiet"])
cmd = (f"rm -f /tmp/cmmsa-mz-threshold-r2.exit && cd {remote} && "
       "nohup sh -c '/home/dfredriksen_quantyra_org/.elan/bin/lake build PvNP.RealizableHardness.ActualTaggedFixedUDensityForceChecks > /tmp/cmmsa-mz-threshold-r2.log 2>&1; echo $? > /tmp/cmmsa-mz-threshold-r2.exit' </dev/null >/dev/null 2>&1 & echo PID:$!")
run(base + ["ssh", vm, "--zone", zone, "--command", cmd, "--quiet"])
