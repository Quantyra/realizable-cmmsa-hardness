import subprocess

base = ["gcloud.cmd", "--project", "quantyra-lean-cert-20260915", "compute",
        "ssh", "quantyra-lean-builder-01", "--zone", "us-central1-a"]
cmd = ("cd /tmp/cmmsa-mz-threshold-r1 && rm -rf .lake/build && "
       "nohup sh -c '/home/dfredriksen_quantyra_org/.elan/bin/lake build PvNP.RealizableHardness.ActualTaggedFixedUDensityForceChecks > /tmp/cmmsa-mz-threshold-replay.log 2>&1; echo $? > /tmp/cmmsa-mz-threshold-replay.exit' </dev/null >/dev/null 2>&1 & echo PID:$!")
p = subprocess.run(base + ["--command", cmd, "--quiet"],
                   creationflags=subprocess.CREATE_NO_WINDOW,
                   capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=150)
print(p.returncode, p.stdout[-500:], p.stderr[-300:])
