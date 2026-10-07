import subprocess
args = ["gcloud.cmd", "--project", "quantyra-lean-cert-20260915", "compute", "ssh",
        "quantyra-lean-builder-01", "--zone", "us-central1-a", "--quiet",
        "--command", "sha256sum /tmp/cmmsa-fixed-u-density-r1/lean/PvNP/RealizableHardness/ActualTaggedFixedUDensityForce*.lean; cat /tmp/cmmsa-fixed-u-density-r2.exit /tmp/cmmsa-fixed-u-density-r3.exit; pgrep -af 'lake build PvNP.RealizableHardness.ActualTaggedFixedUDensityForce' || true"]
p = subprocess.run(args, creationflags=subprocess.CREATE_NO_WINDOW,
                   capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=120)
print(p.returncode, p.stdout[-30000:].encode("ascii", "backslashreplace").decode(),
      p.stderr[-1000:].encode("ascii", "backslashreplace").decode())
