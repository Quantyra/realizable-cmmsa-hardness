import pathlib
import subprocess

root = pathlib.Path(__file__).resolve().parents[1]
out = root / "evidence/gcp/satellite/gcp_cmmsa_mz_threshold_7a6a104_20260928"
out.mkdir(parents=True, exist_ok=True)
base = ["gcloud.cmd", "--project", "quantyra-lean-cert-20260915", "compute"]
vm = "quantyra-lean-builder-01"
zone = "us-central1-a"
for name in ("cmmsa-mz-threshold-r2.log", "cmmsa-mz-threshold-r2.exit",
             "cmmsa-mz-threshold-replay.log", "cmmsa-mz-threshold-replay.exit"):
    p = subprocess.run(base + ["scp", f"{vm}:/tmp/{name}", str(out / name),
                               "--zone", zone, "--quiet"],
                       creationflags=subprocess.CREATE_NO_WINDOW,
                       capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=150)
    print(name, p.returncode, p.stderr[-350:], flush=True)
    if p.returncode:
        raise SystemExit(p.returncode)
