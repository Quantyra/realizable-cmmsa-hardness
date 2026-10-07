import os
import pathlib
import subprocess
import tarfile
import tempfile

root = pathlib.Path(__file__).resolve().parents[1]
base = ["gcloud.cmd", "--project", "quantyra-lean-cert-20260915", "compute"]
vm = "quantyra-lean-builder-01"
zone = "us-central1-a"
remote = "/tmp/cmmsa-mz-threshold-r1"
flags = subprocess.CREATE_NO_WINDOW

def run(args):
    p = subprocess.run(args, cwd=root, creationflags=flags, capture_output=True,
                       text=True, encoding="utf-8", errors="replace", timeout=180)
    print("EXIT", p.returncode, p.stdout[-1200:], p.stderr[-1200:], flush=True)
    if p.returncode:
        raise SystemExit(p.returncode)
    return p.stdout

state = run(base + ["instances", "describe", vm, "--zone", zone,
                    "--format=value(status)"]).strip()
if state == "TERMINATED":
    run(base + ["instances", "start", vm, "--zone", zone, "--quiet"])
elif state != "RUNNING":
    raise RuntimeError(state)
fd, archive = tempfile.mkstemp(prefix="cmmsa-mz-threshold-", suffix=".tar.gz")
os.close(fd)
try:
    files = subprocess.check_output(["git", "ls-files", "-z"], cwd=root).split(b"\0")
    with tarfile.open(archive, "w:gz") as out:
        for raw in files:
            if not raw:
                continue
            rel = pathlib.Path(os.fsdecode(raw))
            if rel.parts[0] in ("evidence", "paper", "output", "tmp"):
                continue
            if rel.suffix not in (".lean", ".toml", ".json") and rel.name != "lean-toolchain":
                continue
            path = root / rel
            if path.is_file():
                out.add(path, arcname=rel.as_posix())
    run(base + ["scp", archive, f"{vm}:/tmp/cmmsa-mz-threshold-r1.tar.gz",
                "--zone", zone, "--quiet"])
    cmd = (f"mkdir -p {remote}/.lake && tar xzf /tmp/cmmsa-mz-threshold-r1.tar.gz -C {remote} && "
           f"ln -s /home/dfredriksen_quantyra_org/cmmsa-phasea-build-185df9d/.lake/packages {remote}/.lake/packages && "
           f"cd {remote} && nohup sh -c '/home/dfredriksen_quantyra_org/.elan/bin/lake build PvNP.RealizableHardness.ActualTaggedFixedUDensityForceChecks > /tmp/cmmsa-mz-threshold-r1.log 2>&1; echo $? > /tmp/cmmsa-mz-threshold-r1.exit' </dev/null >/dev/null 2>&1 & echo PID:$!")
    run(base + ["ssh", vm, "--zone", zone, "--command", cmd, "--quiet"])
finally:
    os.remove(archive)
