import os
import pathlib
import subprocess
import tarfile
import tempfile

root = pathlib.Path(__file__).resolve().parents[1]
flags = subprocess.CREATE_NO_WINDOW
gcloud = "gcloud.cmd"
base = [gcloud, "--project", "quantyra-lean-cert-20260915"]
vm = "quantyra-lean-builder-01"
zone = "us-central1-a"
remote = "/tmp/cmmsa-fixed-u-density-r1"

def run(args):
    p = subprocess.run(args, cwd=root, creationflags=flags, capture_output=True, text=True)
    print("COMMAND", args[1:3], "EXIT", p.returncode, flush=True)
    if p.stdout: print(p.stdout[-4000:], flush=True)
    if p.stderr: print(p.stderr[-4000:], flush=True)
    if p.returncode: raise SystemExit(p.returncode)
    return p.stdout

state = run(base + ["compute", "instances", "describe", vm, "--zone", zone,
                    "--format=value(status)"]).strip()
if state == "TERMINATED":
    run(base + ["compute", "instances", "start", vm, "--zone", zone, "--quiet"])
elif state != "RUNNING":
    raise RuntimeError(f"Unexpected VM state: {state}")
fd, archive = tempfile.mkstemp(prefix="cmmsa-fixed-u-", suffix=".tar.gz")
os.close(fd)
try:
    files = subprocess.check_output(["git", "ls-files", "-z"], cwd=root).split(b"\0")
    with tarfile.open(archive, "w:gz") as out:
        for raw in files:
            if not raw: continue
            rel = pathlib.Path(os.fsdecode(raw))
            if rel.parts[0] in ("evidence", "paper", "output", "tmp") or rel.suffix not in (".lean", ".toml", ".json") and rel.name != "lean-toolchain":
                continue
            f = root / rel
            if f.is_file(): out.add(f, arcname=rel.as_posix())
        rel = pathlib.Path("lean/PvNP/RealizableHardness/ActualTaggedFixedUDensityForce.lean")
        out.add(root / rel, arcname=rel.as_posix())
    for attempt in range(3):
        p = subprocess.run(base + ["compute", "scp", archive,
            f"{vm}:/tmp/cmmsa-fixed-u-density-r1.tar.gz", "--zone", zone, "--quiet"],
            cwd=root, creationflags=flags, capture_output=True, text=True)
        print("UPLOAD", attempt + 1, "EXIT", p.returncode, p.stderr[-1000:], flush=True)
        if p.returncode == 0: break
    else:
        raise SystemExit(p.returncode)
    cmd = (f"mkdir -p {remote}/.lake && tar xzf /tmp/cmmsa-fixed-u-density-r1.tar.gz -C {remote} && "
           f"ln -s /home/dfredriksen_quantyra_org/cmmsa-phasea-build-185df9d/.lake/packages {remote}/.lake/packages && "
           f"cd {remote} && nohup sh -c '/home/dfredriksen_quantyra_org/.elan/bin/lake build PvNP.RealizableHardness.ActualTaggedFixedUDensityForce > /tmp/cmmsa-fixed-u-density-r1.log 2>&1; echo $? > /tmp/cmmsa-fixed-u-density-r1.exit' </dev/null >/dev/null 2>&1 & echo PID:$!")
    run(base + ["compute", "ssh", vm, "--zone", zone, "--command", cmd, "--quiet"])
finally:
    os.remove(archive)
