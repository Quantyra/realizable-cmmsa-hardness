import subprocess
import sys

BASE = [
    "gcloud.cmd", "compute", "ssh", "quantyra-lean-builder-01",
    "--project=quantyra-lean-cert-20260915", "--zone=us-central1-a",
]

if sys.argv[1] == "launch":
    remote = (
        "mkdir -p /tmp/cmmsa-target-r2 && "
        "tar -xzf /tmp/target-invariant-r2.tar.gz -C /tmp/cmmsa-target-r2 && "
        "mkdir -p /tmp/cmmsa-target-r2/.lake && "
        "ln -s /home/dfredriksen_quantyra_org/cmmsa-phasea-build-185df9d/.lake/packages /tmp/cmmsa-target-r2/.lake/packages && "
        "nohup bash -c 'cd /tmp/cmmsa-target-r2; "
        "/home/dfredriksen_quantyra_org/.elan/bin/lake build "
        "PvNP.RealizableHardness.ActualTaggedTargetPresentationInvariant "
        "> /tmp/cmmsa-target-r2.log 2>&1; "
        "echo $? > /tmp/cmmsa-target-r2.exit' "
        "</dev/null >/tmp/cmmsa-target-r2.nohup 2>&1 & echo PID=$!"
    )
elif sys.argv[1] == "check":
    remote = (
        "if test -f /tmp/cmmsa-target-r2.exit; then "
        "printf 'EXIT='; cat /tmp/cmmsa-target-r2.exit; "
        "tail -n 50 /tmp/cmmsa-target-r2.log; "
        "else ps -eo pid,stat,args | grep '[l]ake build PvNP.RealizableHardness.ActualTaggedTargetPresentationInvariant'; "
        "tail -n 6 /tmp/cmmsa-target-r2.log; fi"
    )
elif sys.argv[1] == "recheck":
    module = (
        sys.argv[2] if len(sys.argv) > 2 else
        "PvNP.RealizableHardness.ActualTaggedTargetPresentationInvariant"
    )
    remote = (
        "cd /tmp/cmmsa-target-r2 && "
        "/home/dfredriksen_quantyra_org/.elan/bin/lake build "
        + module + " "
        "> /tmp/cmmsa-target-r2-recheck.log 2>&1; "
        "result=$?; printf 'EXIT=%s\\n' \"$result\"; "
        "tail -n 35 /tmp/cmmsa-target-r2-recheck.log; exit $result"
    )
elif sys.argv[1] == "status2":
    remote = (
        "ps -eo pid,stat,args | grep '[l]ake build PvNP.RealizableHardness.ActualTaggedComposedPhysicalSampler'; "
        "tail -n 55 /tmp/cmmsa-target-r2-recheck.log"
    )
elif sys.argv[1] == "errors2":
    remote = "grep -n -A 14 'error:' /tmp/cmmsa-target-r2-recheck.log | tail -n 210"
elif sys.argv[1] == "trace2":
    remote = "sed -n '1615,1655p' /tmp/cmmsa-target-r2-recheck.log"
else:
    raise ValueError(sys.argv[1])

p = subprocess.run(
    BASE + ["--command=" + remote],
    creationflags=subprocess.CREATE_NO_WINDOW,
    text=True, encoding="utf-8", errors="replace", capture_output=True, timeout=120,
)
print("returncode", p.returncode)
print(p.stdout[-7000:].encode("ascii", "replace").decode("ascii"))
print(p.stderr[-1200:].encode("ascii", "replace").decode("ascii"))
