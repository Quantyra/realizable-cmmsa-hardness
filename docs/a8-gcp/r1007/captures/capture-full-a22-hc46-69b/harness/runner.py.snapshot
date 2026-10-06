"""Opt-in GCP orchestration. Local subprocesses are process inspection or gcloud only."""
from __future__ import annotations

import base64
import argparse
import json
import re
import shutil
import subprocess
import time
import traceback
import uuid
from datetime import datetime, timezone
from pathlib import Path

from common import (PACKAGE, REPO, CREATE_FLAGS, file_sha, utc, write_new, json_bytes,
                    local_process_check, verify_capture, inherited_now, inherited_status_now)

GCLOUD = r"C:\Users\Dan\AppData\Local\Google\CloudSDKPortable\google-cloud-sdk\bin\gcloud.cmd"
FLAGS = ["--project=quantyra-lean-cert-20260915", "--zone=us-central1-a",
         "--account=dfredriksen@quantyra.org"]
VM = "quantyra-lean-builder-01"
DESCRIBE = ["compute", "instances", "describe", VM,
            "--format=json(name,id,status,zone,machineType,disks,lastStartTimestamp,lastStopTimestamp)"]


def validate_cloud_args(args, authenticated):
    operation = tuple(args[:3])
    if operation in {("compute", "instances", "start"), ("compute", "instances", "stop")}:
        if not authenticated:
            raise RuntimeError("Resource mutation blocked until authenticated TERMINATED preflight succeeds")
        if args[3] != VM:
            raise ValueError("Unexpected GCP mutation target")
    elif operation == ("compute", "instances", "describe"):
        if args[3] != VM:
            raise ValueError("Unexpected GCP inspection target")
    elif args[:2] in [["compute", "scp"], ["compute", "ssh"]]:
        if not authenticated:
            raise RuntimeError("SSH/transfer blocked until authenticated preflight succeeds")
        if args[1] == "ssh" and args[2] != VM:
            raise ValueError("Unexpected SSH target")
        if args[1] == "scp" and not any(value.startswith(VM + ":") for value in args[2:]):
            raise ValueError("Unexpected transfer target")
    else:
        raise ValueError("Local compiler or unapproved cloud operation rejected: " + repr(args))


def render_remote(run_id, manifest):
    if not re.fullmatch(r"cmmsa_a8_output_\d{8}T\d{6}Z_[a-f0-9]{8}", run_id):
        raise ValueError("Invalid immutable run identity")
    replacements = {"@RUN_ID@": run_id,
        "@ARCHIVE_SHA@": manifest["files"]["input-archive.tar.gz"]["sha256"],
        "@CAPTURE_MANIFEST_SHA@": manifest["files"]["inputs/capture-manifest.json"]["sha256"],
        "@WARM_TAG@": manifest["resource_plan"]["reuse_workspace"]}
    if not re.fullmatch(r"cmmsa_analytic_\d{8}T\d{6}Z", replacements["@WARM_TAG@"]):
        raise ValueError("Invalid warm cache identity")
    for key in ["@ARCHIVE_SHA@", "@CAPTURE_MANIFEST_SHA@"]:
        if not re.fullmatch(r"[A-F0-9]{64}", replacements[key]):
            raise ValueError("Invalid immutable archive/manifest hash")
    remote = (PACKAGE / "remote-template.sh").read_text(encoding="utf-8")
    for key, value in replacements.items():
        remote = remote.replace(key, value)
    if re.search(r"@[A-Z_]+@", remote):
        raise ValueError("Unrendered remote script placeholder")
    return remote


class Control:
    def __init__(self, run):
        self.run = run
        self.authenticated = False
        self.records = []

    def cloud(self, args, *, timeout=120, allow_failure=False):
        validate_cloud_args(args, self.authenticated)
        command = [GCLOUD, *args, "--quiet", *FLAGS]
        index = len(self.records)
        record = {"index": index, "argv": command, "started_utc": utc(), "timeout_seconds": timeout}
        start = time.monotonic()
        process = subprocess.Popen(command, cwd=REPO, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   creationflags=CREATE_FLAGS)
        record["local_control_pid"] = process.pid
        stdout = stderr = b""
        timed_out = False
        while True:
            try:
                stdout, stderr = process.communicate(timeout=min(30, max(1, timeout - (time.monotonic() - start))))
                break
            except subprocess.TimeoutExpired:
                if time.monotonic() - start >= timeout:
                    # Observation timeout is never permission to interrupt an active command.
                    timeout += 300
                    print("Observation extended; same GCP command remains active", process.pid, flush=True)
                heartbeat = {"utc": utc(), "command_index": index, "control_pid": process.pid,
                             "elapsed_seconds": round(time.monotonic() - start, 1),
                             "same_command_active": True, "compiler_restarted": False}
                (self.run / "active-handle.json").write_bytes(json_bytes(heartbeat))
                print("Active GCP control", index, "PID", process.pid,
                      "seconds", heartbeat["elapsed_seconds"], flush=True)
        prefix = f"control/{index:03d}"
        write_new(self.run / (prefix + ".stdout"), stdout)
        write_new(self.run / (prefix + ".stderr"), stderr)
        record.update({"finished_utc": utc(), "native_exit": process.returncode,
                       "timed_out": timed_out, "seconds": time.monotonic() - start,
                       "stdout_path": prefix + ".stdout", "stderr_path": prefix + ".stderr",
                       "stdout_sha256": file_sha(self.run / (prefix + ".stdout")),
                       "stderr_sha256": file_sha(self.run / (prefix + ".stderr"))})
        self.records.append(record)
        (self.run / "commands.json").write_bytes(json_bytes(self.records))
        if (process.returncode or timed_out) and not allow_failure:
            raise RuntimeError("GCP command failed; raw control receipt " + prefix)
        return process.returncode, stdout, stderr

    def describe(self):
        code, stdout, _ = self.cloud(DESCRIBE)
        if code:
            raise RuntimeError("Authenticated VM description unavailable")
        value = json.loads(stdout)
        if value.get("name") != VM or str(value.get("id")) != "8337954477286097405" or value.get("zone", "").rsplit("/",1)[-1] != "us-central1-a":
            raise ValueError("Unexpected GCP VM receipt")
        return value

    def settle(self):
        self.cloud(["compute", "instances", "stop", VM, "--async"], allow_failure=True)
        for observation in range(36):
            try:
                state = self.describe()
            except Exception:
                if observation == 35:
                    raise
                time.sleep(10)
                continue
            if state["status"] == "TERMINATED":
                return state
            if observation in {11, 23} and state["status"] == "RUNNING":
                self.cloud(["compute", "instances", "stop", VM, "--async"], allow_failure=True)
            time.sleep(10)
        raise RuntimeError("VM terminal state unproved; retain this handle and continue observation")


def pick_capture(name):
    if name:
        if not re.fullmatch(r"capture-[A-Za-z0-9_-]+", name):
            raise ValueError("Invalid capture selector")
        return PACKAGE / "captures" / name
    captures = sorted(path.parent for path in (PACKAGE / "captures").glob("*/manifest.json"))
    if len(captures) != 1:
        raise ValueError("Specify --capture; expected exactly one complete immutable capture")
    return captures[0]


def execute(capture, manifest):
    process_before = local_process_check()
    inherited = json.loads((capture / "inherited-files-before.json").read_bytes())
    inherited_status = json.loads((capture / "inherited-status-before.json").read_bytes())
    if inherited_now() != inherited or inherited_status_now() != inherited_status:
        raise ValueError("Inherited dirt changed since capture; inspect before executing")
    run_id = "cmmsa_a8_output_" + datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ") + "_" + uuid.uuid4().hex[:8]
    run = PACKAGE / "runs" / run_id
    run.mkdir(parents=True, exist_ok=False)
    for rel in ["runner.py", "audit.py", "common.py"]:
        write_new(run / ("executed-" + rel), (PACKAGE / rel).read_bytes())
    write_new(run / "manifest.json.snapshot", (capture / "manifest.json").read_bytes())
    write_new(run / "invocation.json.snapshot", (capture / "invocation.json").read_bytes())
    archive = run / (run_id + ".tar.gz")
    shutil.copyfile(capture / "input-archive.tar.gz", archive)
    script = run / (run_id + ".sh")
    write_new(script, render_remote(run_id, manifest))
    write_new(run / "request.json", json_bytes({"run": run_id, "capture": capture.name,
        "started_utc": utc(), "manifest_sha256": file_sha(capture / "manifest.json"),
        "archive_sha256": file_sha(archive), "remote_script_sha256": file_sha(script),
        "local_process_check_before": process_before, "compile_host": "GCP VM only",
        "created_resources": [], "automatic_git_writes": False}))
    control = Control(run)
    start_attempted = compiler_attempted = False
    failure = None
    terminal_state = None
    remote_evidence_sha = None
    try:
        initial = control.describe()
        write_new(run / "vm-before.json", json_bytes(initial))
        if str(initial.get("id")) != "8337954477286097405":
            raise RuntimeError("Unexpected instance ID")
        if initial.get("status") != "TERMINATED":
            raise RuntimeError("Existing VM must be TERMINATED; no parallel compiler is launched")
        control.authenticated = True
        start_attempted = True
        control.cloud(["compute", "instances", "start", VM], timeout=300)
        time.sleep(25)
        for probe in range(6):
            code, _, _ = control.cloud(["compute", "ssh", VM, "--tunnel-through-iap", "--command=true"],
                                       timeout=60, allow_failure=True)
            if code == 0:
                break
            if probe == 5:
                raise RuntimeError("VM SSH readiness failed; compiler has not been invoked")
            time.sleep(10)
        _, active, _ = control.cloud(["compute", "ssh", VM, "--tunnel-through-iap", "--command=ps -eo pid,ppid,comm,args | grep -E '[l]ean|[l]ake|[c]loud_capture.py|[c]mmsa_a8_output_.*[.]sh' || true"])
        if active.strip():
            start_attempted = False
            raise RuntimeError("Unexpected active remote run; retain VM unchanged and finish that run first")
        control.cloud(["compute", "scp", str(archive), str(script), VM + ":/tmp/", "--tunnel-through-iap"], timeout=300)
        compiler_attempted = True
        control.cloud(["compute", "ssh", VM, "--tunnel-through-iap",
                       "--command=bash /tmp/" + script.name], timeout=4350)
    except Exception:
        failure = traceback.format_exc()
    finally:
        if start_attempted:
            if compiler_attempted:
                try:
                    remote_path = "/home/dfredriksen_quantyra_org/cmmsa-evidence/" + run_id + "-evidence.tar.gz"
                    local_archive = Path(r"C:\a8gcp") / (run_id[-8:] + ".tar.gz")
                    local_archive.parent.mkdir(parents=True, exist_ok=True)
                    if local_archive.exists(): raise RuntimeError("Short custody path already exists")
                    _, output, _ = control.cloud(["compute", "ssh", VM, "--tunnel-through-iap",
                                                 "--command=sha256sum " + remote_path + "; stat -c %s " + remote_path])
                    remote_evidence_sha = output.decode().splitlines()[0].split()[0].upper()
                    size = int(output.decode().splitlines()[1])
                    block = 4 * 1024 * 1024
                    with local_archive.open("xb") as stream:
                        for index in range((size + block - 1) // block):
                            command = "dd if=" + remote_path + " bs=" + str(block) + " skip=" + str(index) + " count=1 status=none | base64 -w0"
                            _, chunk, _ = control.cloud(["compute", "ssh", VM, "--tunnel-through-iap", "--command=" + command], timeout=120)
                            data = base64.b64decode(chunk, validate=True)
                            if len(data) != min(block, size-index*block): raise ValueError("Archive chunk size mismatch")
                            stream.write(data)
                            print("Preserved archive chunk", index, len(data), flush=True)
                    if size != local_archive.stat().st_size or remote_evidence_sha != file_sha(local_archive):
                        raise ValueError("Downloaded cloud evidence archive hash mismatch")
                    repository_archive = run / (run_id + "-evidence.tar.gz")
                    shutil.copyfile(local_archive, repository_archive)
                    if file_sha(repository_archive) != remote_evidence_sha: raise ValueError("Repository archive hash mismatch")
                    write_new(run / "custody.json", json_bytes({"verified_utc": utc(), "before_stop": True, "short_path": str(local_archive), "repository_path": str(repository_archive), "short_sha256": file_sha(local_archive), "repository_sha256": file_sha(repository_archive), "remote_sha256": remote_evidence_sha}))
                except Exception:
                    failure = (failure or "") + "\nEvidence preservation:\n" + traceback.format_exc()
            try:
                terminal_state = control.settle()
            except Exception:
                failure = (failure or "") + "\nResource settlement:\n" + traceback.format_exc()
        write_new(run / "terminal.json", json_bytes({"run": run_id, "capture": capture.name,
            "finished_utc": utc(), "start_attempted": start_attempted,
            "compiler_attempted": compiler_attempted, "created_resources": [],
            "vm_terminal_receipt": terminal_state, "evidence_archive_sha256": remote_evidence_sha,
            "failure": failure, "local_process_check_after": local_process_check(),
            "inherited_dirt_preserved": inherited_now() == inherited and inherited_status_now() == inherited_status,
            "inherited_preservation_scope": manifest["inherited_preservation_scope"],
            "local_compilation": False, "automatic_git_writes": False}))
    from audit import audit_run
    result = audit_run(capture, run)
    write_new(run / "audit.json", json_bytes(result))
    print(json.dumps({"run": run_id, "green": result["green"], "failures": result["failures"],
                      "vm_terminal_state": result.get("vm_terminal_state")}, indent=2), flush=True)
    return 0 if result["green"] else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--capture")
    parser.add_argument("--execute", action="store_true", help="Start the authenticated GCP run; never writes Git")
    parser.add_argument("--verify-only", action="store_true", help="Offline custody check; no gcloud calls")
    args = parser.parse_args()
    if args.execute and args.verify_only:
        parser.error("--execute and --verify-only are mutually exclusive")
    capture = pick_capture(args.capture)
    manifest = verify_capture(capture)
    if not args.execute:
        print(json.dumps({"capture": capture.name, "status": "PREPARED_OFFLINE", "certified": False,
                          "source_modules": len(manifest["project_sources"]), "gcloud_called": False}, indent=2))
        return 0
    return execute(capture, manifest)


if __name__ == "__main__":
    raise SystemExit(main())
