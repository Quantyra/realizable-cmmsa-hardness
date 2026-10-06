"""Offline immutable capture only. No Lean/Lake execution or gcloud calls."""
from __future__ import annotations

import argparse
import ast
import gzip
import io
import json
import re
import subprocess
import tarfile
from datetime import datetime, timezone

from common import (PACKAGE, REPO, SOURCE, CHECKS, REPORT, FROZEN, CLAIM,
                    REQUESTED_AXIOMS, CREATE_FLAGS, file_sha, sha, utc, write_new,
                    json_bytes, imports, forbidden_tokens, local_process_check,
                    inherited_now, inherited_status_now)

BASELINE = REPO / "docs/a7-certification-20261003/a9-gcp/cmmsa_analytic_20261004T002601Z/remote-evidence"
SCRIPTS = ['retry-65/current-warning-baseline.json', 'retry-65/current-dependency-pins.json', 'retry-65/axiom-declaration-owner-map.json', 'retry-65/controller.py', 'retry-65/cloud_capture.snapshot.py', 'retry-65/adapted-prepare.snapshot.py', 'common.py', 'prepare.py', 'runner.py', 'audit.py', 'cloud_capture.py', 'remote-template.sh', 'setup-diagnostic.py', 'README.md', 'warning-baseline-seal.json', 'workflow-protocol.snapshot']
BASELINE_FILES = ["package-sources.tar.gz", "core-sources.tar.gz", "package-source-hashes.json",
                  "core-source-hashes.json", "package-identities.json", "compiler-identity.json",
                  "toolchain.txt", "package-object-before.sha256", "core-object-before.sha256"]


def git(*args):
    return subprocess.check_output(["git", *args], cwd=REPO, creationflags=CREATE_FLAGS)

def dependency_bytes(rel):
    prior = PACKAGE.with_name("r1005") / "captures/capture-candidate2"
    pins = json.loads((prior / "manifest.json").read_bytes())["project_sources"]
    if rel in pins:
        data = (prior / "inputs" / rel).read_bytes()
        if sha(data) != pins[rel]["sha256"]:
            raise ValueError("Retained r1005 dependency custody failed: " + rel)
        return data, "r1005 retained dependency closure (exact manifest-pinned bytes)"
    return git("show", "HEAD:" + rel), "HEAD (not in r1005 closure)"


def check_source_archive(archive, hashes):
    with tarfile.open(archive, "r:gz") as stream:
        seen = set()
        for member in stream:
            if not member.isfile():
                continue
            name = member.name
            if name not in hashes or name in seen:
                raise ValueError("Dependency source archive membership drift: " + name)
            seen.add(name)
            if sha(stream.extractfile(member).read()) != hashes[name].upper():
                raise ValueError("Dependency source archive hash mismatch: " + name)
        if seen != set(hashes):
            raise ValueError("Dependency source archive membership drift")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--name", help="Unique capture directory name; existing captures are never overwritten")
    parser.add_argument("--repair-from-run", help="Retained failed GCP run authorizing an owned successor capture")
    args = parser.parse_args()
    name = args.name or ("capture-" + datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ"))
    if not re.fullmatch(r"capture-[A-Za-z0-9_-]+", name):
        raise ValueError("Invalid capture name")
    processes = local_process_check()
    if git("diff", "--cached", "--name-only").strip():
        raise RuntimeError("Index contains changes; capture will not alter it")
    offered = {rel: file_sha(REPO / rel) for rel in FROZEN}
    if any(offered[rel] != expected for rel, expected in FROZEN.items() if rel not in {SOURCE, CHECKS, REPORT}):
        raise ValueError("Frozen dependency drift; owned repairs cannot change dependencies")
    if offered != FROZEN and not args.repair_from_run:
        raise ValueError("Owned successor requires --repair-from-run with captured GCP diagnostics")
    basis = None
    if args.repair_from_run:
        if not re.fullmatch(r"cmmsa_a8_output_\d{8}T\d{6}Z_[a-f0-9]{8}", args.repair_from_run):
            raise ValueError("Invalid repair-basis run identity")
        prior_run = PACKAGE / "runs" / args.repair_from_run
        prior_audit = json.loads((prior_run / "audit.json").read_bytes())
        prior_terminal = json.loads((prior_run / "terminal.json").read_bytes())
        if (prior_audit["green"] or prior_terminal["vm_terminal_receipt"]["status"] != "TERMINATED"
                or not prior_terminal["compiler_attempted"]):
            raise ValueError("Successor requires a failed, preserved, terminated GCP attempt")
        if file_sha(prior_run / (prior_run.name + "-evidence.tar.gz")) != prior_terminal["evidence_archive_sha256"]:
            raise ValueError("Repair-basis cloud evidence archive custody failed")
        basis = {"run": prior_run.name, "capture": prior_terminal["capture"],
                 "cloud_evidence_archive_sha256": prior_terminal["evidence_archive_sha256"],
                 "reason": "Owned proof repair based solely on retained GCP stage diagnostics",
                 "changed_owned_files": sorted(rel for rel in offered if offered[rel] != FROZEN[rel])}
    for script in SCRIPTS:
        if script.endswith(".py"):
            ast.parse((PACKAGE / script).read_text(encoding="utf-8"), filename=script)
    capture = PACKAGE / "captures" / name
    capture.mkdir(parents=True, exist_ok=False)
    files = {}

    def save(rel, data):
        write_new(capture / rel, data)
        files[rel] = {"sha256": sha(data), "bytes": len(data)}

    for script in SCRIPTS:
        save("harness/" + script + ".snapshot", (PACKAGE / script).read_bytes())
    if basis:
        for original, destination in [("manifest.json.snapshot", "manifest.json"),
                                      ("terminal.json", "terminal.json"), ("audit.json", "audit.json")]:
            save("repair-basis/" + destination, (prior_run / original).read_bytes())
        for index in range(4):
            for suffix in ["stdout", "stderr", "native-exit", "command.json"]:
                diagnostic_name = f"stage-{index}.{suffix}"
                save("repair-basis/" + diagnostic_name, (prior_run / "remote-evidence" / diagnostic_name).read_bytes())


    save("status-before.txt", git("status", "--porcelain=v1", "--untracked-files=normal"))
    save("inherited-tracked-diff-before.patch", git("diff", "--binary", "HEAD", "--"))
    inherited = inherited_now()
    save("inherited-files-before.json", json_bytes(inherited))
    inherited_status = inherited_status_now()
    save("inherited-status-before.json", json_bytes(inherited_status))
    heads = {"head": git("rev-parse", "HEAD").decode().strip(),
             "branch": git("branch", "--show-current").decode().strip(),
             "origin_url": git("remote", "get-url", "origin").decode().strip(),
             "origin_main": git("rev-parse", "origin/main").decode().strip(),
             "staged_paths": []}
    save("heads-before.json", json_bytes(heads))
    records = {}
    external = set()
    visiting = set()
    order = []

    def visit(module):
        rel = "lean/" + module.replace(".", "/") + ".lean"
        if rel in records:
            return
        if module in visiting:
            raise ValueError("Project import cycle: " + module)
        path = REPO / rel
        if not path.is_file():
            if module.startswith("PvNP."):
                raise ValueError("Missing project dependency: " + module)
            external.add(module)
            return
        visiting.add(module)
        data, basis = (candidate_bytes(rel), "exact immutable author-offer overlay; mutable successor separate") if rel in OWNED else dependency_bytes(rel)
        text = data.decode("utf-8", errors="strict")
        if any(marker in text for marker in ["\ufffd", "\u00c3", "\u00c2", "\u00e2\u20ac"]):
            raise ValueError("Mojibake marker: " + rel)
        if data.startswith(b"\xef\xbb\xbf"):
            raise ValueError("UTF-8 BOM: " + rel)
        deps = imports(data)
        for dep in deps:
            visit(dep)
        visiting.remove(module)
        save("inputs/" + rel, data)
        records[rel] = {"sha256": sha(data), "bytes": len(data), "imports": deps, "basis": basis,
                        "forbidden_tokens": forbidden_tokens(data)}
        order.append(module)

    for rel in OWNED:
        visit(rel.removeprefix("lean/").removesuffix(".lean").replace("/", "."))
    for rel in OWNED:
        if records[rel]["forbidden_tokens"]:
            raise ValueError("Forbidden target token: " + rel)
    save("source.lean.snapshot", (REPO / SOURCE).read_bytes())
    save("checks.lean.snapshot", (REPO / CHECKS).read_bytes())
    save("author-report.md.snapshot", (REPO / REPORT).read_bytes())
    configs = {}
    for rel in ["lakefile.toml", "lake-manifest.json", "lean-toolchain"]:
        data = (REPO / rel).read_bytes()
        canonical = git("show", "HEAD:" + rel)
        if data.replace(b"\r\n", b"\n") != canonical.replace(b"\r\n", b"\n"):
            raise ValueError("Unreviewed configuration drift: " + rel)
        save("inputs/" + rel, data)
        configs[rel] = {"sha256": sha(data), "head_sha256": sha(canonical),
                        "normalized_equal": True}
    for rel in BASELINE_FILES:
        save("dependency-baseline/" + rel, (BASELINE / rel).read_bytes())
    baseline_counts = {}
    external_paths = set()
    for prefix in ["package", "core"]:
        hashes = json.loads((capture / f"dependency-baseline/{prefix}-source-hashes.json").read_bytes())
        check_source_archive(capture / f"dependency-baseline/{prefix}-sources.tar.gz", hashes)
        baseline_counts[prefix] = len(hashes)
        external_paths.update(hashes)
    for module in external:
        if not any(path.endswith("/" + module.replace(".", "/") + ".lean") for path in external_paths):
            raise ValueError("External direct import absent from source baseline: " + module)
    lake_manifest = json.loads((capture / "inputs/lake-manifest.json").read_bytes())
    revisions = json.loads((capture / "dependency-baseline/package-identities.json").read_bytes())
    if any(revisions.get(row["name"]) != row["rev"] for row in lake_manifest["packages"]):
        raise ValueError("External source baseline package revision drift")
    save("inputs/cloud_capture.py", (PACKAGE / "retry-65/cloud_capture.snapshot.py").read_bytes())
    stages=STAGES
    save('inputs/fresh-integrated-axioms.lean', FRESH.encode('utf-8'))
    save('inputs/fresh-prior-a7-axioms.lean', FRESH_A8.encode('utf-8'))
    inner = {"project_sources": records, "configs": configs, "stages": stages,
             "vm": "quantyra-lean-builder-01", "project": "quantyra-lean-cert-20260915",
             "zone": "us-central1-a", "external_imports": sorted(external),
             "requested_axioms": REQUESTED_AXIOMS, "claims_boundary": CLAIM,"owned_sources":OWNED,"cache_provenance":CACHE}
    save("inputs/capture-manifest.json", json_bytes(inner))
    archive_path = capture / "input-archive.tar.gz"
    with archive_path.open("xb") as raw:
        with gzip.GzipFile(fileobj=raw, mode="wb", mtime=0, filename="") as compressed:
            with tarfile.open(fileobj=compressed, mode="w", format=tarfile.PAX_FORMAT) as archive:
                for rel in sorted(files):
                    if not rel.startswith("inputs/"):
                        continue
                    data = (capture / rel).read_bytes()
                    member = tarfile.TarInfo(rel.removeprefix("inputs/"))
                    member.size = len(data)
                    member.mode = 0o644
                    archive.addfile(member, io.BytesIO(data))
    files["input-archive.tar.gz"] = {"sha256": file_sha(archive_path), "bytes": archive_path.stat().st_size}
    report_text = (REPO / REPORT).read_text(encoding="utf-8-sig")
    report_source_hash = re.search(r"ActualBinaryMatrixHC46A9AmbientFiber\.lean`:\s*`([A-F0-9]{64})`", report_text)
    manifest = {"schema": 1, "capture": name, "prepared_utc": utc(), "status": "PREPARED_OFFLINE",
        "certified": False, "local_compilation": False, "gcloud_invoked_during_preparation": False,
        "frozen_identities": FROZEN, "offered_identities": offered, "repair_basis": basis,
        "project_sources": records, "project_module_order": order,
        "project_modules": len(records) - 13, "check_modules": 13,
        "external_imports": sorted(external), "configs": configs,
        "external_source_baseline": {"origin": str(BASELINE.relative_to(REPO)).replace("\\", "/"),
            "counts": baseline_counts, "package_revisions": revisions,
            "note": "Prior GCP source custody only; not a compile receipt for this increment. "
                    "The VM run recaptures these sources and must match every byte hash."},
        "script_hashes": {rel: file_sha(PACKAGE / rel) for rel in SCRIPTS},
        "files": files, "stages": stages, "requested_axioms": REQUESTED_AXIOMS,
        "claims_boundary": CLAIM, "local_process_check_before": processes,
        "report_identity_note": {"embedded_source_hash": report_source_hash.group(1) if report_source_hash else None,
            "captured_source_hash": offered[SOURCE],
            "note": "Frozen authored report and exact handoff bytes are preserved."},
        "known_gate_risk": "Prior GCP A9InitialGraph logs contain linter warnings. "
                           "Legacy audit stays zero-total RED; prospective audit compares frozen warning headers; no suppression.",
        "resource_plan": {"project": inner["project"], "zone": inner["zone"], "vm": inner["vm"],
            "reuse_workspace": PRIOR, "created_resources": [],
            "precondition": "Authenticated GCP describe succeeds and existing VM is TERMINATED",
            "terminal_required": "TERMINATED"}, "inherited_files": len(inherited),
        "inherited_preservation_scope": "All tracked modified/deleted file hashes, all untracked Lean file hashes, "
            "complete tracked diff, and directory-level untracked Git status. Other inherited untracked contents "
            "are outside every write operation; they are not exhaustively hashed.",
        "protocol_context": {"destination_protocol_snapshot": "workflow-protocol.snapshot", "planning_files_modified": False}}

    from runner import render_remote
    preview_run_id = "cmmsa_a8_output_" + datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ") + "_00000000"
    save("remote-run.sh.preview", render_remote(preview_run_id, manifest).encode("utf-8"))
    manifest["prepared_remote_preview"] = {"run_id": preview_run_id, "executed": False,
        "note": "Concrete script rendered offline for inspection; authoritative attempt receives its own unique run ID."}
    write_new(capture / "manifest.json", json_bytes(manifest))
    command = ["python", "-B", (PACKAGE / "runner.py").relative_to(REPO).as_posix(), "--capture", name, "--execute"]
    write_new(capture / "invocation.json", json_bytes({"cwd": str(REPO), "argv": command,
        "manifest_sha256": file_sha(capture / "manifest.json"), "offline_prepared_only": True,
        "mutations_now": [], "compile_host": "GCP VM only", "automatic_git_writes": False,
        "authentication_blocker": None,
        "authentication_note": "User restored GCP authentication; runner still requires authenticated preflight"}))
    write_new(capture / "capture-ack.json", json_bytes({"utc": utc(), "capture": name,
        "offered_hashes_match": True, "offered_identities": offered,
        "initial_frozen_identities_match": offered == FROZEN, "repair_basis": basis,
        "project_source_modules": len(records),
        "baseline_sources": baseline_counts, "manifest_sha256": file_sha(capture / "manifest.json"),
        "local_process_check_after": local_process_check(), "certified": False, "claims_boundary": CLAIM,"owned_sources":OWNED,"cache_provenance":CACHE}))
    if inherited_now() != inherited or inherited_status_now() != inherited_status:
        raise ValueError("Inherited worktree changed during capture")
    print(json.dumps({"capture": name, "project_source_modules": len(records),
        "baseline_sources": baseline_counts, "archive_sha256": file_sha(archive_path),
        "launch_argv": command, "certified": False}, indent=2), flush=True)


if __name__ == "__main__":
    main()
