"""Audit captured GCP bytes offline. Never invokes Lean, Lake, or gcloud."""
from __future__ import annotations

import argparse
import json
import tarfile
from pathlib import Path

from common import (PACKAGE, SOURCE, CHECKS, CLAIM, REQUESTED_AXIOMS, file_sha, sha, utc,
                    verify_capture, diagnostic_counts, axiom_profiles, require_profiles,
                    forbidden_tokens, write_new, json_bytes)


def normalize_hashes(values):
    return {name: value.upper() for name, value in values.items()}


def verify_source_archive(path, hashes):
    with tarfile.open(path, "r:gz") as archive:
        seen = set()
        for member in archive:
            if not member.isfile():
                continue
            name = member.name
            if name not in hashes or name in seen:
                raise ValueError("Cloud source archive membership mismatch: " + name)
            seen.add(name)
            if sha(archive.extractfile(member).read()) != hashes[name].upper():
                raise ValueError("Cloud source archive hash mismatch: " + name)
        if seen != set(hashes):
            raise ValueError("Cloud source archive membership mismatch: " + path.name)


def audit_run(capture, run):
    capture, run = Path(capture), Path(run)
    summary = {"run": run.name, "capture": capture.name, "audited_utc": utc(), "green": False,
        "certified": False, "local_compilation": False, "failures": [], "stage_results": [],
        "claims_boundary": CLAIM, "review_debt": {"proof_adversarial": "INCOMPLETE",
            "complexity": "INCOMPLETE", "non_claims": "INCOMPLETE",
            "note": "Development compiler evidence only; route-final acceptance remains open"}}

    def require(condition, message):
        if not condition:
            summary["failures"].append(message)

    try:
        # Historical attempts remain auditable after an owned successor repair.
        # Executed scripts and compiled source identities are checked against the
        # immutable capture below, independently of the mutable live worktree.
        manifest = verify_capture(capture, live=False)
        request = json.loads((run / "request.json").read_bytes())
        terminal = json.loads((run / "terminal-custody-recovered.json").read_bytes())
        require(request["manifest_sha256"] == file_sha(capture / "manifest.json"), "Run/capture manifest identity mismatch")
        require(terminal["compiler_attempted"], "GCP compiler stage never launched")
        require(terminal.get("failure") is None, "Runner reports a transport/preservation/terminal failure")
        for script in ["runner.py", "audit.py", "common.py"]:
            require(file_sha(run / ("executed-" + script)) == manifest["script_hashes"][script],
                    "Executed script identity differs from the prepared script: " + script)
        require(terminal["local_process_check_after"]["processes"] == [], "Local Lean/Lake process observed")
        require(terminal["inherited_dirt_preserved"], "Inherited dirt changed during run")
        state = terminal.get("vm_terminal_receipt") or {}
        summary["vm_terminal_state"] = state.get("status", "UNPROVED")
        require(state.get("name") == manifest["resource_plan"]["vm"] and state.get("status") == "TERMINATED",
                "GCP VM TERMINATED state not proved")
        controls = json.loads((run / "commands-custody-recovered.json").read_bytes())
        for row in controls:
            require(file_sha(run / row["stdout_path"]) == row["stdout_sha256"], "Control stdout custody failed")
            require(file_sha(run / row["stderr_path"]) == row["stderr_sha256"], "Control stderr custody failed")
        final_descriptions = [row for row in controls if row["argv"][1:4] == ["compute", "instances", "describe"]
                              and row["native_exit"] == 0]
        require(bool(final_descriptions), "Missing authenticated describe receipt")
        if final_descriptions:
            raw_state = json.loads((run / final_descriptions[-1]["stdout_path"]).read_bytes())
            require(raw_state == state, "Terminal state summary differs from raw GCP receipt")
        archive = run / (run.name + "-evidence.tar.gz")
        require(archive.is_file(), "No downloaded cloud evidence archive")
        if not archive.is_file():
            return summary
        require(file_sha(archive) == terminal["evidence_archive_sha256"], "Cloud evidence archive hash mismatch")
        receipt = run / "remote-evidence"
        if not receipt.exists():
            receipt.mkdir()
            with tarfile.open(archive, "r:gz") as stream:
                stream.extractall(receipt, filter="data")
        with tarfile.open(archive, "r:gz") as stream:
            for member in stream:
                if member.isfile():
                    path = receipt / member.name
                    require(path.is_file() and file_sha(path) == sha(stream.extractfile(member).read()),
                            "Extracted cloud receipt differs from retained archive: " + member.name)
        require((receipt / "run-id.txt").read_text().strip() == run.name, "Remote run identity mismatch")
        identity = json.loads((receipt / "gcp-execution-identity.json").read_bytes())
        require(identity["id"] == str(state["id"]) and identity["name"] == state["name"],
                "Compiler GCP identity differs from terminal VM identity")
        require(identity["project"] == manifest["resource_plan"]["project"] and
                identity["zone"].rsplit("/", 1)[-1] == manifest["resource_plan"]["zone"],
                "Compiler executed on an unexpected GCP project/zone")
        expected = {rel: row["sha256"] for rel, row in manifest["project_sources"].items()}
        expected.update({rel: row["sha256"] for rel, row in manifest["configs"].items()})
        for phase in ["before", "after"]:
            actual = json.loads((receipt / f"source-{phase}.json").read_bytes())
            require(actual == expected, "Exact source/configuration custody mismatch " + phase)
        objects = json.loads((receipt / "compiled-project-objects.json").read_bytes())
        required_objects = {".lake/build/lib/lean/" + rel.removeprefix("lean/").removesuffix(".lean") + ".olean"
                            for rel in manifest["project_sources"]}
        require(set(objects) == required_objects, "Incomplete compiled project dependency closure")
        summary["compiled_project_modules"] = len(objects)
        object_inventory = json.loads((receipt / "object-after.json").read_bytes())
        require(all(object_inventory.get(name) == value for name, value in objects.items()),
                "Compiled object inventories disagree")
        for prefix in ["package", "core"]:
            hashes = json.loads((receipt / f"{prefix}-source-hashes.json").read_bytes())
            verify_source_archive(receipt / f"{prefix}-sources.tar.gz", hashes)
            baseline = json.loads((capture / f"dependency-baseline/{prefix}-source-hashes.json").read_bytes())
            require(normalize_hashes(hashes) == normalize_hashes(baseline),
                    "Cloud " + prefix + " sources differ from immutable dependency baseline")
            summary[prefix + "_source_count"] = len(hashes)
        revisions = json.loads((receipt / "package-identities.json").read_bytes())
        require(revisions == manifest["external_source_baseline"]["package_revisions"], "Package revision drift")
        compiler = json.loads((receipt / "compiler-identity.json").read_bytes())
        baseline_compiler = json.loads((capture / "dependency-baseline/compiler-identity.json").read_bytes())
        require(compiler["sha256"].upper() == baseline_compiler["sha256"].upper(), "Compiler binary identity drift")
        toolchain = (receipt / "toolchain.txt").read_text().strip()
        require(toolchain == (capture / "dependency-baseline/toolchain.txt").read_text().strip(), "Compiler version/commit drift")
        summary["lean_identity"] = toolchain
        summary["compiler_sha256"] = compiler["sha256"].upper()
        total = {"warnings": 0, "errors": 0, "unsolved_goals": 0}
        for stage in manifest["stages"]:
            index = stage["index"]
            stdout = (receipt / f"stage-{index}.stdout").read_text(encoding="utf-8", errors="replace")
            stderr = (receipt / f"stage-{index}.stderr").read_text(encoding="utf-8", errors="replace")
            code = int((receipt / f"stage-{index}.native-exit").read_text())
            command = json.loads((receipt / f"stage-{index}.command.json").read_bytes())
            require(command["stage"] == stage and command["argv"][4:] == stage["argv"], "Stage command mismatch")
            require(command["native_exit"] == code, "Per-stage exit receipts disagree")
            require(command["gcp_instance_id"] == identity["id"], "Per-stage execution host mismatch")
            require(command["stdout_sha256"] == file_sha(receipt / f"stage-{index}.stdout") and
                    command["stderr_sha256"] == file_sha(receipt / f"stage-{index}.stderr"), "Per-stage raw log hash mismatch")
            require(bool(command["started_utc"] and command["finished_utc"]), "Missing stage timestamps")
            counts = diagnostic_counts(stdout, stderr)
            summary["stage_results"].append({"index": index, "name": stage["name"], "native_exit": code, **counts})
            for key in total:
                total[key] += counts[key]
            require(code == 0, f"Stage {index} compiler exit is {code}")
        for stem in ["setup", "finish", "toolchain", "lake"]:
            stdout_path = receipt / (stem + (".txt" if stem in {"toolchain", "lake"} else ".stdout"))
            stderr_path = receipt / (stem + ".stderr")
            counts = diagnostic_counts(stdout_path.read_text(errors="replace"), stderr_path.read_text(errors="replace"))
            for key in total:
                total[key] += counts[key]
        summary["diagnostics"] = total
        require(all(value == 0 for value in total.values()), "Warnings/errors/unsolved goals are not all zero")
        for name in ["native-exit", "aggregate.native-exit", "finish.native-exit"]:
            require(int((receipt / name).read_text()) == 0, "Nonzero remote terminal exit: " + name)
        axiom_text = (receipt / "stage-3.stdout").read_text(encoding="utf-8", errors="replace")
        profiles = axiom_profiles(axiom_text)
        require_profiles(profiles)
        summary["axiom_profiles"] = {name: profiles[name] for name in REQUESTED_AXIOMS}
        for rel in [SOURCE, CHECKS]:
            require(not forbidden_tokens((capture / "inputs" / rel).read_bytes()), "Forbidden target token: " + rel)
        for name in ["started.utc", "finished.utc", "terminal.utc"]:
            require(bool((receipt / name).read_text().strip()), "Missing terminal timestamp: " + name)
        summary["source_sha256"] = manifest["project_sources"][SOURCE]["sha256"]
        summary["checks_sha256"] = manifest["project_sources"][CHECKS]["sha256"]
        summary["archive_sha256"] = manifest["files"]["input-archive.tar.gz"]["sha256"]
        summary["green"] = not summary["failures"]
        summary["certified"] = summary["green"]
    except Exception as error:
        summary["failures"].append(type(error).__name__ + ": " + str(error))
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--capture", required=True)
    parser.add_argument("--run", required=True)
    args = parser.parse_args()
    capture = (PACKAGE / "captures" / args.capture).resolve()
    run = (PACKAGE / "runs" / args.run).resolve()
    if not capture.is_relative_to(PACKAGE / "captures") or not run.is_relative_to(PACKAGE / "runs"):
        raise ValueError("Audit target outside the evidence package")
    result = audit_run(capture, run)
    output = run / ("audit-recheck-" + utc().replace(":", "-") + ".json")
    write_new(output, json_bytes(result))
    print(json.dumps(result, indent=2))
    return 0 if result["green"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
