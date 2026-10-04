"""Offline syntax, custody, and negative-gate tests. No cloud or compiler invocation."""
from __future__ import annotations

import argparse
import ast
import io
import json
import re
import tarfile
import unittest
import uuid
from datetime import datetime, timezone
from pathlib import Path
from unittest.mock import patch

import audit
import cloud_capture
from common import (PACKAGE, SOURCE, CHECKS, FROZEN, REQUESTED_AXIOMS, file_sha, sha, utc,
                    local_process_check, verify_capture, forbidden_tokens, imports,
                    diagnostic_counts, axiom_profiles, require_profiles, inherited_now, inherited_status_now,
                    write_new, json_bytes)
from prepare import SCRIPTS, check_source_archive
from runner import render_remote, validate_cloud_args, pick_capture, VM


class OfflineGates(unittest.TestCase):
    capture = None

    def profiles(self, extras=()):
        return {name: ["propext", "Classical.choice", "Quot.sound", *extras]
                for name in REQUESTED_AXIOMS}

    def test_active_placeholders_and_native_decide_are_detected(self):
        found = forbidden_tokens(b"theorem broken : True := by\n  sorry\nexample : True := by native_decide\n")
        self.assertEqual(found, [{"token": "sorry", "line": 2}, {"token": "native_decide", "line": 3}])

    def test_nested_comments_strings_and_axioms_plural_are_masked(self):
        text = '/- sorry /- axiom -/ native_decide -/\n-- admit\ndef s := "unsafe sorry"\n#print axioms good\n'
        self.assertEqual(forbidden_tokens(text.encode()), [])

    def test_unterminated_comment_is_rejected(self):
        with self.assertRaises(ValueError):
            forbidden_tokens(b"/- unfinished sorry")

    def test_import_capture_ignores_commented_imports(self):
        text = b"/- import PvNP.Hidden -/\nimport PvNP.First Mathlib.Data.Fintype.Card -- import Hidden\npublic import PvNP.Second\n"
        self.assertEqual(imports(text), ["PvNP.First", "Mathlib.Data.Fintype.Card", "PvNP.Second"])

    def test_diagnostics_include_stderr_and_unsolved_goals(self):
        self.assertEqual(diagnostic_counts("warning: linter\nerror: unsolved goals", "WARNING: stderr"),
                         {"warnings": 2, "errors": 1, "unsolved_goals": 1})

    def test_standard_and_axiom_free_profiles_are_accepted(self):
        values = self.profiles()
        values[REQUESTED_AXIOMS[-2]] = []
        require_profiles(values)

    def test_sorry_axiom_is_rejected(self):
        with self.assertRaises(ValueError):
            require_profiles(self.profiles(["sorryAx"]))

    def test_nonstandard_axiom_is_rejected(self):
        with self.assertRaises(ValueError):
            require_profiles(self.profiles(["Custom.assumption"]))

    def test_missing_axiom_receipt_is_rejected(self):
        values = self.profiles()
        values.pop(REQUESTED_AXIOMS[0])
        with self.assertRaises(ValueError):
            require_profiles(values)

    def test_multiline_axiom_output_and_no_axioms_parse(self):
        text = "'A' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n'B' does not depend on any axioms\n"
        self.assertEqual(axiom_profiles(text), {"A": ["Classical.choice", "Quot.sound", "propext"], "B": []})

    def test_disagreeing_repeated_axiom_output_is_rejected(self):
        with self.assertRaises(ValueError):
            axiom_profiles("'A' depends on axioms: [propext]\n'A' depends on axioms: [sorryAx]")

    def test_local_compiler_commands_are_rejected_by_controller(self):
        for command in [["lean", "source.lean"], ["lake", "build"], ["lake", "env", "lean"],
                        ["compute", "instances", "create", VM], ["compute", "instances", "delete", VM]]:
            with self.subTest(command=command), self.assertRaises(ValueError):
                validate_cloud_args(command, authenticated=True)

    def test_mutations_cannot_precede_authenticated_preflight(self):
        for operation in ["start", "stop"]:
            with self.subTest(operation=operation), self.assertRaises(RuntimeError):
                validate_cloud_args(["compute", "instances", operation, VM], authenticated=False)
        validate_cloud_args(["compute", "instances", "describe", VM], authenticated=False)

    def test_other_vm_is_rejected(self):
        for command in [["compute", "instances", "start", "other-vm"],
                        ["compute", "ssh", "other-vm"], ["compute", "scp", "file", "other-vm:/tmp/"]]:
            with self.subTest(command=command), self.assertRaises(ValueError):
                validate_cloud_args(command, authenticated=True)

    def test_windows_cloud_helper_refuses_to_spawn_compiler(self):
        with patch.object(cloud_capture.sys, "platform", "win32"):
            with patch.object(cloud_capture.subprocess, "run") as spawn:
                with self.assertRaises(RuntimeError):
                    cloud_capture.run_compiler(["lake", "env", "lean", "source.lean"], {})
                spawn.assert_not_called()

    def test_remote_render_rejects_command_injection_in_id(self):
        with self.assertRaises(ValueError):
            render_remote("anything; lean source.lean", {})

    def test_remote_render_rejects_injected_archive_hash(self):
        manifest = {"files": {"input-archive.tar.gz": {"sha256": "'; bad"},
            "inputs/capture-manifest.json": {"sha256": "A" * 64}},
            "resource_plan": {"reuse_workspace": "cmmsa_analytic_20261004T002601Z"}}
        with self.assertRaises(ValueError):
            render_remote("cmmsa_a9_ambient_20261004T000000Z_1234abcd", manifest)

    def test_missing_cloud_receipts_cannot_certify(self):
        if self.capture is None:
            self.skipTest("Requires a prepared capture")
        missing = PACKAGE / "validations" / "synthetic-absent-cloud-receipts"
        result = audit.audit_run(self.capture, missing)
        self.assertFalse(result["green"])
        self.assertFalse(result["certified"])
        self.assertTrue(result["failures"])

    def test_tampered_snapshot_hash_is_rejected(self):
        if self.capture is None:
            self.skipTest("Requires a prepared capture")
        target = self.capture / "source.lean.snapshot"
        actual_digest = file_sha

        def tampered(path):
            return "0" * 64 if Path(path) == target else actual_digest(path)

        with patch("common.file_sha", side_effect=tampered):
            with self.assertRaisesRegex(ValueError, "Capture file drift"):
                verify_capture(self.capture, live=False)

    def check_memory_archive(self, entries, hashes, expected_error=None):
        buffer = io.BytesIO()
        with tarfile.open(fileobj=buffer, mode="w:gz") as archive:
            for name, data in entries:
                member = tarfile.TarInfo(name)
                member.size = len(data)
                archive.addfile(member, io.BytesIO(data))
        for checker in [check_source_archive, audit.verify_source_archive]:
            reader = tarfile.open(fileobj=io.BytesIO(buffer.getvalue()), mode="r:gz")
            with self.subTest(checker=checker.__name__), patch("tarfile.open", return_value=reader):
                if expected_error:
                    with self.assertRaisesRegex(ValueError, expected_error):
                        checker(Path("memory.tar.gz"), hashes)
                else:
                    checker(Path("memory.tar.gz"), hashes)

    def test_source_archives_accept_unsorted_hash_inventory(self):
        self.check_memory_archive([("a.lean", b"a"), ("b.lean", b"b")],
                                  {"b.lean": sha(b"b"), "a.lean": sha(b"a")})

    def test_source_archives_reject_duplicate_members(self):
        self.check_memory_archive([("a.lean", b"a"), ("a.lean", b"a")],
                                  {"a.lean": sha(b"a")}, "membership")

    def test_source_archives_reject_corrupt_and_missing_sources(self):
        self.check_memory_archive([("a.lean", b"corrupt")], {"a.lean": sha(b"a")}, "hash mismatch")
        self.check_memory_archive([("a.lean", b"a")],
                                  {"a.lean": sha(b"a"), "b.lean": sha(b"b")}, "membership")


def validate(capture):
    process_before = local_process_check()
    manifest = verify_capture(capture)
    syntax = []
    for name in SCRIPTS:
        if name.endswith(".py"):
            tree = ast.parse((PACKAGE / name).read_text(encoding="utf-8"), filename=name)
            syntax.append({"file": name, "sha256": file_sha(PACKAGE / name), "python_ast": "PASS"})
            if name != "cloud_capture.py":
                for node in ast.walk(tree):
                    if not isinstance(node, ast.Call) or not node.args:
                        continue
                    function = node.func
                    if not (isinstance(function, ast.Attribute) and isinstance(function.value, ast.Name)
                            and function.value.id == "subprocess" and function.attr in
                            {"run", "Popen", "check_output", "check_call", "call"}):
                        continue
                    first = node.args[0]
                    if isinstance(first, (ast.List, ast.Tuple)) and first.elts:
                        executable = first.elts[0]
                        if isinstance(executable, ast.Constant) and executable.value in {"lean", "lean.exe", "lake", "lake.exe"}:
                            raise ValueError("Local compiler subprocess in " + name)
    archive = capture / "input-archive.tar.gz"
    with tarfile.open(archive, "r:gz") as stream:
        archive_expected = {rel.removeprefix("inputs/"): row for rel, row in manifest["files"].items()
                    if rel.startswith("inputs/")}
        members = {member.name: member for member in stream if member.isfile()}
        if set(members) != set(archive_expected):
            raise ValueError("Immutable upload archive membership mismatch")
        for rel, row in archive_expected.items():
            data = stream.extractfile(members[rel]).read()
            if sha(data) != row["sha256"] or len(data) != row["bytes"]:
                raise ValueError("Immutable upload archive payload mismatch: " + rel)
    for prefix in ["package", "core"]:
        hashes = json.loads((capture / f"dependency-baseline/{prefix}-source-hashes.json").read_bytes())
        check_source_archive(capture / f"dependency-baseline/{prefix}-sources.tar.gz", hashes)
    scans = {rel: forbidden_tokens((capture / "inputs" / rel).read_bytes()) for rel in [SOURCE, CHECKS]}
    if any(scans.values()):
        raise ValueError("Forbidden target token in prepared source/checks")
    for rel, expected in FROZEN.items():
        if manifest["frozen_identities"][rel] != expected:
            raise ValueError("Initial frozen offer drift: " + rel)
    inner = json.loads((capture / "inputs/capture-manifest.json").read_bytes())
    if inner["project_sources"] != manifest["project_sources"] or inner["stages"] != manifest["stages"]:
        raise ValueError("Remote/local source or stage manifest disagreement")
    for rel in [SOURCE, CHECKS]:
        code = (capture / "inputs" / rel).read_bytes()
        for module in imports(code):
            path = "lean/" + module.replace(".", "/") + ".lean"
            if path not in manifest["project_sources"] and module not in manifest["external_imports"]:
                raise ValueError("Uncaptured project import: " + module)
    check_text = (capture / "checks.lean.snapshot").read_text(encoding="utf-8-sig")
    authored_axioms = re.findall(r"^#print axioms\s+(\S+)", check_text, re.M)
    if {name.rsplit(".", 1)[-1] for name in REQUESTED_AXIOMS} != set(authored_axioms):
        raise ValueError("Prepared requested profiles do not match authored #print axioms commands")
    rendered = render_remote("cmmsa_a9_ambient_20261004T000000Z_1234abcd", manifest)
    if re.search(r"@[A-Z_]+@", rendered):
        raise ValueError("Remote template contains unresolved placeholders")
    preview = render_remote(manifest["prepared_remote_preview"]["run_id"], manifest)
    if preview.encode("utf-8") != (capture / "remote-run.sh.preview").read_bytes():
        raise ValueError("Concrete prepared remote preview differs from its template/manifest")
    OfflineGates.capture = capture
    unit_output = io.StringIO()
    result = unittest.TextTestRunner(stream=unit_output, verbosity=2).run(
        unittest.defaultTestLoader.loadTestsFromTestCase(OfflineGates))
    inherited = json.loads((capture / "inherited-files-before.json").read_bytes())
    inherited_status = json.loads((capture / "inherited-status-before.json").read_bytes())
    if inherited_now() != inherited or inherited_status_now() != inherited_status:
        raise ValueError("Inherited worktree differs from capture baseline")
    report = {"utc": utc(), "capture": capture.name, "status": "OFFLINE_VALIDATION_PASS" if result.wasSuccessful() else "OFFLINE_VALIDATION_FAIL",
        "certified": False, "local_compilation": False, "gcloud_invocations": 0, "resource_mutations": 0,
        "python_syntax": syntax, "unit_tests": {"run": result.testsRun, "failures": len(result.failures),
            "errors": len(result.errors), "skipped": len(result.skipped)},
        "manifest_sha256": file_sha(capture / "manifest.json"), "input_archive_sha256": file_sha(archive),
        "archive_members_checked": len(archive_expected), "project_source_modules": len(manifest["project_sources"]),
        "external_source_counts": manifest["external_source_baseline"]["counts"],
        "frozen_identities": FROZEN, "offered_identities": manifest.get("offered_identities", FROZEN),
        "repair_basis": manifest.get("repair_basis"), "target_forbidden_tokens": scans,
        "closure_forbidden_tokens": {rel: row["forbidden_tokens"] for rel, row in manifest["project_sources"].items()
                                     if row["forbidden_tokens"]},
        "remote_render": "PASS", "shell_runtime_validation": "Pending authoritative GCP run",
        "inherited_files_preserved": len(inherited), "inherited_preservation_scope": manifest["inherited_preservation_scope"],
        "local_process_check_before": process_before,
        "local_process_check_after": local_process_check(), "claims_boundary": manifest["claims_boundary"]}
    return report, unit_output.getvalue()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--capture")
    args = parser.parse_args()
    capture = pick_capture(args.capture)
    report, unit_output = validate(capture)
    name = "offline-" + datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ") + "-" + uuid.uuid4().hex[:8]
    receipt = PACKAGE / "validations" / name
    write_new(receipt / "report.json", json_bytes(report))
    write_new(receipt / "unit.stdout", unit_output)
    write_new(receipt / "unit.stderr", b"")
    inventory = {}
    for path in sorted(PACKAGE.rglob("*")):
        if path.is_file() and "__pycache__" not in path.parts:
            rel = path.relative_to(PACKAGE).as_posix()
            inventory[rel] = {"sha256": file_sha(path), "bytes": path.stat().st_size}
    write_new(receipt / "prepared-files.json", json_bytes(inventory))
    print(json.dumps({"capture": capture.name, "validation": name, "status": report["status"],
        "unit_tests": report["unit_tests"], "project_source_modules": report["project_source_modules"],
        "external_source_counts": report["external_source_counts"], "prepared_files": len(inventory),
        "gcloud_invocations": 0, "certified": False}, indent=2))
    return 0 if report["status"] == "OFFLINE_VALIDATION_PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
