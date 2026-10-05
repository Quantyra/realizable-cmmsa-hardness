"""Shared byte-custody checks. This module never runs a compiler or gcloud."""
from __future__ import annotations

import hashlib
import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath

PACKAGE = Path(__file__).resolve().parent
REPO = PACKAGE.parents[2]
SOURCE = 'lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A8OutputCoordinateTransport.lean'
CHECKS = 'lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A8OutputCoordinateTransportChecks.lean'
REPORT = 'docs/a8-gcp/r1005/statement-fidelity.md'
FROZEN = {'lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A8OutputCoordinateTransport.lean': '27060E3D3E4E9AF55622C13318C366DEE7CCCEBE804653F59954624B006266A1', 'lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A8OutputCoordinateTransportChecks.lean': 'A1610A8E4190836643646E33C0152B578D7821DF3EC17F947B153514EDA48E42', 'docs/a8-gcp/r1005/statement-fidelity.md': '5F3D3CF861E4653EDD8001E5B16E27B58EB9B1EF6E97F45DBE135F133CFD6CE1'}
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
NAMESPACE = "PvNP.RealizableHardness.ActualBinaryMatrixHC46A8OutputCoordinateTransport."
REQUESTED_AXIOMS = [NAMESPACE + name for name in ['a8_carrier_coordinate_nested_filter', 'a8_carrier_coordinate_nested_mean', 'a8_output_coordinate_eq', 'a8_output_pair_component_nested_mean', 'a8_w6_domain_quotient_square']]
CLAIM = 'Exact Luna domain quotient square, development candidate 2; unaccepted pending green GCP evidence and three-lens closeout. Accepted helper count 1; compiler/import repairs zero credit; threshold not crossed. S3132 partial / analytic A8 open; S3137 incomplete.'
CREATE_FLAGS = getattr(subprocess, "CREATE_NO_WINDOW", 0)


def utc():
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def file_sha(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest().upper()


def write_new(path, data):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("xb") as stream:
        stream.write(data if isinstance(data, bytes) else data.encode("utf-8"))


def json_bytes(value):
    return (json.dumps(value, indent=2, ensure_ascii=False) + "\n").encode("utf-8")


def safe_rel(name):
    path = PurePosixPath(name)
    if not name or path.is_absolute() or ".." in path.parts or "\\" in name or ":" in name:
        raise ValueError("Unsafe relative path: " + name)
    return path


def local_process_check():
    command = ["powershell.exe", "-NoProfile", "-NonInteractive", "-Command",
        "ConvertTo-Json -InputObject @(Get-Process -ErrorAction SilentlyContinue | "
        "Where-Object { $_.ProcessName -match '^(lean|lake)(\\.exe)?$' } | "
        "Select-Object Id,ProcessName,Path) -Compress"]
    result = subprocess.run(command, capture_output=True, check=True, timeout=30,
                            creationflags=CREATE_FLAGS)
    processes = json.loads(result.stdout.decode("utf-8-sig").strip() or "[]")
    if processes:
        raise RuntimeError("Local Lean/Lake process detected: " + repr(processes))
    return {"utc": utc(), "command": command, "processes": processes,
            "native_exit": result.returncode}


def lean_code(text):
    """Mask nested comments and strings, preserving lines for token diagnostics."""
    output = []
    depth = 0
    quoted = False
    index = 0
    while index < len(text):
        pair = text[index:index + 2]
        char = text[index]
        if depth:
            if pair == "/-":
                depth += 1
                output.extend("  ")
                index += 2
                continue
            if pair == "-/":
                depth -= 1
                output.extend("  ")
                index += 2
                continue
            output.append("\n" if char == "\n" else " ")
        elif quoted:
            if char == "\\" and index + 1 < len(text):
                output.extend("  ")
                index += 2
                continue
            if char == '"':
                quoted = False
            output.append("\n" if char == "\n" else " ")
        elif pair == "/-":
            depth = 1
            output.extend("  ")
            index += 2
            continue
        elif pair == "--":
            end = text.find("\n", index)
            end = len(text) if end < 0 else end
            output.extend(" " * (end - index))
            index = end
            continue
        elif char == '"':
            quoted = True
            output.append(" ")
        else:
            output.append(char)
        index += 1
    if depth or quoted:
        raise ValueError("Unterminated Lean comment/string in captured source")
    return "".join(output)


def forbidden_tokens(data):
    code = lean_code(data.decode("utf-8-sig"))
    pattern = r"\b(?:sorry|admit|axiom|unsafe|native_decide|sorryAx|implemented_by)\b"
    return [{"token": match.group(), "line": code.count("\n", 0, match.start()) + 1}
            for match in re.finditer(pattern, code)]


def imports(data):
    code = lean_code(data.decode("utf-8-sig"))
    found = []
    for line in re.findall(r"^\s*(?:(?:public|private|meta)\s+)*import\s+([^\r\n]+)", code, re.M):
        for name in line.split():
            if name == "all":
                continue
            if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.']*", name):
                raise ValueError("Unrecognized import token: " + name)
            found.append(name)
    return found


def diagnostic_counts(stdout, stderr):
    text = stdout + "\n" + stderr
    return {
        "warnings": len(re.findall(r"\bwarning\s*:", text, re.I)),
        "errors": len(re.findall(r"\berror\s*:", text, re.I)),
        "unsolved_goals": len(re.findall(r"\bunsolved goals\b", text, re.I)),
    }


def axiom_profiles(text):
    profiles = {}
    pattern = r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
    for match in re.finditer(pattern, text):
        name, values = match.groups()
        axioms = sorted({item.strip() for item in (values or "").split(",") if item.strip()})
        if name in profiles and profiles[name] != axioms:
            raise ValueError("Inconsistent repeated axiom profile: " + name)
        profiles[name] = axioms
    return profiles


def require_profiles(profiles):
    missing = set(REQUESTED_AXIOMS) - set(profiles)
    if missing:
        raise ValueError("Missing axiom profiles: " + repr(sorted(missing)))
    for name in REQUESTED_AXIOMS:
        extra = set(profiles[name]) - STANDARD_AXIOMS
        if extra:
            raise ValueError("Nonstandard axiom profile: " + name + " " + repr(sorted(extra)))


def verify_capture(capture, *, live=True):
    capture = Path(capture).resolve()
    manifest = json.loads((capture / "manifest.json").read_bytes())
    if manifest["capture"] != capture.name:
        raise ValueError("Manifest/capture directory identity mismatch")
    invocation = json.loads((capture / "invocation.json").read_bytes())
    acknowledgement = json.loads((capture / "capture-ack.json").read_bytes())
    actual_manifest_sha = file_sha(capture / "manifest.json")
    if invocation["manifest_sha256"] != actual_manifest_sha or acknowledgement["manifest_sha256"] != actual_manifest_sha:
        raise ValueError("Immutable manifest differs from invocation/capture acknowledgement")
    if manifest["frozen_identities"] != FROZEN or manifest["requested_axioms"] != REQUESTED_AXIOMS:
        raise ValueError("Frozen offers or requested axiom scope changed")
    for name, row in manifest["files"].items():
        safe_rel(name)
        path = capture / name
        if file_sha(path) != row["sha256"] or path.stat().st_size != row["bytes"]:
            raise ValueError("Capture file drift: " + name)
    offered = manifest.get("offered_identities", FROZEN)
    if set(offered) != set(FROZEN):
        raise ValueError("Offered identity membership changed")
    if any(not re.fullmatch(r"[A-F0-9]{64}", value) for value in offered.values()):
        raise ValueError("Malformed offered SHA256 identity")
    for name, snapshot in [(SOURCE, "source.lean.snapshot"), (CHECKS, "checks.lean.snapshot"),
                           (REPORT, "author-report.md.snapshot")]:
        if manifest["files"][snapshot]["sha256"] != offered[name]:
            raise ValueError("Offered snapshot identity mismatch: " + name)
    for name in [SOURCE, CHECKS]:
        if manifest["project_sources"][name]["sha256"] != offered[name]:
            raise ValueError("Offered compiler input identity mismatch: " + name)
    changed = {name for name in FROZEN if offered[name] != FROZEN[name]}
    if changed - {SOURCE, CHECKS, REPORT}:
        raise ValueError("Frozen dependency repair is outside the owned scope")
    if changed:
        basis = manifest.get("repair_basis")
        if not basis or not basis.get("run"):
            raise ValueError("Owned repair lacks captured GCP diagnostics")
        previous = json.loads((capture / "repair-basis/manifest.json").read_bytes())
        terminal = json.loads((capture / "repair-basis/terminal.json").read_bytes())
        audit = json.loads((capture / "repair-basis/audit.json").read_bytes())
        if (previous["frozen_identities"] != FROZEN or audit["green"]
                or terminal["vm_terminal_receipt"]["status"] != "TERMINATED"
                or terminal["run"] != basis["run"] or audit["run"] != basis["run"]):
            raise ValueError("Repair basis is not a retained failed, terminated GCP run")
        for name in ["repair-basis/manifest.json", "repair-basis/terminal.json", "repair-basis/audit.json",
                     "repair-basis/stage-1.stdout", "repair-basis/stage-1.stderr"]:
            if name not in manifest["files"]:
                raise ValueError("Unbound repair diagnostic: " + name)
    for name, expected in manifest["script_hashes"].items():
        snapshot = capture / "harness" / (name + ".snapshot")
        if snapshot.is_file() and file_sha(snapshot) != expected:
            raise ValueError("Captured harness drift: " + name)
        if live and file_sha(PACKAGE / name) != expected:
            raise ValueError("Prepared script drift: " + name + "; create a successor capture")
    if live:
        for name, row in manifest["project_sources"].items():
            if file_sha(REPO / name) != row["sha256"]:
                raise ValueError("Live project source drift: " + name)
        for name, row in manifest["configs"].items():
            if file_sha(REPO / name) != row["sha256"]:
                raise ValueError("Live configuration drift: " + name)
        for name, expected in offered.items():
            if file_sha(REPO / name) != expected:
                raise ValueError("Live offered file drift: " + name)
    return manifest


def inherited_now():
    # Millions of generated untracked receipts exist outside the Lean source tree.
    # Never expand/hash that entire tree. Preserve all tracked dirt and every
    # untracked Lean file; directory-level status and the write scope cover the rest.
    tracked = subprocess.check_output(["git", "ls-files", "--modified", "--deleted", "-z"],
                                      cwd=REPO, creationflags=CREATE_FLAGS)
    lean_untracked = subprocess.check_output(["git", "ls-files", "--others", "--exclude-standard", "-z", "--", "lean"],
                                             cwd=REPO, creationflags=CREATE_FLAGS)
    names = set(tracked.decode("utf-8").strip("\0").split("\0"))
    names.update(name for name in lean_untracked.decode("utf-8").strip("\0").split("\0") if name.endswith(".lean"))
    owned_prefix = PACKAGE.relative_to(REPO).as_posix() + "/"
    rows = {}
    for name in sorted(names):
        if not name or name in {SOURCE, CHECKS, REPORT} or name.startswith(owned_prefix):
            continue
        path = REPO / name
        rows[name] = ({"sha256": file_sha(path), "bytes": path.stat().st_size}
                      if path.is_file() else {"missing": True})
    return rows


def inherited_status_now():
    data = subprocess.check_output(["git", "status", "--porcelain=v1", "--untracked-files=normal"],
                                   cwd=REPO, creationflags=CREATE_FLAGS)
    owned_prefix = PACKAGE.relative_to(REPO).as_posix()
    lines = []
    for line in data.decode("utf-8").splitlines():
        name = line[3:].rstrip("/")
        if name in {SOURCE, CHECKS, REPORT, owned_prefix} or name.startswith(owned_prefix + "/"):
            continue
        lines.append(line)
    return lines
