"""GCP-only helper. Every compiler call is gated by Linux and GCP metadata identity."""
from __future__ import annotations

import hashlib
import json
import os
import platform
import subprocess
import sys
import tarfile
import time
import urllib.request
from datetime import datetime, timezone
from pathlib import Path


def utc():
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def digest(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest().upper()


def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def require_gcp(manifest):
    if sys.platform != "linux":
        raise RuntimeError("Cloud helper refuses to execute on a non-Linux host")
    opener = urllib.request.build_opener(urllib.request.ProxyHandler({}))

    def metadata(path):
        request = urllib.request.Request("http://metadata.google.internal/computeMetadata/v1/" + path,
                                         headers={"Metadata-Flavor": "Google"})
        with opener.open(request, timeout=10) as response:
            if response.headers.get("Metadata-Flavor") != "Google":
                raise RuntimeError("Missing authenticated GCP metadata response header")
            return response.read().decode().strip()

    identity = {"name": metadata("instance/name"), "id": metadata("instance/id"),
                "zone": metadata("instance/zone"), "project": metadata("project/project-id"),
                "machine_type": metadata("instance/machine-type"),
                "platform": platform.platform(), "utc": utc()}
    if (identity["id"] != "8337954477286097405" or identity["name"] != manifest["vm"] or identity["project"] != manifest["project"]
            or identity["zone"].rsplit("/", 1)[-1] != manifest["zone"]):
        raise RuntimeError("Unexpected GCP execution host: " + repr(identity))
    return identity


def source_pins(work, manifest):
    expected = {rel: row["sha256"] for rel, row in manifest["project_sources"].items()}
    expected.update({rel: row["sha256"] for rel, row in manifest["configs"].items()})
    actual = {rel: digest(work / rel) for rel in expected}
    if actual != expected:
        raise RuntimeError("Project/configuration source custody failed")
    return actual


def run_compiler(command, manifest, **kwargs):
    # Guard the subprocess itself as well as the helper's main entry point.
    require_gcp(manifest)
    return subprocess.run(command, **kwargs)


def object_pins(root, relative_to):
    return {str(path.relative_to(relative_to)): digest(path)
            for path in sorted(root.rglob("*.olean*")) if path.is_file()}


def snapshot(evidence):
    archive_path = evidence.with_name(evidence.name + ".tar.gz")
    next_path = archive_path.with_name(archive_path.name + ".next")
    with tarfile.open(next_path, "w:gz") as archive:
        for path in sorted(evidence.iterdir()):
            archive.add(path, arcname=path.name)
    next_path.replace(archive_path)


def begin(work, evidence, manifest, identity):
    save(evidence / "gcp-execution-identity.json", identity)
    save(evidence / "source-before.json", source_pins(work, manifest))
    for command, name in [(["lean", "--version"], "toolchain"), (["lake", "--version"], "lake")]:
        with (evidence / (name + ".txt")).open("wb") as stdout:
            with (evidence / (name + ".stderr")).open("wb") as stderr:
                result = run_compiler(command, manifest, stdout=stdout, stderr=stderr, check=False)
        save(evidence / (name + "-invocation.json"), {"argv": command, "native_exit": result.returncode,
                                                       "utc": utc(), "host": identity})
        if result.returncode:
            raise RuntimeError("Compiler identity command failed: " + name)
    package_sources = {}
    revisions = {}
    for package in sorted((work / ".lake/packages").iterdir()):
        if not package.is_dir():
            continue
        if (package / ".git").exists():
            revisions[package.name] = subprocess.check_output(
                ["git", "-C", str(package), "rev-parse", "HEAD"]).decode().strip()
            patch = subprocess.check_output(["git", "-C", str(package), "diff", "--binary", "HEAD", "--"])
            (evidence / (package.name + "-tracked-diff.patch")).write_bytes(patch)
            changed = subprocess.check_output(["git", "-C", str(package), "diff", "--numstat", "HEAD", "--"])
            for line in changed.decode().splitlines():
                added, removed, rel = line.split("\t", 2)
                if added == removed == "0" or not rel.endswith(".lean"):
                    continue
                canonical = subprocess.check_output(["git", "-C", str(package), "show", "HEAD:" + rel])
                if (package / rel).read_bytes().replace(b"\r\n", b"\n") != canonical.replace(b"\r\n", b"\n"):
                    raise RuntimeError("Changed package Lean source: " + package.name + "/" + rel)
        for directory, dirs, files in os.walk(package):
            dirs[:] = [name for name in dirs if name not in {".git", ".lake"}]
            for name in files:
                if name.endswith(".lean") or name in {"lean-toolchain", "lake-manifest.json", "lakefile.toml"}:
                    path = Path(directory) / name
                    package_sources[str(path.relative_to(work))] = digest(path)
    expected_revisions = json.loads((work / "lake-manifest.json").read_bytes())["packages"]
    if any(revisions.get(row["name"]) != row["rev"] for row in expected_revisions):
        raise RuntimeError("VM package revisions do not match immutable lake-manifest.json")
    save(evidence / "package-identities.json", revisions)
    save(evidence / "package-source-hashes.json", package_sources)
    with tarfile.open(evidence / "package-sources.tar.gz", "w:gz") as archive:
        for rel in sorted(package_sources):
            archive.add(work / rel, arcname=rel)
    compiler = Path(subprocess.check_output([str(Path.home() / ".elan/bin/elan"), "which", "lean"]).decode().strip())
    toolchain = compiler.parent.parent
    save(evidence / "compiler-identity.json", {"path": str(compiler), "sha256": digest(compiler)})
    core_sources = {str(path.relative_to(toolchain)): digest(path)
                    for path in sorted((toolchain / "src").rglob("*.lean"))}
    save(evidence / "core-source-hashes.json", core_sources)
    with tarfile.open(evidence / "core-sources.tar.gz", "w:gz") as archive:
        for rel in sorted(core_sources):
            archive.add(toolchain / rel, arcname=rel)
    save(evidence / "package-object-before.json", object_pins(work / ".lake/packages", work))
    save(evidence / "core-object-before.json", object_pins(toolchain / "lib/lean", toolchain))
    cache=manifest['cache_provenance']
    assert digest(compiler)==cache['compiler']['sha256']
    assert package_sources==cache['package_sources'] and core_sources==cache['core_sources']
    assert all(manifest['project_sources'][n]['sha256']==h for n,h in cache['project_sources'].items())
    assert all(digest(work/n)==h for n,h in cache['objects'].items()), 'Cached dependency object changed'
    save(evidence/'verified-cache-provenance.json',cache)
    removed = []
    invalidated = {}
    for rel in manifest['owned_sources']+['lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A9AmbientReindex.lean','lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A7Transfer.lean']:
        suffix=rel.removeprefix('lean/').removesuffix('.lean')
        for root in [work/'.lake/build/lib/lean',work/'.lake/build/ir']:
            stem=root/suffix
            for path in sorted(stem.parent.glob(stem.name+'.*')):
                assert path.is_file() and path.resolve().is_relative_to(work.resolve())
                name=str(path.relative_to(work))
                invalidated[name]={'sha256':digest(path),'nlink_before':path.stat().st_nlink}
                path.unlink()
                removed.append(name)
            assert not list(stem.parent.glob(stem.name+'.*')), 'Owned auxiliary remains'
    save(evidence/'invalidated-project-objects.json',removed)
    save(evidence/'invalidated-owned-artifacts.json',invalidated)
    save(evidence/'owned-artifact-absence-before-compile.json',{'owned_sources':manifest['owned_sources'],'roots':['.lake/build/lib/lean','.lake/build/ir'],'all_absent':True,'prior_cache_untouched':True})
    snapshot(evidence)


def compile_stages(work, evidence, manifest, identity):
    aggregate = 0
    for stage in manifest["stages"]:
        index = stage["index"]
        command = ["timeout", "--signal=TERM", "--kill-after=20s", "900s", *stage["argv"]]
        started = utc()
        monotonic = time.monotonic()
        with (evidence / f"stage-{index}.stdout").open("wb") as stdout:
            with (evidence / f"stage-{index}.stderr").open("wb") as stderr:
                if aggregate:
                    code = 125
                    stderr.write(b"Skipped because a preceding compiler stage failed.\n")
                else:
                    code = run_compiler(command, manifest, cwd=work, stdout=stdout, stderr=stderr,
                                        check=False).returncode
        (evidence / f"stage-{index}.native-exit").write_text(str(code) + "\n")
        save(evidence / f"stage-{index}.command.json", {"argv": command, "stage": stage,
            "started_utc": started, "finished_utc": utc(), "seconds": time.monotonic() - monotonic,
            "native_exit": code, "gcp_instance_id": identity["id"],
            "stdout_sha256": digest(evidence / f"stage-{index}.stdout"),
            "stderr_sha256": digest(evidence / f"stage-{index}.stderr")})
        if code:
            aggregate = 1
        snapshot(evidence)
    (evidence / "aggregate.native-exit").write_text(str(aggregate) + "\n")
    return aggregate


def finish(work, evidence, manifest):
    save(evidence / "source-after.json", source_pins(work, manifest))
    build = work / ".lake/build/lib/lean"
    expected = {}
    for rel in manifest["project_sources"]:
        obj = ".lake/build/lib/lean/" + rel.removeprefix("lean/").removesuffix(".lean") + ".olean"
        if (work / obj).is_file():
            expected[obj] = digest(work / obj)
    save(evidence / "compiled-project-objects.json", expected)
    save(evidence / "object-after.json", object_pins(build / "PvNP", work))
    (evidence / "finished.utc").write_text(utc() + "\n")


def main():
    action, evidence_path = sys.argv[1:]
    work = Path.cwd()
    evidence = Path(evidence_path)
    manifest = json.loads((work / "capture-manifest.json").read_bytes())
    identity = require_gcp(manifest)
    if action == "begin":
        begin(work, evidence, manifest, identity)
    elif action == "compile":
        return compile_stages(work, evidence, manifest, identity)
    elif action == "finish":
        finish(work, evidence, manifest)
    elif action == "snapshot":
        snapshot(evidence)
    else:
        raise ValueError("Unknown GCP helper action: " + action)
    return 0


if __name__ == "__main__":
    sys.exit(main())
