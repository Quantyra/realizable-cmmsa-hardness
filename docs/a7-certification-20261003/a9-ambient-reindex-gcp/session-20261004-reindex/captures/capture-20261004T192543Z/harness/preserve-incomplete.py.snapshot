"""Preserve an interrupted offline capture; no deletion, compiler, or cloud calls."""
import argparse
import gzip
import json
import re
import shutil

from common import PACKAGE, REPO, FROZEN, file_sha, utc, write_new, json_bytes, local_process_check


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--capture", required=True)
    args = parser.parse_args()
    if not re.fullmatch(r"capture-[A-Za-z0-9_-]+", args.capture):
        raise ValueError("Invalid capture name")
    folder = PACKAGE / "captures" / args.capture
    if (folder / "manifest.json").exists():
        raise ValueError("Refusing to rewrite a completed immutable capture")
    status = folder / "status-before.txt"
    compressed = folder / "status-before.txt.gz"
    with status.open("rb") as source, compressed.open("xb") as raw:
        with gzip.GzipFile(fileobj=raw, mode="wb", filename="", mtime=0) as target:
            shutil.copyfileobj(source, target)
    import hashlib
    with gzip.open(compressed, "rb") as source:
        reconstructed = hashlib.file_digest(source, "sha256").hexdigest().upper()
    if reconstructed != file_sha(status):
        raise ValueError("Compressed interrupted status does not preserve the exact raw bytes")
    scripts = {}
    for name in ["prepare.py", "common.py"]:
        snapshot = folder / ("executed-" + name + ".snapshot")
        write_new(snapshot, (PACKAGE / name).read_bytes())
        scripts[name] = file_sha(snapshot)
    for rel, expected in FROZEN.items():
        if file_sha(REPO / rel) != expected:
            raise ValueError("Frozen identity changed during interrupted offline preparation")
    write_new(folder / "incomplete-attempt.json", json_bytes({"utc": utc(),
        "status": "PREPARATION_INTERRUPTED", "certified": False, "local_compilation": False,
        "gcloud_invocations": 0, "resource_mutations": 0,
        "reason": "Full untracked inventory produced a 331 MB path listing; all-file hashing was interrupted. "
                  "Successor capture uses tracked dirty files, untracked Lean files, and directory-level Git status.",
        "raw_status_sha256": file_sha(status), "raw_status_bytes": status.stat().st_size,
        "compressed_status_sha256": file_sha(compressed), "compressed_status_bytes": compressed.stat().st_size,
        "compressed_reconstruction_verified": True, "raw_status_retained_locally": True,
        "tracked_diff_sha256": file_sha(folder / "inherited-tracked-diff-before.patch"),
        "executed_script_hashes": scripts, "frozen_identities": FROZEN,
        "local_process_check_after": local_process_check()}))
    print(json.dumps({"capture": args.capture, "compressed_status_bytes": compressed.stat().st_size,
                      "raw_bytes_preserved": status.stat().st_size, "certified": False}, indent=2))


if __name__ == "__main__":
    main()
