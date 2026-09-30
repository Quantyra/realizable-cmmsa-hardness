"""Scoped receipt audit; does not certify classical inhabitants or full core."""
import hashlib
import json
import pathlib
import re
import tarfile

ROOT = pathlib.Path(__file__).resolve().parents[3]
HERE = pathlib.Path(__file__).resolve().parent
manifest = json.loads((HERE / "material-claims-manifest.json").read_text(encoding="utf-8"))
run = HERE / manifest["run"]
archive = run / (run.name + "-evidence.tar.gz")
assert hashlib.sha256(archive.read_bytes()).hexdigest() == manifest["evidence_archive_sha256"]
with tarfile.open(archive) as receipt:
    raw = {pathlib.PurePosixPath(m.name).name: receipt.extractfile(m).read()
           for m in receipt.getmembers() if m.isfile()}
assert all(int(raw[n].decode().strip()) == 0 for n in
           ["native-exit", "prebuild-0.native-exit", "prebuild-1.native-exit"])
pins = dict(line.split(None, 1)[::-1] for line in raw["pins.sha256"].decode().splitlines())
for name, expected in manifest["sources"].items():
    assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == expected, name
    assert pins[name] == expected, name
text = raw["build.stdout"].decode("utf-8")
assert "Build completed successfully" in text
assert not re.search(r"^error:", text, re.M)
assert "sorryAx" not in text
profiles = {}
for export in manifest["axiom_exports"]:
    name = "PvNP.RealizableHardness." + export
    found = re.findall(re.escape("'" + name + "' depends on axioms:") +
                       r"\s*\[([^\]]*)\]", text)
    assert len(found) == 1, name
    axioms = [a.strip() for a in found[0].split(",") if a.strip()]
    assert set(axioms) <= set(manifest["allowed_axioms"]), (name, axioms)
    profiles[name] = axioms
objects = {name: digest for name, digest in pins.items() if name.endswith(".olean")}
assert len(objects) == 3
report = {"success": True, "audit_scope": "actual native receipt/source/profile consistency only",
          "archive_sha256": manifest["evidence_archive_sha256"],
          "source_pins": manifest["sources"], "object_pins": objects,
          "native_exit_codes": [0, 0, 0], "axiom_profiles": profiles,
          "final_three_lens_acceptance": "not evaluated by this receipt audit; see independent reviews and ledger",
          "open_debts": manifest["open_debts"]}
(HERE / "material-claims-audit-result.json").write_text(
    json.dumps(report, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"success": True, "verified_profiles": len(profiles),
                  "verified_source_pins": len(manifest["sources"]),
                  "verified_object_receipt_pins": len(objects)}))
