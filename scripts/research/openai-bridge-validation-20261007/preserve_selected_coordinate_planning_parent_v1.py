from pathlib import Path
import hashlib
import json
import subprocess

S = Path(__file__).resolve().parent
P = Path(r'C:\Users\dfred\Desktop\Projects\IGH\Quantyra-AI-Planning')
manifest = json.loads((S / 'numeric-selected-coordinate-mass-offer-20261011-v1/manifest.json').read_text(encoding='utf-8'))
record = manifest['planning_argument']
relative = 'docs/research/pvnp/full90-actual-rhs-numeric-no-obligations-2026-10-08.md'
raw = subprocess.run(['git', '-C', str(P), 'show', '9a9cb09:' + relative],
                     check=True, stdout=subprocess.PIPE).stdout
sha = lambda b: hashlib.sha256(b).hexdigest().upper()
expected = record['sha256']
assert sha(raw) == expected, dict(expected=expected, actual=sha(raw))
out = S / 'numeric-selected-coordinate-mass-planning-custody-v1'
out.mkdir(exist_ok=False)
(out / 'argument-parent.md').write_bytes(raw)
(out / '.gitattributes').write_bytes(b'* -text\n')
receipt = dict(source_commit='9a9cb09', source_path=relative, bytes=len(raw),
               sha256=sha(raw), offer_manifest_unchanged=True,
               current_planning_note_may_advance=True, accepted=False)
(out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8', newline='\n')
print(json.dumps(receipt))
