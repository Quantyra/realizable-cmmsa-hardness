from pathlib import Path
import hashlib
import json
import subprocess

S = Path(__file__).resolve().parent
P = Path(r'C:\Users\dfred\Desktop\Projects\IGH\Quantyra-AI-Planning')
manifest = json.loads((S / 'numeric-selected-coordinate-mass-offer-20261011-v1/manifest.json').read_text(encoding='utf-8'))
record = manifest['planning_argument']
relative = 'docs/research/pvnp/full90-actual-rhs-numeric-no-obligations-2026-10-08.md'
git_raw = subprocess.run(['git', '-C', str(P), 'show', '9a9cb09:' + relative],
                         check=True, stdout=subprocess.PIPE).stdout
sha = lambda b: hashlib.sha256(b).hexdigest().upper()
expected = record['sha256']
current = (P / relative).read_bytes()
marker = b'## 2026-10-11 The full supplied advice tuple and its used prefix'
assert current.count(marker) == 1
prefix = current[:current.index(marker)]
candidates = [git_raw, git_raw.replace(b'\n', b'\r\n'), prefix,
              prefix.rstrip(b'\r\n') + b'\n', prefix.rstrip(b'\r\n') + b'\r\n']
matches = [data for data in candidates if sha(data) == expected]
assert matches, dict(expected=expected, candidates=[dict(bytes=len(x), sha256=sha(x)) for x in candidates])
raw = matches[0]
assert raw.replace(b'\r\n', b'\n') == git_raw
out = S / 'numeric-selected-coordinate-mass-planning-custody-v1'
out.mkdir(exist_ok=False)
(out / 'argument-parent.md').write_bytes(raw)
(out / '.gitattributes').write_bytes(b'* -text\n')
receipt = dict(source_commit='9a9cb09', source_path=relative, bytes=len(raw),
               sha256=sha(raw), git_normalized_sha256=sha(git_raw),
               exact_old_working_bytes_reconstructed_by_matching_offered_sha256=True,
               normalized_content_equals_committed_blob=True,
               offer_manifest_unchanged=True, current_planning_note_may_advance=True,
               prior_attempt=dict(control='preserve_selected_coordinate_planning_parent_v1.py',
                   terminal_exit=1, terminal_chunk='32ed19', failure='Expected working-file hash differs from normalized Git blob',
                   output_directory_created=False), accepted=False)
(out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8', newline='\n')
print(json.dumps(receipt))
