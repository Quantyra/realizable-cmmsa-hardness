"""One top-level visual/content review of the exact PDF and complete source."""
from pathlib import Path
import base64
import hashlib
import json
import subprocess
import sys

ROOT = Path('C:/Users/dfred/.quantyra/manuscript-builds/spectral-attribution-20261009-v3')


def main():
    root = Path(sys.argv[1]) if len(sys.argv) == 3 else ROOT
    expected_pdf = sys.argv[2] if len(sys.argv) == 3 else 'CBA8E3A3B98B9A71D9C8558297803FD6BBF24F5D665F482AB2A821CBB0D0EBA4'
    folder = root/('independent-visual-content-review-v1' if root != ROOT else 'independent-visual-content-review-v2')
    if root == ROOT:
        prior = ROOT/'independent-visual-content-review-v1'
        assert int((prior/'native-exit.txt').read_text()) == 1
        assert '--input-format=stream-json requires output-format=stream-json' in (prior/'stderr.txt').read_text()
    folder.mkdir(exist_ok=False)
    pdf = (root/'output/pdf/realizable-hardness.pdf').read_bytes()
    sha = lambda b: hashlib.sha256(b).hexdigest().upper()
    assert sha(pdf) == expected_pdf
    pins = json.loads((root/'source-pins.json').read_bytes())
    bodies = []
    for row in pins:
        body = (root/row['file']).read_bytes()
        assert len(body) == row['bytes'] and sha(body) == row['sha256']
        bodies.append('\nFILE '+row['file']+' SHA256 '+row['sha256']+'\n'+body.decode('utf-8'))
    prompt = '''You are the independent all-page visual and source-to-PDF content reviewer.
Inspect every one of the 31 PDF pages, not a sample. Report a per-page visual
coverage table and explicit skipped pages. Compare the complete canonical source,
generated body, preamble, bibliography and source correspondence supplied below.
Check glyphs, equations, clipping, overlaps, table/proof transitions, references,
URLs, the page9 MZ24 A.13 attribution and page31 bibliography. Eight bibliography
underfull notices exist; assess them directly. Separate visual/content acceptance
from mathematical proof, formal certification, novelty and publication clearance.
Full105 has conditional scoped three-lens acceptance only; runtime/source and
exact product/G-Phi/adjoint manuscript native identities remain open. No overall GO.
Use no tools, writes, Lean, Lake, network or subagents. If PDF visual content is
unavailable, say INCOMPLETE and do not invent page coverage. Give separate visual,
transcription, claims-boundary and overall verdicts with concrete findings.
''' + ''.join(bodies)
    content = [dict(type='document', source=dict(type='base64', media_type='application/pdf',
                                               data=base64.b64encode(pdf).decode())),
               dict(type='text', text=prompt)]
    payload = (json.dumps(dict(type='user', message=dict(role='user', content=content)))+'\n').encode()
    assert len(payload) < 10_000_000
    (folder/'input.jsonl').write_bytes(payload)
    command = ['C:/Users/dfred/.local/bin/claude.exe', '--print', '--model', 'claude-opus-5-5[1m]',
               '--input-format', 'stream-json', '--output-format', 'stream-json', '--verbose', '--tools', '', '--no-session-persistence']
    (folder/'command.json').write_text(json.dumps(command)+'\n')
    child = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE, cwd=folder, creationflags=subprocess.CREATE_NO_WINDOW)
    (folder/'live.json').write_text(json.dumps(dict(pid=child.pid, input_sha256=sha(payload),
                                                  pdf_sha256=sha(pdf)))+'\n')
    first = True
    while True:
        try:
            out, err = child.communicate(input=payload if first else None, timeout=30)
            break
        except subprocess.TimeoutExpired:
            first = False
            print('Same independent PDF reviewer remains live', child.pid, flush=True)
    (folder/'stdout.json').write_bytes(out)
    (folder/'stderr.txt').write_bytes(err)
    (folder/'native-exit.txt').write_text(str(child.returncode)+'\n')
    print(json.dumps(dict(native_exit=child.returncode, stdout_bytes=len(out), stderr_bytes=len(err))), flush=True)
    raise SystemExit(child.returncode)


if __name__ == '__main__':
    main()
