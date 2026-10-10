"""Run the existing paper builder on an isolated, hash-pinned source copy.

Preserve one invocation and terminal logs; a PDF build supplies no formal,
mathematical, novelty, publication, or independent visual acceptance.
"""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    root, texbin = (Path(arg).resolve() for arg in sys.argv[1:])
    pins = json.loads((root/'source-pins.json').read_bytes())
    for row in pins:
        data = (root/row['file']).read_bytes()
        assert len(data) == row['bytes'] and sha(data) == row['sha256'], row['file']
    assert (texbin/'pdflatex.exe').is_file() and (texbin/'bibtex.exe').is_file()
    env = dict(os.environ)
    env['PATH'] = str(texbin)+os.pathsep+str(Path(sys.executable).parent)+os.pathsep+env['PATH']
    env['SOURCE_DATE_EPOCH'] = '1789171200'
    env['FORCE_SOURCE_DATE'] = '1'
    command = [sys.executable, '-B', '-X', 'utf8', str(root/'paper/build.py')]
    with (root/'build-once.json').open('x', encoding='utf-8') as file:
        json.dump(dict(command=command, source_pins_sha256=sha((root/'source-pins.json').read_bytes()),
                       texbin=str(texbin)), file, indent=2)
    with (root/'build.stdout').open('xb') as stdout, (root/'build.stderr').open('xb') as stderr:
        native = subprocess.run(command, cwd=root, env=env, stdout=stdout, stderr=stderr)
    pdf = root/'output/pdf/realizable-hardness.pdf'
    record = dict(native_exit=native.returncode, command=command,
                  stdout_sha256=sha((root/'build.stdout').read_bytes()),
                  stderr_sha256=sha((root/'build.stderr').read_bytes()),
                  PDF_built=native.returncode == 0 and pdf.is_file(),
                  independent_visual_QA=False, mathematical_acceptance=False,
                  formal_certification=False, publication_acceptance=False)
    if record['PDF_built']:
        record.update(pdf_bytes=pdf.stat().st_size, pdf_sha256=sha(pdf.read_bytes()))
    for row in pins:
        data = (root/row['file']).read_bytes()
        assert len(data) == row['bytes'] and sha(data) == row['sha256'], row['file']
    record['all_seven_source_pins_unchanged'] = True
    with (root/'build-terminal.json').open('x', encoding='utf-8') as file:
        json.dump(record, file, indent=2); file.write('\n')
    print(json.dumps(record))
    raise SystemExit(native.returncode)


if __name__ == '__main__':
    main()
