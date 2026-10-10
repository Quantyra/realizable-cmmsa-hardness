"""Verify scoped citation numbering against two distinct preserved primary PDFs.

PDF text extraction verifies printed statement numbers, not visual quality or
mathematical acceptance. Dependencies are isolated from the cloud SDK runtime.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tarfile

sys.path.insert(0, 'C:/Users/dfred/.quantyra/tools/pdf-audit-pypdf')
from pypdf import PdfReader, __version__

ROOT = Path(__file__).resolve().parents[3]
PRIMARY = Path('C:/Users/dfred/.quantyra/source-verification/spectral-primary-20261009-v1')
sha = lambda data: hashlib.sha256(data).hexdigest().upper()


def main():
    source = PRIMARY/'mz24-arxiv-v4-source.tar'
    with tarfile.open(source) as archive:
        main_tex = archive.extractfile('main.tex').read()
        fourier = archive.extractfile('appendix_sections/Fourier_appendix.tex').read()
    assert b'\\newtheorem{lemma}[thm]{Lemma}' in main_tex
    assert b'\\newtheorem{claim}[thm]{Claim}' in main_tex
    labels = ['lm: eigenvalue calcs', 'lm: level d intermediate lemma 1', 'lm: preserve pseudorandom']
    assert all(label.encode() in fourier for label in labels)
    statements = {13: (77, 'weaker eigenvalue bound'),
                  17: (80, 'affine restriction intermediate reduction'),
                  18: (82, 'Grassmann-to-matrix pseudorandomness preservation')}
    rows = []
    for name in ['mz24-arxiv-v4.pdf', 'mz24-eccc-r1-windows.pdf']:
        pdf = PRIMARY/name
        reader = PdfReader(pdf)
        assert len(reader.pages) == 106
        entries = []
        for number, (page, description) in statements.items():
            text = reader.pages[page-1].extract_text()
            pattern = rf'Lemma\s+A\.?\s*{number}\.'
            assert re.search(pattern, text), (name, page, number)
            entries.append(dict(statement=f'A.{number}', pdf_page_one_based=page,
                                extracted_page_sha256=sha(text.encode()),
                                statement_number_present=True, interpretation=description))
        rows.append(dict(file=str(pdf), bytes=pdf.stat().st_size,
                         sha256=sha(pdf.read_bytes()), pages=106, statements=entries))
    assert rows[0]['sha256'] != rows[1]['sha256']
    bib = subprocess.check_output(['git', 'show', 'HEAD:paper/references.bib'], cwd=ROOT)
    entry = re.search(rb'@misc\{MZ24,(.*?)\n\}', bib, re.S).group(1)
    assert b'year={2026}' in entry
    assert re.search(rb'ECCC TR24-027, revision 1, 13 May(?: 2026)?\}', entry)
    assert b'https://eccc.weizmann.ac.il/report/2024/027/revision/1/download/' in bib
    manuscript = (ROOT/'paper/submission-manuscript.md').read_bytes()
    assert b'Lemmas~A.17--A.18' in manuscript
    assert b'MZ24 Lemma~A.13 states the weaker eigenvalue bound' in manuscript
    record = dict(schema='mz24-compiled-citation-numbering-v1', pypdf_version=__version__,
                  primary_pdfs=rows, source_archive_sha256=sha(source.read_bytes()),
                  shared_lemma_claim_counter_verified=True, source_labels=labels,
                  bibliography_sha256=sha(bib), bibliography_pins='ECCC revision 1',
                  manuscript_sha256=sha(manuscript), citation_numbering_matches=True,
                  bibliography_change_required=False, distinct_pdf_identities_preserved=True,
                  exact_eigenvalue_is_reconstruction_not_literal_A13=True,
                  manuscript_PDF_rebuilt=False, visual_QA=False,
                  mathematical_acceptance=False, novelty_clearance=False)
    destination = ROOT/'paper/mz24-compiled-citation-numbering-2026-10-09.json'
    if sys.argv[1:] == ['--repaired-source']:
        build = Path('C:/Users/dfred/.quantyra/manuscript-builds/transcription-repair-20261009-v4')
        pins = json.loads((build/'source-pins.json').read_bytes())
        for row in pins:
            current = ROOT/row['file']
            if current.exists():
                assert sha(current.read_bytes()) == row['sha256'], row['file']
        terminal = json.loads((build/'build-terminal.json').read_bytes())
        pdf = (build/'output/pdf/realizable-hardness.pdf').read_bytes()
        assert terminal['native_exit'] == 0 and terminal['pdf_sha256'] == sha(pdf)
        record.update(schema='mz24-compiled-citation-numbering-repaired-source-v2',
                      manuscript_PDF_rebuilt=True, manuscript_PDF_sha256=sha(pdf),
                      inherited_visual_acceptance=False)
        destination = ROOT/'paper/mz24-compiled-citation-numbering-repaired-source-2026-10-09.json'
    elif sys.argv[1:]:
        raise ValueError('Unknown scope')
    with destination.open('x', encoding='utf-8', newline='\n') as output:
        json.dump(record, output, indent=2); output.write('\n')
    print(json.dumps(dict(citation_numbering_matches=True, pdfs=len(rows),
                          statements_per_pdf=3, record_sha256=sha(destination.read_bytes()))))


if __name__ == '__main__':
    main()
