"""Revalidate completed v5 QA/citation custody; no fresh visual or proof review."""
from datetime import datetime, timezone
import gzip
import hashlib
import io
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile

sys.path.insert(0, 'C:/Users/dfred/.quantyra/tools/pdf-audit-pypdf')
from pypdf import PdfReader, __version__

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
DEST = HERE / 'draft-v5-qa-citation-reconciliation-v1'
QA = HERE / 'draft-author-visual-qa-v5/author-qa.json'
CITATION = REPO / 'paper/mz24-compiled-citation-numbering-current-draft-2026-10-09.json'
QA_PIN = 'CEF04411A254485BA8F0362D5B33B49606D2F3E5340B726E71DFC9032673D9E6'
CITATION_PIN = 'D9C6626DF314C8B9632F9F29251FC7FFF7F97F25BFBABE9E458E3EF554873CE4'
PDF_PIN = '3A25A4CFEFFB213F3AE4FB7934BCFFC3BDB3CC99300C6F9D1C55B5110E5C606E'
RESERVE = 1536 * 1024**2


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def git_bytes(commit, path):
    return subprocess.check_output(['git', '-C', str(REPO), 'cat-file', 'blob',
                                    commit + ':' + path.relative_to(REPO).as_posix()])


def main():
    assert not DEST.exists(), 'Never replace an existing reconciliation'
    assert sha(QA.read_bytes()) == QA_PIN and sha(CITATION.read_bytes()) == CITATION_PIN
    assert QA.read_bytes() == git_bytes('94d700473598d87aafbf4419ba0c2e93ff98b12b', QA)
    assert CITATION.read_bytes() == git_bytes('5995f14ff1cd2d4e5cea53196a470cdd6b256937', CITATION)
    qa, citation = json.loads(QA.read_bytes()), json.loads(CITATION.read_bytes())
    assert citation['pypdf_version'] == __version__
    build = Path(citation['build_directory'])
    pdf = build / 'output/pdf/realizable-hardness.pdf'
    saved_pdf = HERE / 'draft-disclosure-notation-repair-build-v5/draft.pdf'
    assert pdf.read_bytes() == saved_pdf.read_bytes() and sha(pdf.read_bytes()) == PDF_PIN
    assert qa['pdf_sha256'] == citation['manuscript_PDF_sha256'] == PDF_PIN
    assert qa['pdf_bytes'] == len(pdf.read_bytes()) == 617041
    assert len(PdfReader(pdf).pages) == citation['manuscript_PDF_pages'] == 32
    assert qa['inspected_pages'] == list(range(1, 33)) and qa['skipped_pages'] == []
    assert qa['render_native_exit'] == 0 and len(qa['images']) == 32
    assert not qa['font_level_inspection'] and not qa['source_transcription_reaudit']
    images = {}
    for number, row in enumerate(qa['images'], 1):
        path = Path(row['path'])
        assert path.name == f'page-{number:02d}.png'
        assert path.parent == build / 'author-page-images'
        data = path.read_bytes()
        assert len(data) == row['bytes'] and sha(data) == row['sha256']
        images[path.name] = data
    pins_path = build / 'source-pins.json'
    pins = json.loads(pins_path.read_bytes())
    assert len(pins) == 7
    for row in pins:
        path = REPO / row['file']
        data = path.read_bytes() if path.is_file() else git_bytes('HEAD', path)
        assert len(data) == row['bytes'] and sha(data) == row['sha256']
    terminal = json.loads((build / 'build-terminal.json').read_bytes())
    assert terminal['native_exit'] == 0 and terminal['pdf_sha256'] == PDF_PIN
    assert sha((REPO / 'paper/submission-manuscript.md').read_bytes()) == citation['manuscript_sha256']
    bibliography = git_bytes('HEAD', REPO / 'paper/references.bib')
    assert sha(bibliography) == citation['bibliography_sha256']
    entry = re.search(rb'@misc\{MZ24,(.*?)\n\}', bibliography, re.S).group(1)
    assert b'year={2026}' in entry and re.search(rb'ECCC TR24-027, revision 1, 13 May(?: 2026)?\}', entry)
    assert b'https://eccc.weizmann.ac.il/report/2024/027/revision/1/download/' in bibliography
    primary = Path(citation['primary_pdfs'][0]['file']).parent
    assert sha((primary / 'mz24-arxiv-v4-source.tar').read_bytes()) == citation['source_archive_sha256']
    with tarfile.open(primary / 'mz24-arxiv-v4-source.tar') as archive:
        main_tex = archive.extractfile('main.tex').read()
        fourier = archive.extractfile('appendix_sections/Fourier_appendix.tex').read()
    assert b'\\newtheorem{lemma}[thm]{Lemma}' in main_tex
    assert b'\\newtheorem{claim}[thm]{Claim}' in main_tex
    assert all(label.encode() in fourier for label in citation['source_labels'])
    primary_rows = []
    for row in citation['primary_pdfs']:
        path = Path(row['file'])
        assert path.stat().st_size == row['bytes'] and sha(path.read_bytes()) == row['sha256']
        reader = PdfReader(path)
        assert len(reader.pages) == row['pages'] == 106
        assert [item['statement'] for item in row['statements']] == ['A.13', 'A.17', 'A.18']
        for statement in row['statements']:
            text = reader.pages[statement['pdf_page_one_based'] - 1].extract_text()
            assert sha(text.encode()) == statement['extracted_page_sha256']
            number = statement['statement'].split('.')[1]
            assert re.search(rf'Lemma\s+A\.?\s*{number}\.', text)
        primary_rows.append(row)
    assert len(primary_rows) == 2 and primary_rows[0]['sha256'] != primary_rows[1]['sha256']
    manuscript = (REPO / 'paper/submission-manuscript.md').read_bytes()
    assert b'Lemmas~A.17--A.18' in manuscript
    assert b'MZ24 Lemma~A.13 states the weaker eigenvalue bound' in manuscript
    independent = HERE / 'draft-independent-visual-content-report-v5'
    disposition = json.loads((independent / 'root-disposition.json').read_bytes())
    assert disposition['native_exit'] == 0 and disposition['all32_pages_inspected']
    assert disposition['actual_context_fit'] and disposition['overall'] == 'NO GO'
    assert json.loads((independent / 'live.json').read_bytes())['pdf_sha256'] == PDF_PIN
    for record in (qa, disposition):
        for key in ('mathematical_acceptance', 'formal_certification', 'novelty_clearance', 'publication_clearance'):
            assert record[key] is False
    assert not citation['mathematical_acceptance'] and not citation['novelty_clearance']
    before = shutil.disk_usage(HERE).free
    assert before >= RESERVE + 3 * (sum(map(len, images.values())) + pdf.stat().st_size)
    DEST.mkdir()
    (DEST / '.gitattributes').write_bytes(b'* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    archive_path = DEST / 'author-page-images.tar.gz'
    with archive_path.open('xb') as raw:
        with gzip.GzipFile(filename='', mode='wb', fileobj=raw, mtime=0) as compressed:
            with tarfile.open(fileobj=compressed, mode='w') as archive:
                for name, data in images.items():
                    member = tarfile.TarInfo(name)
                    member.size, member.mode, member.mtime = len(data), 0o644, 0
                    archive.addfile(member, io.BytesIO(data))
    with tarfile.open(archive_path, 'r:gz') as archive:
        assert {m.name: archive.extractfile(m).read() for m in archive.getmembers()} == images
    copies = [(QA, 'author-qa.original.json'), (CITATION, 'citation-audit.original.json'),
              (pdf, 'draft.original.pdf'), (pins_path, 'source-pins.original.json'),
              (build / 'build-terminal.json', 'build-terminal.original.json'),
              (independent / 'report.md', 'independent-report.original.md'),
              (independent / 'root-disposition.json', 'independent-disposition.original.json'),
              (Path(__file__), 'reconciliation-control.snapshot.py')]
    rows = []
    for path, name in copies:
        data = path.read_bytes()
        (DEST / name).open('xb').write(data)
        assert (DEST / name).read_bytes() == data
        rows.append(dict(original=str(path), copy=name, bytes=len(data), sha256=sha(data)))
    after = shutil.disk_usage(HERE).free
    assert after >= RESERVE
    result = dict(schema='draft-v5-qa-citation-reconciliation-v1', utc=datetime.now(timezone.utc).isoformat(),
                  qa_source_commit='94d700473598d87aafbf4419ba0c2e93ff98b12b',
                  citation_source_commit='5995f14ff1cd2d4e5cea53196a470cdd6b256937',
                  copies=rows, author_images=qa['images'], complete_image_archive_sha256=sha(archive_path.read_bytes()),
                  complete_image_roundtrip_passed=True, image_bytes=sum(map(len, images.values())),
                  existing_all32_author_visual_QA_receipt_revalidated=True,
                  existing_independent_all32_review_receipt_revalidated=True,
                  all_seven_current_source_pins_verified=True,
                  primary_pdfs=primary_rows, scoped_A13_A17_A18_numbering_reverified=True,
                  current32_page_PDF_sha256=PDF_PIN, minor_findings_retained=qa['findings'],
                  stale_pending_author_QA_and_current_citation_status_should_be_corrected=True,
                  fresh_visual_review_performed=False, new_PDF_rendered=False,
                  full_bibliography_and_novelty_audit_complete=False,
                  mathematical_acceptance=False, formal_certification=False,
                  novelty_clearance=False, publication_clearance=False, full_goal_complete=False,
                  local_free_before=before, local_free_after=after, minimum_reserve_bytes=RESERVE)
    (DEST / 'reconciliation.json').open('x', encoding='utf-8').write(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(destination=str(DEST), image_count=len(images), source_pins=7,
                          primary_pdfs=2, statement_number_checks=6,
                          reconciliation_sha256=sha((DEST / 'reconciliation.json').read_bytes()),
                          fresh_visual_review=False, mathematical_acceptance=False)))


if __name__ == '__main__':
    main()
