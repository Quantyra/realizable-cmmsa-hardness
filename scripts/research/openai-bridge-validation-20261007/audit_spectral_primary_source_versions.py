"""Verify preserved primary source bytes and labelled proof custody; never execute TeX."""
import hashlib
import json
from pathlib import Path
import re
import tarfile

ROOT = Path('C:/Users/dfred/.quantyra/source-verification/spectral-primary-20261009-v1')
HERE = Path(__file__).parent
PINS = {
    'mz-v1.pdf': '01E2D99CEC90778BB8401B8D8528BEC8E28C111E1264823CF089A839319FB47C',
    'mz-v1-source.tar': '7FCE2E66A2AE99B502D4F4DA79F0236257A4F6C0304E1E4DA7AA0C0CA3001B65',
    'mz24-arxiv-v4-source.tar': '252D1F5940F8EE809F5396366105CBDBFFACD114D44F212F5466377BEB665553',
    'mz24-eccc-r1-windows.pdf': '13B8EB55F86CFE28AC8B283FE83612889B335E14B7A87D64D479451693C7DFF4',
    'mz24-arxiv-v4.pdf': '3B2F8711CABC27C6FA6CA6F1BCC392D1D8E9F6C9C4EC642080537DBFE65C19CB',
}


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def proof_block(text, label):
    at = text.index('\\label{' + label + '}')
    start = text.rfind('\\begin{lemma}', 0, at)
    assert start >= 0
    begin = text.index('\\begin{proof}', at)
    depth = 0
    end = None
    for token in re.finditer(r'\\(begin|end)\{proof\}', text[begin:]):
        depth += 1 if token.group(1) == 'begin' else -1
        if depth == 0:
            end = begin + token.end()
            break
    assert end is not None
    data = text[start:end].encode('utf-8')
    return dict(label=label, start_line=text[:start].count('\n') + 1,
                bytes=len(data), sha256=sha(data), nested_proof_boundaries_preserved=True)


def main():
    files = []
    for name, pin in PINS.items():
        b = (ROOT / name).read_bytes()
        assert sha(b) == pin
        if name.endswith('.pdf'):
            assert b.startswith(b'%PDF')
        files.append(dict(name=name, bytes=len(b), sha256=pin))
    blocks = []
    for name, member, labels in [
        ('mz-v1-source.tar', 'k_query_grassmann.tex', ['lm: not increase norm']),
        ('mz24-arxiv-v4-source.tar', 'appendix_sections/Fourier_appendix.tex',
         ['lm: level d basis invariant', 'lm: adjoint', 'lm: phi', 'lm: eigenvalue calcs']),
    ]:
        with tarfile.open(ROOT / name) as archive:
            data = archive.extractfile(member).read()
        text = data.decode('utf-8')
        blocks.append(dict(archive=name, archive_sha256=PINS[name], member=member,
                           bytes=len(data), member_sha256=sha(data),
                           labelled_lemma_and_complete_proof_blocks=[proof_block(text, label) for label in labels]))
    assert (ROOT / 'mz24-arxiv-v4.pdf').read_bytes() != (ROOT / 'mz24-eccc-r1-windows.pdf').read_bytes()
    receipt = (ROOT / 'download-receipt.json').read_bytes()
    metadata = (ROOT / 'version-custody.json').read_bytes()
    value = dict(schema='spectral-primary-source-version-and-proof-custody-v1', files=files,
        downloaded_receipt_sha256=sha(receipt), version_custody_sha256=sha(metadata), proof_members=blocks,
        MZ_v1_and_MZ24_v4_sources_match_historical_pins=True,
        ECCC_revision1_PDF_matches_historical_pin=True,
        ECCC_revision1_and_arxiv_v4_PDF_bytes_equal=False,
        bibliography_revision1_is_ECCC_number_not_arxiv_v1=True,
        root_source_shape_crosswalk=dict(T='Unrestricted append in MZ Section4.2 and MZ24 AppendixA',
            G='Uniform full-column-rank restriction', Phi='Unrestricted B, full-row-rank C',
            adjoint='Restricted to invariant first argument',
            exact_lambda='Reconstructed count identity; cited A.13 states a weaker bound, not our exact formula'),
        source_notation_issues_retained=['A.11 uses G/H inconsistently and gives an n-row description for A inverse J whose row count is2ell',
            'A.13 chooses S A transpose but displayed covariance produces S A; local direct kernel-frame route avoids copying this notation'],
        PDF_screenshot_attempt='ECCC pages75-77 zero-index returned cache-miss; no visual QA claimed',
        ECCC_selected_equations_text_inspected_pages_one_indexed=[75, 76, 77, 78],
        whole_PDF_normalized_text_or_byte_equivalence_claimed=False,
        raw_sources_unchanged_and_not_executed=True, independent_source_manuscript_crosswalk_pending=True,
        native_verification=False, novelty_or_priority_claim=False, overall_GO=False, full_goal_complete=False)
    p = HERE / 'spectral-primary-source-version-audit-v1.json'
    data = (json.dumps(value, indent=2) + '\n').encode('utf-8')
    if p.exists():
        assert p.read_bytes() == data
    else:
        with p.open('xb') as stream:
            stream.write(data)
    print(json.dumps(dict(audit_sha256=sha(data), primary_files_verified=5,
        complete_labelled_proofs=5, ECCC_arxiv_PDF_same=False, native_verification=False)))


if __name__ == '__main__':
    main()
