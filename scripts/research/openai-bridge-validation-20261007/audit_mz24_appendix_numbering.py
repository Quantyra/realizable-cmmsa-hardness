"""Bounded pinned-source counter audit; does not execute TeX or assert PDF QA."""
import json
import re
import tarfile
from pathlib import Path
from audit_spectral_primary_source_versions import ROOT, PINS, sha


def uncomment(text):
    return '\n'.join(re.split(r'(?<!\\)%', line, maxsplit=1)[0] for line in text.splitlines())


def main():
    name = 'mz24-arxiv-v4-source.tar'
    archive_bytes = (ROOT / name).read_bytes()
    assert sha(archive_bytes) == PINS[name]
    with tarfile.open(ROOT / name) as archive:
        bodies = {p: archive.extractfile(p).read() for p in
                  ['main.tex', 'appendix.tex', 'appendix_sections/Fourier_appendix.tex']}
    maintext = uncomment(bodies['main.tex'].decode())
    assert r'\newtheorem{thm}{Theorem}[section]' in maintext
    shared = re.findall(r'\\newtheorem\{([^}]+)\}\[thm\]', maintext)
    assert 'lemma' in shared and 'claim' in shared
    assert maintext.index(r'\appendix') < maintext.index(r'\input{appendix}')
    appendix = uncomment(bodies['appendix.tex'].decode())
    assert appendix.lstrip().startswith(r'\input{appendix_sections/Fourier_appendix}')
    text = uncomment(bodies['appendix_sections/Fourier_appendix.tex'].decode())
    assert text.lstrip().startswith(r'\section{')
    assert not re.search(r'\\(?:setcounter|addtocounter|stepcounter|refstepcounter|include|input)\b', text)
    counter = 0
    rows = []
    for match in re.finditer(r'\\begin\{([^}]+)\}', text):
        environment = match.group(1)
        if environment not in shared + ['thm']:
            continue
        counter += 1
        end = text.index(r'\end{' + environment + '}', match.end())
        labels = re.findall(r'\\label\{([^}]+)\}', text[match.end():end])
        rows.append(dict(environment=environment, number='A.' + str(counter), labels=labels))
    expected = {'lm: level d basis invariant': 'A.10', 'lm: adjoint': 'A.11',
                'lm: phi': 'A.12', 'lm: eigenvalue calcs': 'A.13',
                'claim:what_if_non_zero_w': 'A.14', 'lm: degree inner': 'A.15',
                'lm: pseudorandom edges over bilinear scheme': 'A.16',
                'lm: level d intermediate lemma 1': 'A.17',
                'lm: preserve pseudorandom': 'A.18', 'lm: edge count preserved': 'A.19'}
    observed = {label: row['number'] for row in rows for label in row['labels']}
    assert all(observed[label] == number for label, number in expected.items())
    result = dict(schema='mz24-v4-pinned-source-appendix-counter-audit-v1',
                  archive=name, archive_sha256=PINS[name],
                  member_identities={p: dict(bytes=len(b), sha256=sha(b)) for p, b in bodies.items()},
                  shared_thm_counter_environments=shared, counter_rows=rows,
                  checked_labels=expected, claim_shares_lemma_counter=True,
                  preserve_pseudorandom_source_number='A.18',
                  scope='bounded source/preamble audit; no TeX execution or PDF numbering confirmation',
                  PDF_confirmed=False, native_verified=False, overall_GO=False)
    data = (json.dumps(result, indent=2) + '\n').encode()
    path = Path(__file__).with_name('mz24-appendix-numbering-audit-v1.json')
    if path.exists():
        assert path.read_bytes() == data
    else:
        path.write_bytes(data)
    print(json.dumps(dict(audit_sha256=sha(data), labels=len(expected), preserve_pseudorandom='A.18', PDF_confirmed=False)))


if __name__ == '__main__':
    main()
