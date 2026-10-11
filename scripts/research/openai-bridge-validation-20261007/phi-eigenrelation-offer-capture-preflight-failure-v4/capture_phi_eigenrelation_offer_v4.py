"""Capture the stable v4 author offer; no compiler or acceptance is invoked."""
import json
from pathlib import Path
from custody_checks import digest

HERE = Path(__file__).resolve().parent
OFFERS = {
    'ExactPhiEigenrelation-v4.lean': 'B1177090ABB0AFA8E09CD9505DD3AC78C9445656C8B20F4C86D66AF325B9CCEE',
    'ExactPhiEigenrelationChecks-v4.lean': 'E0EFF56684477F10E76326E1FDF16BB489A1F1F45342F54FD012847E64E5E1FB',
    'ARGUMENT-AND-API-MAP-v4.md': '6F31E7F2302D4C3A30C4397DC9D1F00ED6BB54374DBA68710DEA6F7964A75509',
}


def main():
    rows = []
    for name, pin in OFFERS.items():
        source = HERE / 'exact-phi-eigenrelation-candidate-v1' / name
        data = source.read_bytes()
        assert digest(source) == pin and not data.startswith(b'\xef\xbb\xbf')
        text = data.decode('utf-8')
        assert '\ufffd' not in text and '\u00e2\u2020' not in text and '\u00c3\u00a2' not in text
        if name.endswith('.lean'):
            assert not any(token in text for token in ('sorry', 'admit', 'axiom '))
        rows.append(dict(original=source.relative_to(HERE).as_posix(), copy=name,
                         bytes=len(data), sha256=pin))
    target = HERE / 'phi-eigenrelation-offer-capture-v4'
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    for row in rows:
        (target / row['copy']).open('xb').write((HERE / row['original']).read_bytes())
        assert digest(target / row['copy']) == row['sha256']
    record = dict(files=rows, immutable_capture_acknowledged=True,
                  root_read_complete_offer=True,
                  utf8_no_bom_and_known_glyph_corruption_checks_passed=True,
                  lean_executed=False, certified=False, accepted=False,
                  full_goal_complete=False, dependency_capture_complete=False,
                  mathematical_target_preserves_arbitrary_real_F_and_unrestricted_B=True,
                  root_static_disposition=[
                      'v3 raw-matrix/subtype mistakes and independence transport directions repaired in the source.',
                      'Explicit scalar and finite-sum linearity supplied; exact native elaboration remains untested.',
                      'Kernel-frame bijection, rank-nullity, impossible-frame branch and product conversion have complete proposed bodies.',
                      'Rank-projection target has no invariance hypothesis and allows empty out-of-range projections without forcing the empty product to zero.',
                      'Checks request three public axiom profiles; no actual profile output exists.',
                      'Final operator contract and the complete qualified import graph must be pinned before GCP launch.',
                  ])
    (target / 'index.json').open('x', encoding='utf-8').write(json.dumps(record, indent=2) + '\n')
    print(json.dumps(dict(folder=str(target), offers=len(rows), accepted=False)))


if __name__ == '__main__':
    main()
