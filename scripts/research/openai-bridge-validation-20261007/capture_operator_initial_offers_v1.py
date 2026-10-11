"""Preserve exact uncompiled initial offers before any successor repairs."""
import json
from pathlib import Path
from custody_checks import digest

HERE = Path(__file__).resolve().parent
OFFERS = {
 'exact-operator-continuation-candidate-v1/ARGUMENT-AND-API-MAP.md': 'E7107470247C38195F1D827BB15512EE532E0C603B184786947941CAC716194E',
 'exact-operator-continuation-candidate-v1/ExactAppendOperatorContracts.lean': '5DD7F28C0349E4A8318B18A41D38B21DAEC814980079B5D0E35E8DB9980307FE',
 'exact-phi-eigenrelation-candidate-v1/ExactPhiEigenrelation.lean': 'D8B8300348D12AAB58E1C63658F8DE1481D25CDAB5C5839EF7771DB78422399F',
 'exact-phi-eigenrelation-candidate-v1/ARGUMENT-AND-API-MAP.md': '8CBE9BF4DB6C3AF404370D0A3D9F610F455DE23401553E1AC1A3EB33CC2C9BD7',
}


def main():
    rows = []
    for relative, pin in OFFERS.items():
        source = HERE/relative
        data = source.read_bytes()
        assert digest(source) == pin and not data.startswith(b'\xef\xbb\xbf')
        text = data.decode('utf-8')
        assert '\ufffd' not in text and '\u00e2\u2020' not in text and '\u00c3\u00a2' not in text
        rows.append(dict(original=relative, sha256=pin, bytes=len(data), valid_utf8_no_bom=True))
    target = HERE/'operator-initial-offers-capture-v1'
    target.mkdir(exist_ok=False)
    (target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    for number, row in enumerate(rows):
        name = f'{number:02d}-'+Path(row['original']).name
        (target/name).open('xb').write((HERE/row['original']).read_bytes())
        assert digest(target/name) == row['sha256']
        row['copy'] = name
    record = dict(schema='operator-initial-uncompiled-offers-v1', files=rows,
                  root_read_complete_offers=True, immutable_capture_acknowledged=True,
                  lean_executed=False, certified=False, accepted=False, full_goal_complete=False,
                  root_static_findings=[
                    'Operator contracts require explicit implicit s in phiAverage calls and arbitrary-real-F eigenrelation without invariance.',
                    'Phi pairing calc must match operand order of the actual pairing definition and correct sum_mul distribution.',
                    'Phi character zero lemmas and exact frame-product API require source reconciliation.',
                    'For i>d, projection vanishes; do not assert the scalar product always vanishes (s=0 is a counterexample).',
                    'Kernel-frame count and full G/Phi/eigenrelation/adjoint/complex bodies remain open.'
                  ])
    (target/'index.json').open('x', encoding='utf-8').write(json.dumps(record, indent=2)+'\n')
    print(json.dumps(dict(folder=str(target), verified_offers=len(rows), accepted=False)))


if __name__ == '__main__':
    main()
