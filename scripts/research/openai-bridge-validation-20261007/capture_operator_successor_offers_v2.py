"""Freeze offered uncompiled successor bytes; acceptance remains open."""
import json
from pathlib import Path
from custody_checks import digest

HERE = Path(__file__).resolve().parent
OPERATOR = {
 'RectangularFrameFiberAverage.lean': '5F93279F44E22B3022C724FBD6C739163645494D74235CA3E8C8A29942C66038',
 'RectangularFrameFiberAverageChecks.lean': 'CB02EB2563A9D53438C3A1F58B71699D3E9ECAE70A5563DA661570F79B4E5518',
 'RectangularGLRowCompletion.lean': 'A14616579952CACF84C198F00ACBD787A03B205DEF7D3DE5A66233687330AFBF',
 'RectangularGLRowCompletionChecks.lean': 'D17BF262EB0E9ABA0110C7E6C6CD51EAFFECE4AC03D68E033C3320383E6984FB',
 'ARGUMENT-AND-API-MAP.md': 'C1AB73BB816EA068639D4D5F5E55ACA6FA6CB3A0364EFCE0FC4D653207136874',
 'API-MAP-ROW-COMPLETION-ADDENDUM.md': 'F8984965F6D6DC25157FCB34C168BB315396CD5BB1B2009CAED82DBD10851419',
 'FIBER-EQUIVALENCE-ADDENDUM.md': '1B9DB4D55E448B677D62CBAB1A70BE15F9344090FCB31136FE0193BB24F5AEAC',
 'ROW-MARGINAL-ADDENDUM.md': '6E5DB30126658C9ADCE69DAB38D468E8052CDE8D7BF89D87718301CE6547DA72',
 'COLUMN-MARGINAL-ADDENDUM.md': '593B9697F8D0CDB8EDBD36530C286D59CAFDF4B3686805A8CE9E660E63CC76D3',
}
PHI = {
 'ExactPhiEigenrelation-v2.lean': '985415C71C86EFE42796329FF0FC5737E5B68418502B471995C7F01C7F3BC44E',
 'ARGUMENT-AND-API-MAP-v2.md': '62C625F67FEA2E90EBC1B249D53BC10BB886B2B551AD53C823BBAFBA45EF7994',
}


def main():
    sources = {**{f'exact-operator-continuation-candidate-v2/{k}':v for k,v in OPERATOR.items()},
               **{f'exact-phi-eigenrelation-candidate-v1/{k}':v for k,v in PHI.items()}}
    for relative, pin in sources.items():
        data = (HERE/relative).read_bytes()
        assert digest(HERE/relative) == pin and not data.startswith(b'\xef\xbb\xbf')
        text = data.decode('utf-8')
        assert '\ufffd' not in text and '\u00e2\u2020' not in text and '\u00c3\u00a2' not in text
    target = HERE/'operator-successor-offers-capture-v2'
    target.mkdir(exist_ok=False)
    (target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    rows = []
    for number, (relative, pin) in enumerate(sources.items()):
        name = f'{number:02d}-'+Path(relative).name
        data = (HERE/relative).read_bytes()
        (target/name).open('xb').write(data)
        assert digest(target/name) == digest(HERE/relative) == pin
        rows.append(dict(original=relative, copy=name, bytes=len(data), sha256=pin, valid_utf8_no_bom=True))
    record = dict(schema='operator-successor-uncompiled-offers-v2', files=rows,
                  immutable_capture_acknowledged=True, complete_root_body_review_pending=True,
                  lean_executed=False, certified=False, accepted=False, full_goal_complete=False,
                  root_static_findings=['Row marginal references prefix_fiber_equiv before its declaration; order must be repaired in successor.',
                                        'Phi v2 repairs pairing operand order; kernel/frame equivalence, count and final eigenrelation remain missing.'],
                  route_assessment='Explicit equal-fibre GL marginals and kernel-frame cardinality still target the complete original G/Phi/eigenrelation/adjoint laws without an oracle or changed carrier. Helpers confer no separate milestone acceptance.')
    (target/'index.json').open('x', encoding='utf-8').write(json.dumps(record, indent=2)+'\n')
    print(json.dumps(dict(folder=str(target), verified_offers=len(rows), accepted=False)))


if __name__ == '__main__':
    main()
