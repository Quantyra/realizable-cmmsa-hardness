"""Freeze the complete uncompiled eigenrelation chain and root static findings."""
import json
from pathlib import Path
from custody_checks import digest

HERE = Path(__file__).resolve().parent
OFFERS = {
 'ExactPhiEigenrelation-v3.lean':'4EE40B14AD0A6214CE777B450BE5C28E336975C25E8135A5A927D476102E266A',
 'ARGUMENT-AND-API-MAP-v3.md':'03D2C985C9FE31B8B4E8953602A876B2B925BC8B70AB330C91D30245E5E59208',
}


def main():
    rows = []
    for name,pin in OFFERS.items():
        source = HERE/'exact-phi-eigenrelation-candidate-v1'/name
        data = source.read_bytes()
        assert digest(source) == pin and not data.startswith(b'\xef\xbb\xbf')
        text = data.decode('utf-8')
        assert '\ufffd' not in text and '\u00e2\u2020' not in text and '\u00c3\u00a2' not in text
        rows.append(dict(original=source.relative_to(HERE).as_posix(),copy=name,bytes=len(data),sha256=pin))
    target = HERE/'phi-eigenrelation-offer-capture-v3'
    target.mkdir(exist_ok=False)
    (target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n',encoding='utf-8')
    for row in rows:
        (target/row['copy']).open('xb').write((HERE/row['original']).read_bytes())
        assert digest(target/row['copy']) == row['sha256']
    record = dict(files=rows, immutable_capture_acknowledged=True, root_read_complete_offer=True,
                  utf8_no_bom_and_known_glyph_corruption_checks_passed=True,
                  lean_executed=False, certified=False, accepted=False, full_goal_complete=False,
                  mathematical_target_preserves_arbitrary_real_F_and_unrestricted_B=True,
                  root_static_findings=[
                    'Raw BinaryMatrix subtype binders incorrectly use C.1 projections in several predicates.',
                    'Independence transport through kernel subtype runs in the wrong direction and applies congrArg to the wrong carrier.',
                    'Rewrite at f.property must use a named local proof; inspect exact subtype equivalence API.',
                    'Frame-product duality namespace is imported but not opened or qualified.',
                    'Final projection law needs explicit scalar linearity of Phi; sum interchange alone does not factor Fourier coefficients.',
                    'Reassociation in the character numerator and generic sum-normalization proof need explicit completion.'
                  ],
                  route_assessment='The full proposed chain targets the original eigenrelation, including empty and impossible frames. These are source/elaboration gaps, not verified theorem bodies; no helper milestone is accepted.')
    (target/'index.json').open('x',encoding='utf-8').write(json.dumps(record,indent=2)+'\n')
    print(json.dumps(dict(folder=str(target),offers=len(rows),accepted=False)))


if __name__ == '__main__':
    main()
