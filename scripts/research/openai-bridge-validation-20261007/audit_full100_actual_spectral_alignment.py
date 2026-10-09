"""Pin actual append/contract statements; no mathematical or launch acceptance."""
import hashlib
import json
from pathlib import Path
import re
import tarfile
from custody_checks import digest

ROOT = Path('C:/Users/dfred/.quantyra/builder02/full100-matrix-fourier-bullet-repair-resource02')
HERE = Path(__file__).parent
SPECS = {
 'ActualFixedFunctionalAppendOperator': ['appendAverage'],
 'ActualAppendFourierCrossLevelOrthogonality': ['appendZeroFrequency','appendAverage_character','appendAverage_rankProjection_sum'],
 'BinaryMatrixFourier': ['uniformMean','fourierCoeff','rankProjection','fourierCoeff_rankProjection','fourier_parseval'],
 'ActualSelectedComplementSourceSizeAnalyticMoment': ['Spectral47ExactContract'],
 'BinaryMatrixRightOrbit': ['same_range_matrix_right_orbit','basis_invariant_eq_of_same_range'],
 'BinaryMatrixRightFourierCovariance': ['fourierCoeff_mul_right_of_basis_invariant','fourierCoeff_eq_of_same_range'],
}

def main():
    assert digest(ROOT/'capture-manifest.json') == '8E71DE454150DEAC5FE9F12B1DCCF8BA768D7788A70D5F159D436C2682D73D3D'
    assert digest(ROOT/'input-archive.tar.gz') == '2B03C230621FB495E35A953C4C56AF4228C4E061D592C04E1D8CCA732CFF9DCF'
    manifest = json.loads((ROOT/'capture-manifest.json').read_bytes())
    rows = []
    with tarfile.open(ROOT/'input-archive.tar.gz') as archive:
        for module, names in SPECS.items():
            rel = 'lean/PvNP/RealizableHardness/'+module+'.lean'
            data = archive.extractfile(rel).read(); pin = hashlib.sha256(data).hexdigest().upper()
            assert pin == manifest['project_sources'][rel]['sha256']
            assert len(data) == manifest['project_sources'][rel]['bytes']
            text = data.decode('utf-8'); declarations = []
            for name in names:
                matches = list(re.finditer(r'^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?(?:def|theorem) '+re.escape(name)+r'\b', text, re.M))
                assert len(matches) == 1, (module,name)
                start = matches[0].start()
                next_decl = re.search(r'^\s*(?:/--|@\[|(?:noncomputable\s+)?(?:def|theorem)\s|end\b)', text[matches[0].end():], re.M)
                end = matches[0].end()+next_decl.start() if next_decl else len(text)
                block = text[start:end].strip()
                statement = block.split(':= by',1)[0].strip() if 'theorem '+name in block else block
                declarations.append(dict(name=name,line=text[:start].count('\n')+1,statement=statement))
            rows.append(dict(path=rel,sha256=pin,bytes=len(data),declarations=declarations))
    report = dict(schema='full100-actual-append-spectral-contract-source-alignment-v1',
        input_archive_sha256=digest(ROOT/'input-archive.tar.gz'),
        manifest_sha256=digest(ROOT/'capture-manifest.json'),source_statements=rows,
        actual_operator='unconditional uniform appended binary matrix average at each fixed base matrix',
        original_contract_scope='all dimensions and all right-basis invariant real functions, with every original height/parity/rho/parameter guard retained',
        existing_exact_ingredient='appendAverage_character kills exactly nonzero tail frequencies; fourier_parseval and rankProjection coefficient filter',
        new_native_ingredient='right-basis covariance and same-image coefficient constancy',
        required_remaining_proofs=['zero-tail embedding rank/image transport',
            'actual append coefficient and rank-level Parseval energy identity',
            'uniform-frame pushforward or fixed-image dual-frame fibre equivalence',
            'universal cardinality ratio and gain bound including all zero/impossible dimensions',
            'full Spectral47 contract inhabitant retaining every original guard'],
        source_identity_verified=True,mathematical_implication_reviewed=False,
        universal_Spectral47_inhabitant_proven=False,compiler_invoked=False,accepted=False)
    data = (json.dumps(report,indent=2,ensure_ascii=False)+'\n').encode('utf-8')
    target = HERE/'full100-actual-spectral-source-alignment-v1.json'
    if target.exists(): assert target.read_bytes() == data
    else:
        with target.open('xb') as stream: stream.write(data)
    print(json.dumps(dict(sources=len(rows),declarations=sum(len(r['declarations']) for r in rows),sha256=digest(target),universal_proof=False)))

if __name__ == '__main__': main()
