"""Check exact offered UTF8 source and parent pins; never invoke Lean."""
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).parent
ROOT = Path('C:/Users/dfred/.quantyra/builder02/full107-exact-product-energy-repair-resource02')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def main():
    manifest = json.loads((ROOT/'capture-manifest.json').read_bytes())
    rows = []
    for name in ('ActualAppendProductCrossLevelIdentity.lean', 'ActualAppendProductCrossLevelIdentityChecks.lean', 'argument.md'):
        path = HERE/name
        data = path.read_bytes(); text = data.decode('utf-8')
        assert not data.startswith(b'\xef\xbb\xbf')
        if path.suffix == '.lean':
            assert not re.search(r'\b(sorry|admit|axiom)\b', text)
            assert 'set_option linter' not in text
        rows.append(dict(path=name, bytes=len(data), sha256=sha(path)))
    dependencies = []
    for name in ('ActualFiniteFrameProductDuality', 'ActualAppendFourierCrossLevelOrthogonality'):
        rel = 'lean/PvNP/RealizableHardness/'+name+'.lean'
        path = ROOT/'consumption-v3/qualification/review-sources'/rel
        pin = manifest['project_sources'][rel]
        assert path.stat().st_size == pin['bytes'] and sha(path) == pin['sha256']
        dependencies.append(dict(path=rel, **pin))
    settlement = HERE.parent/'full107-material-integration-reports-v4/root-reconciliation-v1.json'
    assert sha(settlement) == '0BF97A645869BB8974A726693FD6521B057686EF0DAB78BA0E665762D89D29E4'
    result = dict(schema='append-product-crosslevel-uncompiled-candidate-v1', files=rows,
                  exact_full107_dependency_pins=dependencies,
                  parent_capture_manifest_sha256=sha(ROOT/'capture-manifest.json'),
                  parent_reconciliation_sha256=sha(settlement), sources_after_addition=348,
                  profiles_after_addition=261, stages=7, mathematical_argument_recorded=True,
                  UTF8_without_BOM_verified=True, compiled=False, reviewed=False, accepted=False,
                  G_Phi_or_adjoint_claimed=False)
    data = (json.dumps(result, indent=2)+'\n').encode('utf-8')
    output = HERE/'candidate.json'
    if output.exists():
        assert output.read_bytes() == data
    else:
        output.open('xb').write(data)
    print(json.dumps(dict(files=rows, parent_dependencies=2, compiled=False, accepted=False)))


if __name__ == '__main__':
    main()
