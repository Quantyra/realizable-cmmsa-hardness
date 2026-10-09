"""Complete static declaration and exact statement-module custody pointers."""
import json
import re
import tarfile
from pathlib import Path
import audit_spectral_prerequisite_review_coverage as coverage
from prepare_sourcesize_spectral_application import HERE, ROOT, PARENT, sha

EXTRA = ['ActualSelectedComplementSourceSizeAnalyticMoment',
         'ActualSelectedComplementAnalyticMoment', 'ActualFixedFunctionalAppendOperator',
         'ActualFixedFunctionalBinaryMatrixMoment', 'ActualAppendFourierCrossLevelOrthogonality',
         'BinaryMatrixFourier', 'GrassmannCounting']


def main():
    coverage_name = 'spectral-statement-module-review-pointers-v1.json'
    coverage.main(EXTRA, coverage_name)
    pointers = json.loads((HERE / coverage_name).read_bytes())
    assert not pointers['unresolved_three_lens_body_supply']
    source = ROOT / 'ActualSelectedComplementSourceSizeSpectralApplication.lean'
    data = source.read_bytes()
    derivation = json.loads((ROOT / 'derivation.json').read_bytes())
    assert sha(data) == derivation['files'][0]['sha256']
    text = data.decode()
    name = 'sourceSize_spectral47_inhabited'
    start = text.index('theorem ' + name + ' ')
    statement = text[start:text.index(' :=', start)]
    assert '(cutoff : Real → Nat)' in statement
    assert 'ActualSelectedComplementSourceSizeAnalyticMoment.Spectral47ExactContract cutoff' in statement
    checks = (ROOT / 'ActualSelectedComplementSourceSizeSpectralApplicationChecks.lean').read_text(encoding='utf-8')
    targets = re.findall(r'(?m)^#print axioms (\S+)$', checks)
    assert len(targets) == len(set(targets)) == 7
    rel = 'lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46OriginalExactInhabitant.lean'
    capture = json.loads((PARENT / 'capture-manifest.json').read_bytes())
    with tarfile.open(PARENT / 'input-archive.tar.gz') as archive:
        hc = archive.extractfile(rel).read()
    assert sha(hc) == capture['project_sources'][rel]['sha256']
    ht = hc.decode()
    namespace = 'PvNP.RealizableHardness.ActualBinaryMatrixHC46OriginalExactInhabitant'
    assert re.search(r'(?m)^namespace ' + re.escape(namespace) + r'\s*$', ht)
    assert re.search(r'(?m)^(?:theorem|def) original_HC46_exact\b', ht)
    assert namespace + '.original_HC46_exact' in targets
    result = dict(schema='sourcesize-spectral-v2-static-metadata-supplement-v1',
                  candidate_source_sha256=sha(data), original_derivation_sha256=sha((ROOT / 'derivation.json').read_bytes()),
                  additional_public_declaration=dict(name=name, statement=statement,
                      statement_sha256=sha(statement.encode()), native_verified=False),
                  permitted_axiom_output_targets=targets, unique_target_count=7,
                  HC46_full_name=namespace+'.original_HC46_exact', HC46_name_source_verified=True,
                  HC46_source_sha256=sha(hc), statement_module_receipt_pointer_audit_sha256=sha((HERE / coverage_name).read_bytes()),
                  statement_modules=[r for r in pointers['named_and_prefix_selected_bodies'] if Path(r['path']).stem in EXTRA],
                  source_bytes_changed=False, frozen_full101_modified=False,
                  compiler_invoked=False, native_verified=False, overall_GO=False)
    out = HERE / 'sourcesize-spectral-v2-metadata-supplement-v1.json'
    b = (json.dumps(result, indent=2)+'\n').encode()
    if out.exists():
        assert out.read_bytes() == b
    else:
        out.write_bytes(b)
    print(json.dumps(dict(public_declaration=name, statement_modules=len(EXTRA),
                         HC46_name_verified=True, axiom_targets=7, supplement_sha256=sha(b))))


if __name__ == '__main__':
    main()
