"""Source-only inventory; never creates an execution archive or invokes Lean."""
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent


def pin(path):
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def main():
    old = json.loads((HERE / 'complete-numeric-additive-scope-proposal-v7.json').read_bytes())
    selected = {}
    for row in old['exact_candidate_sources']:
        if row['capture'] in ('numeric-fixed-frame-transport-capture-v2', 'numeric-side-extension-formal-capture-v2'):
            continue
        directory = HERE / row['capture']
        matches = [p for p in directory.rglob('*.lean') if pin(p) == row['sha256']]
        assert len(matches) == 1, row
        selected[row['path']] = (matches[0], row['capture'])
    captures = [
        'numeric-fixed-frame-transport-capture-v3', 'numeric-side-extension-formal-capture-v11',
        'numeric-tagged-common-leaf-capture-v2', 'numeric-rational-decoder-capture-v1',
        'numeric-row-deletion-capture-v1', 'numeric-refresh-progress-capture-v1',
        'numeric-star-marginal-capture-v1', 'numeric-refresh-cover-capture-v1',
        'numeric-refresh-formal-capture-v1', 'numeric-refresh-tail-capture-v2',
        'numeric-refresh-history-capture-v1', 'numeric-refresh-history-capture-v2',
        'numeric-refresh-history-capture-v6', 'numeric-distinct-advice-capture-v1',
        'numeric-complement-mass-capture-v1', 'numeric-advice-average-capture-v1',
        'numeric-refresh-preservation-capture-v1', 'numeric-visible-completion-capture-v1',
        'numeric-random-extension-capture-v1', 'numeric-completion-pullback-capture-v1', 'numeric-selected-refresh-cover-capture-v2',
        'numeric-restricted-visible-pair-capture-v1', 'numeric-actual-visible-leaf-loss-capture-v1', 'numeric-two-table-leaf-loss-capture-v1', 'numeric-transverse-agreement-loss-capture-v2', 'numeric-hside-full-zoom-capture-v2',
        'numeric-hside-selected-charge-capture-v1', 'numeric-hside-visible-table-capture-v1',
        'numeric-original-law-amplification-capture-v2', 'numeric-varying-completion-exception-capture-v7',
        'numeric-refresh-checks-supplement-v1', 'numeric-refresh-history-checks-supplement-v6',
    ]
    renames = {'ExactRefresh.lean': 'NumericRefreshFormalOffer.lean',
               'ExactRefreshTail.lean': 'NumericRefreshTailOffer.lean'}
    for capture in captures:
        directory = HERE / capture
        assert (directory / 'index.json').is_file(), capture
        sources = sorted(directory.rglob('*.lean'))
        for source in sources:
            name = renames.get(source.name, source.name)
            if name == 'Checks.lean':
                imports = re.findall(r'^import\s+(PvNP\.RealizableHardness\.\w+)\s*$', source.read_text(), re.M)
                assert imports and len(imports)==len(set(imports)), source
                name = imports[0].rsplit('.', 1)[-1] + ('BundleChecks.lean' if len(imports)>1 else 'Checks.lean')
            path = 'lean/PvNP/RealizableHardness/' + name
            assert path not in selected, (path, capture, selected.get(path))
            selected[path] = (source, capture)
    parent = Path('C:/Users/dfred/.quantyra/builder02/full114-exact-real-complex-operators-repair4-resource02')
    manifest = json.loads((parent / 'capture-manifest.json').read_bytes())
    assert len(manifest['project_sources']) == 369 and len(manifest['requested_axioms']) == 347 and len(manifest['stages']) == 7
    baseline = set(manifest['project_sources'])
    # Manifest source entries can be mappings or records; normalize without changing them.
    if baseline and not isinstance(next(iter(baseline)), str):
        raise AssertionError('Unexpected parent manifest source format')
    known = {p.removeprefix('lean/').removesuffix('.lean').replace('/', '.') for p in baseline}
    known.update(p.removeprefix('lean/').removesuffix('.lean').replace('/', '.') for p in selected)
    rows = []; requests = set(); missing = []
    for path, (source, capture) in sorted(selected.items()):
        text = source.read_text(encoding='utf-8-sig')
        imports = re.findall(r'^import\s+(\S+)\s*$', text, re.M)
        explicit = re.findall(r'^#print axioms\s+(\S+)\s*$', text, re.M)
        namespace = sorted(set(re.findall(r'^namespace\s+(\S+)\s*$', text, re.M)))
        public = re.findall(r'^(?:theorem|lemma)\s+(\w+)', text, re.M)
        inferred = [namespace[0] + '.' + n for n in public] if len(namespace) == 1 else []
        if public and len(namespace) != 1:
            missing.append(dict(kind='namespace_requires_explicit_review', source=path, namespaces=namespace))
        requests.update(explicit); requests.update(inferred)
        for name in imports:
            if name.startswith('PvNP.') and name not in known:
                missing.append(dict(kind='unmapped_project_import', source=path, module=name))
        rows.append(dict(path=path, captured_source=str(source), capture=capture,
                         capture_index_sha256=pin(HERE / capture / 'index.json'),
                         sha256=pin(source), bytes=source.stat().st_size,
                         imports=imports, explicit_axiom_requests=explicit,
                         public_theorem_requests=inferred))
    original_requests = set(manifest['requested_axioms'])
    additional = sorted(requests - original_requests)
    value = dict(schema='full-numeric-source-only-inventory-v7',
                 original_operator_baseline=dict(sources=369, requests=347, stages=7,
                     input_sha256=pin(parent / 'input-archive.tar.gz'), manifest_sha256=pin(parent / 'capture-manifest.json')),
                 selected_sources=rows, selected_source_count=len(rows),
                 total_project_source_count=369 + len(rows),
                 additional_requests=additional, additional_request_count=len(additional),
                 total_request_count=347 + len(additional), unresolved=missing,
                 source_inventory_incomplete=True,
                 remaining_drafts=['final decoder composition', 'kernel verification of all selected uncompiled candidates', 'actual accepted operator successor rebind'],
                 requires_rebind_to_actual_accepted_operator_successor_before_execution=True,
                 execution_archive_created=False, cloud_operation=False, lean_executed=False,
                 native_verified=False, accepted=False)
    target = HERE / 'complete-numeric-source-only-inventory-v7.json'
    target.open('xb').write((json.dumps(value, indent=2) + '\n').encode())
    print(json.dumps(dict(inventory=str(target), sha256=pin(target), sources=value['total_project_source_count'],
                          requests=value['total_request_count'], unresolved=len(missing))), flush=True)


if __name__ == '__main__':
    main()
