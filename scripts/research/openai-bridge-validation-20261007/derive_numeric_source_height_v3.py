"""Add eventual same-floor selector existence using the pinned selector theorem."""
import hashlib
import json
from pathlib import Path
from custody_checks import digest
from lean_source_static_preflight_v2 import inspect_bytes

HERE = Path(__file__).resolve().parent
ADDITION = '''
/-- Every supplied enlarged floor eventually has an actual selected output,
with the same numeric tail guards and an arbitrarily prescribed lower bound
on m. This does not construct a joint source/table/lower-signal witness. -/
theorem selected_numeric_parameters_eventually
    (base : Nat → Nat) (cutoff : Real → Nat) (A M : Nat) (hA : 1 ≤ A) :
    ∃ L0, ∀ L, L0 ≤ L → ∃ m : Nat,
      selector
        (fun j => max (analyticSourceHeightFloor (numericSourceBase base) cutoff j) (j + 2)) L =
          (m : WithBot Nat) ∧
      M ≤ m ∧ numericRankThreshold m ≤ hBlock L m ∧
      20 * m ≤ leafK m (hBlock L m) ∧ 1 ≤ leafK m (hBlock L m) - 1 ∧
      leafT m (hBlock L m) + leafK m (hBlock L m) +
          numericRankThreshold m * (leafK m (hBlock L m) - 1) + 3 ≤
        2 * blocks A (hBlock L m) := by
  obtain ⟨L0, hlarge⟩ := selector_unbounded
    (fun j => max (analyticSourceHeightFloor (numericSourceBase base) cutoff j) (j + 2)) M
  refine ⟨L0, ?_⟩
  intro L hL
  obtain ⟨m, hsel, hM, _⟩ := hlarge L hL
  rcases selected_numeric_height base cutoff hsel with ⟨_, hrank, _, _, _⟩
  exact ⟨m, hsel, hM, hrank, selected_numeric_tail_parameters base cutoff hA hsel⟩

'''


def main():
    prior = HERE / 'numeric-source-height-offer-capture-v2'
    assert digest(prior / 'index.json') == '374929947B78070E4A207892AF5A8D0E16DED611BD8B51D5F3863680FB351344'
    old = json.loads((prior / 'index.json').read_bytes())
    for row in old['files']:
        assert digest(prior / row['path']) == row['sha256']
    manifest = json.loads((prior / 'OFFER-MANIFEST.json').read_bytes())
    assert digest(Path(manifest['dependency_archive']['path'])) == old['dependency_archive_sha256']
    source = HERE / 'actual-numeric-source-height-candidate-v3'
    source.mkdir(exist_ok=False)
    body = (prior / 'ActualNumericSourceHeight.lean').read_text(encoding='utf-8')
    end = 'end PvNP.RealizableHardness.ActualNumericSourceHeight\n'
    assert body.count(end) == 1
    body = body.replace(end, ADDITION + end)
    body = body.replace('Selector existence, the common effective cutoff and the source signal remain\nseparate obligations.',
        'Eventual numeric selector existence is included; the common effective\ncutoff and the joint source signal remain separate obligations.')
    checks = (prior / 'ActualNumericSourceHeightChecks.lean').read_text(encoding='utf-8')
    checks += '#print axioms PvNP.RealizableHardness.ActualNumericSourceHeight.selected_numeric_parameters_eventually\n'
    argument = (prior / 'ARGUMENT-MAP.md').read_text(encoding='utf-8')
    argument = argument.replace('This root-authored, uncompiled candidate', 'This root-authored, uncompiled v3 candidate')
    argument = argument.replace('Still open: existence of a selector output at this enlarged base, a computable common cutoff',
        'Still open: a computable common cutoff')
    argument += '\nThe additional `selected_numeric_parameters_eventually` applies the existing exact `selector_unbounded` to the enlarged floor and any requested lower bound M. Its same returned m and selector equality supply the height and tail guards, for every L beyond a single L0. Thus bare eventual numeric selector inhabitance at the supplied floor has a direct candidate integration; joint source/table/star/sampler inhabitance and the effective common floor remain open. This is not a native verification result.\n'
    contents = {'ActualNumericSourceHeight.lean': body.encode('utf-8'),
                'ActualNumericSourceHeightChecks.lean': checks.encode('utf-8'), 'ARGUMENT-MAP.md': argument.encode('utf-8')}
    rows, lexical = [], []
    for name, data in contents.items():
        rows.append(dict(path=name, bytes=len(data), sha256=hashlib.sha256(data).hexdigest().upper()))
        if name.endswith('.lean'):
            lexical.append(inspect_bytes(data, name))
        (source / name).open('xb').write(data)
    manifest.update(offer=source.name, files=rows, lexical_preflight=lexical,
        parent_capture_index_sha256=digest(prior / 'index.json'),
        same_floor_eventual_selector_candidate=True,
        remaining=['Effective common scalar/source cutoff and its algorithmic bounds',
                   'Joint source/table/star/physical-sampler and lower signal', 'GCP kernel/axiom/trace and review'])
    (source / 'OFFER-MANIFEST.json').open('x', encoding='utf-8').write(json.dumps(manifest, indent=2)+'\n')
    rows = [*rows, dict(path='OFFER-MANIFEST.json', bytes=(source / 'OFFER-MANIFEST.json').stat().st_size,
                      sha256=digest(source / 'OFFER-MANIFEST.json'))]
    target = HERE / 'numeric-source-height-offer-capture-v3'
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    for row in rows:
        data = (source / row['path']).read_bytes()
        (target / row['path']).open('xb').write(data)
        assert digest(target / row['path']) == row['sha256']
    (target / 'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
    index = dict(original_directory=str(source), files=rows, dependencies=old['dependencies'],
        dependency_archive_sha256=old['dependency_archive_sha256'], lexical_preflight=lexical,
        prior_capture_index_sha256=digest(prior / 'index.json'), exact_added_theorem=ADDITION,
        root_read_pinned_selector_body=True, same_floor_eventual_selection_argument_reviewed=True,
        immutable_capture=True, compiler_invoked=False, native_verified=False, accepted=False)
    (target / 'index.json').open('x', encoding='utf-8').write(json.dumps(index, indent=2)+'\n')
    print(json.dumps(dict(folder=str(target), source=rows[0], index_sha256=digest(target / 'index.json'),
        compiler_invoked=False, native_verified=False)), flush=True)


if __name__ == '__main__':
    main()
