"""Bind the two captured proof repairs to the unchanged Full111 batch."""
import ast
import json
from pathlib import Path
import subprocess
from custody_checks import digest

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
PREFIX = HERE.relative_to(REPO).as_posix() + '/'


def main():
    phi = HERE / 'full112-phi-repair-capture-v1'
    gl = HERE / 'full112-rectangular-gl-repair-capture-v2'
    assert digest(phi / 'index.json') == '45571240BC2B88D69BB3127BB4D7178602B7E89C6E56B1C2826A91EFE1B794C8'
    assert digest(phi / 'ExactPhiEigenrelation.lean') == '6E784A3BA94EDF55A4919E78DC82DA2D140EECBD894E5507F17696DC9785D51F'
    assert digest(gl / 'RectangularGLRowCompletion.lean') == '1E117431C3D55B88A2F1BE2E18C9FAA17ABAE94BC504A0490D4DDB0D80720993'
    rows = []

    def derive(name, changes):
        source = HERE / name
        raw = source.read_bytes()
        assert raw == subprocess.check_output(['git', 'cat-file', 'blob', '4930801c:' + PREFIX + name], cwd=REPO)
        text = raw.decode('utf-8')
        replacements = []
        for old, new in changes:
            count = text.count(old)
            if not count:
                assert (old, new) in common, (name, old)
                continue
            text = text.replace(old, new)
            replacements.append(dict(old=old, new=new, occurrences=count))
        ast.parse(text)
        target = HERE / name.replace('full111', 'full112')
        target.open('xb').write(text.encode('utf-8'))
        rows.append(dict(parent=name, parent_commit='4930801c', parent_sha256=digest(source),
                         target=target.name, target_sha256=digest(target), exact_replacements=replacements))

    common = [('full111-exact-real-complex-operators-repair', 'full112-exact-real-complex-operators-repair2'),
              ('full111', 'full112'), ('Full111', 'Full112'), ('full110', 'full111'), ('Full110', 'Full111')]
    derive('prepare_builder02_full111.py', common + [
        ('full112-rectangular-repair-capture-v1', gl.name),
        ('B6FBD029B98BEAA781A705C057C6223764F24F996F24131CC9E174276FF8D136', digest(gl / 'index.json')),
        ('RectangularFrameFiberAverage.lean', 'RectangularGLRowCompletion.lean'),
        ('full112-phi-repair-capture-v2', phi.name),
        ('00C4EC7598E26786D7125344C4D12F79BFD444491D55D058015E0E27D816356A', digest(phi / 'index.json')),
        ('ExactPhiEigenrelation-v4.lean', 'ExactPhiEigenrelation.lean'),
        ('cmmsa_a8_output_20261011T025221Z_7046a7c0', 'cmmsa_a8_output_20261011T035621Z_498f7ba6'),
        ('frame-and-phi-body-repair', 'gl-and-phi-body-repair')])
    derive('full111_capture_gates.py', common)
    result = dict(schema='full112-selected-two-body-package-control-derivation-v1', records=rows,
        selected_capture_indices={gl.name:digest(gl / 'index.json'), phi.name:digest(phi / 'index.json')},
        source_count=369, requests=347, stages=7, archive_members=376,
        other_source_bodies_preserved=367, source_only_bounded_heartbeat_change=True,
        compiler_invoked=False, package_prepared=False)
    (HERE / 'full112-package-control-derivation-v1.json').open('x', encoding='utf-8').write(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(controls=len(rows), selected=list(result['selected_capture_indices']), compiler_invoked=False)))


if __name__ == '__main__':
    main()
