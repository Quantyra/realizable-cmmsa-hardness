"""Preserve complete source recovery algorithms for qualified Full103 trace."""
import ast
import json
from pathlib import Path
import sys
from custody_checks import digest

HERE = Path(__file__).parent
PARENT = 'prepare_full100_consumption_review_sources.py'


def main(write=False):
    source = HERE/PARENT
    text = source.read_text(encoding='utf-8')
    text = text.replace('full100-matrix-fourier-bullet-repair', 'full103-spectral-owned-warning-repair')
    text = text.replace('full100', 'full103').replace('Full100', 'Full103')
    text = text.replace('327', '340').replace('192', '251')
    text = text.replace('focused-twentyfour', 'focused-eighty-three').replace('focused24', 'focused83')
    old = "len(graphs['graphs']['focused-eighty-three-consumer']['roots']) != 24"
    assert text.count(old) == 1
    text = text.replace(old, "len(graphs['graphs']['focused-eighty-three-consumer']['roots']) != 83")
    ast.parse(text)
    output = HERE/'prepare_full103_consumption_review_sources.py'
    data = text.encode()
    if write:
        output.open('xb').write(data)
    else:
        assert output.read_bytes() == data
    result = dict(schema='full103-complete340-body-source-control-derivation-v1',
        source=PARENT, source_sha256=digest(source), target=output.name,
        target_sha256=digest(output), sources=340, roots=251, focused=83,
        own_trace_custody_and_independent_termination_required=True,
        complete_project_and_external_boundary_source_algorithms_preserved=True,
        scope_narrowed=False, executed=False, accepted=False)
    path = HERE/'full103-review-source-control-derivation.json'
    data = (json.dumps(result, indent=2)+'\n').encode()
    if write:
        path.open('xb').write(data)
    else:
        assert path.read_bytes() == data
    print('Complete340/251/83 source recovery controls verified; not executed')


if __name__ == '__main__':
    assert sys.argv[1:] in ([], ['--write'])
    main(sys.argv[1:] == ['--write'])
