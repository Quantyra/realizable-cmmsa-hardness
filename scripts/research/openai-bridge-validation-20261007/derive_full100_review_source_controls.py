"""Reproduce whole327/192/24 source collection from qualified Full100 v2."""
import ast
import json
from pathlib import Path
import sys
from custody_checks import digest

HERE = Path(__file__).parent
PARENT = 'prepare_full97_consumption_review_sources.py'
PIN = '12822CA5B6F6592C9D64FEBD24C447549E49333CD4A504C0EBC7E38A0E96295D'

def expected():
    assert digest(HERE/PARENT) == PIN
    text = (HERE/PARENT).read_text(encoding='utf-8')
    text = text.replace('full97-spectral-bridge-utf8-section-repair-resource02', 'full100-matrix-fourier-bullet-repair-resource02')
    text = text.replace('consumption-v1','consumption-v2')
    text = text.replace('full97','full100').replace('Full97','Full100')
    text = text.replace('184','192').replace('325','327')
    text = text.replace('focused-sixteen','focused-twentyfour').replace('focused16','focused24')
    old = "len(graphs['graphs']['focused-twentyfour-consumer']['roots']) != 16"
    assert text.count(old) == 1
    text = text.replace(old, "len(graphs['graphs']['focused-twentyfour-consumer']['roots']) != 24")
    ast.parse(text)
    return text.encode('utf-8')

def main(write=False):
    data = expected(); output = HERE/'prepare_full100_consumption_review_sources.py'
    if write:
        with output.open('xb') as stream: stream.write(data)
    else: assert output.read_bytes() == data
    value = dict(schema='full100-qualified-v2-complete327-body-source-controls',
        parent=PARENT,parent_sha256=PIN,output=output.name,output_sha256=digest(output),
        sources=327,roots=192,focused=24,own_trace_custody_and_independent_termination_required=True,
        complete_project_and_external_boundary_source_algorithms_unchanged=True,
        no_source_selection_narrowing=True,executed=False,accepted=False)
    receipt = HERE/'full100-review-source-control-derivation.json'
    if write:
        with receipt.open('x',encoding='utf-8') as stream: json.dump(value,stream,indent=2);stream.write('\n')
    else: assert json.loads(receipt.read_bytes()) == value
    print('Full100 complete327/192/24 source-control derivation verified; no Lean/cloud operation')

if __name__ == '__main__':
    assert sys.argv[1:] in ([],['--write'])
    main(bool(sys.argv[1:]))
