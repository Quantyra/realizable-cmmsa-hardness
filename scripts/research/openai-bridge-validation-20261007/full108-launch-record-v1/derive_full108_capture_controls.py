"""Derive additive cross-level capture controls; no compiler or cloud operation."""
import ast
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).parent


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def expand(text):
    text = text.replace('full106-exact-product-energy', 'full108-exact-crosslevel-product')
    text = text.replace('full106_product_energy', 'full108_crosslevel_product')
    text = text.replace('full106-product-energy', 'full108-crosslevel-product')
    text = text.replace('full106', 'full108').replace('Full106', 'Full108')
    text = text.replace('full105', 'full107').replace('Full105', 'Full107')
    # Replace cardinalities simultaneously; hash literals have no word boundaries.
    text = re.sub(r'\b(?:344|346|257|260|92)\b', lambda m: {'344':'346','346':'348','257':'260','260':'261','92':'93'}[m.group()], text)
    for old,new in [('all344','all346'),('parent344','parent346'),('entire346','entire348'),('full346','full348'),('full260','full261'),('257_profiles','260_profiles'),('and257','and260')]:
        text = text.replace(old,new)
    return text


def main():
    records = []
    for source,target in [('prepare_full106_product_energy_scope.py','prepare_full108_crosslevel_product_scope.py'),
                          ('prepare_builder02_full106.py','prepare_builder02_full108.py'),
                          ('test_full106_scope.py','test_full108_scope.py')]:
        parent = (HERE/source).read_bytes()
        text = expand(parent.decode('utf-8'))
        if source.startswith('prepare_full106_'):
            text = text.replace("CANDIDATES = [('frame-product-duality-candidate-v1','candidate.json')]", "CANDIDATES = [('append-product-crosslevel-candidate-v1','candidate.json')]")
            text = text.replace("        for row in rows:\n            data =", "        for row in rows:\n            if not row['path'].endswith('.lean'): continue\n            row = dict(row, path='lean/PvNP/RealizableHardness/'+row['path'])\n            data =")
            text = text.replace('len(set(requests)) == 3','len(set(requests)) == 1')
            text = text.replace('exact_product_candidate=True','exact_real_crosslevel_candidate=True')
        elif source == 'prepare_builder02_full106.py':
            text = text.replace('CC11E2DA3B8A3FB372D5976BF615C066EE4071FBF7F2D7F9B2D1FA0A3B5CBE92', 'C787891955E5688EAC6820643FD26D61755F955D8AED53DE95893801CAE29765')
            text = text.replace('exact_product_energy_native=False','exact_real_crosslevel_native=False')
        ast.parse(text)
        output = text.encode('utf-8')
        path = HERE/target
        if path.exists():
            assert path.read_bytes() == output
        else:
            path.open('xb').write(output)
        records.append(dict(source=source,source_sha256=sha(parent),target=target,target_sha256=sha(output)))
    receipt = dict(schema='full108-additive348-261-crosslevel-capture-control-derivation-v1',records=records,
                   sources=348,profiles=261,focused=93,stages=7,
                   compiler_invoked=False,cloud_operation=False,accepted=False)
    data = (json.dumps(receipt,indent=2)+'\n').encode('utf-8')
    path = HERE/'full108-capture-control-derivation-v2.json'
    if path.exists(): assert path.read_bytes() == data
    else: path.open('xb').write(data)
    print(json.dumps(receipt))


if __name__ == '__main__':
    main()
