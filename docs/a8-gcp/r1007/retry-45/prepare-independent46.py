"""Prepare full A8 gates before A11, retaining all original combined requests."""
from pathlib import Path
import ast
import shutil

here = Path(__file__).resolve().parent
target = here.parent / 'retry-46'
target.mkdir()
for name in ['controller.py', 'finish-native.py', 'associate-offer.py',
             'check-authorized-preservation.py', 'compare-native.py']:
    value = (here / name).read_text(encoding='utf-8')
    value = value.replace('integrated45_import', 'integrated46_import')
    value = value.replace('finish45_import', 'finish46_import')
    value = value.replace('retry-45', 'retry-46')
    value = value.replace('capture-integrated-45', 'capture-integrated-46')
    (target / name).write_bytes(value.encode('utf-8'))
for name in ['accepted-a9-dependency.json', 'accepted-a9-source.lean.snapshot',
             'axiom-declaration-owner-map.json']:
    shutil.copyfile(here / name, target / name)

path = target / 'controller.py'
value = path.read_text(encoding='utf-8')
needle = "save('inputs/fresh-integrated-axioms.lean', FRESH.encode('utf-8'))\\n"
assert value.count(needle) == 1
value = value.replace(needle, needle + "    save('inputs/fresh-a8-original-axioms.lean', FRESH_A8.encode('utf-8'))\\n")
start = value.index('    p.STAGES=')
end = value.index('    p.FRESH=', start)
value = value[:start] + '''    a8_requests=[n for n in common.REQUESTED_AXIOMS if '.ActualBinaryMatrixHC46A11WeightedAggregate.' not in n]
    assert len(a8_requests)==26 and len(common.REQUESTED_AXIOMS)==49
    p.STAGES=[
        {'index':0,'name':'unchanged-dependency-closure','argv':['lake','build','PvNP.RealizableHardness.ActualBinaryMatrixHC46A7Transfer','PvNP.RealizableHardness.ActualBinaryMatrixHC46A9AmbientFiber','PvNP.RealizableHardness.ActualBinaryMatrixHC46T2Transfer','PvNP.RealizableHardness.ActualBinaryMatrixHC46A8OutputCoordinateTransport','PvNP.RealizableHardness.ActualBinaryMatrixHC46A9AmbientReindex']},
        {'index':1,'name':'full-original-A8-source','argv':['lake','build',*module_names(OWNED[:-2:2])]},
        {'index':2,'name':'full-original-A8-checks','argv':['lake','build',*module_names(OWNED[1:-2:2])]},
        {'index':3,'name':'fresh-full-original-A8-axioms','argv':['lake','env','lean','fresh-a8-original-axioms.lean']},
        {'index':4,'name':'original-weighted-A11-A7-source','argv':['lake','build',*module_names([SOURCE])]},
        {'index':5,'name':'original-weighted-A11-A7-checks','argv':['lake','build',*module_names([CHECKS])]},
        {'index':6,'name':'fresh-all49-integrated-axioms','argv':['lake','env','lean','fresh-integrated-axioms.lean']}]
    p.FRESH_A8='\\n'.join('import '+n for n in module_names(OWNED[1:-2:2]))+'\\n'+'\\n'.join('#print axioms '+n for n in a8_requests)+'\\n'
''' + value[end:]
ast.parse(value)
path.write_bytes(value.encode('utf-8'))

path = target / 'finish-native.py'
value = path.read_text(encoding='utf-8')
needle = "(HERE/'finish-native.snapshot.py').write_bytes(text.encode())"
assert value.count(needle) == 1
value = value.replace(needle,
    "text=text.replace('for i in range(4):\\n    code=', 'for i in range(7):\\n    code=')\n"
    "text=text.replace('axiom_profiles(alltext[3])','axiom_profiles(alltext[6])')\n" + needle)
ast.parse(value)
path.write_bytes(value.encode('utf-8'))

path = target / 'compare-native.py'
value = path.read_text(encoding='utf-8')
value = value.replace("final = (run / 'remote-evidence/stage-1.stdout').read_bytes()",
    "stage_index=int(sys.argv[4]) if len(sys.argv)>4 else 1\n"
    "final = (run / f'remote-evidence/stage-{stage_index}.stdout').read_bytes()")
value = value.replace("'checks_axioms_skipped': True", "'stage_index': stage_index, 'combined_acceptance': False")
ast.parse(value)
path.write_bytes(value.encode('utf-8'))

(target / 'author-report.md').write_bytes(
    b'Original integrated A8 endpoint and weighted A11/A7 full215/14/49 candidate. '
    b'Full A8 source/Checks/fresh26 original A8 axiom gates precede A11 source/Checks, '
    b'followed by all49 original fresh axiom requests. This preserves independent '
    b'complete original A8 evidence while retaining the combined RED boundary. '
    b'No helper3, roadmap or mathematical acceptance inferred. Exact identities, '
    b'owned warnings, custody, all400 cache pins and existing70min stop required. '
    b'No local Lean compilation.\n')
for path in target.glob('*.py'):
    ast.parse(path.read_text(encoding='utf-8'))
print('Prepared retry46 Python AST only; seven stages, original215/14/49 retained')
