"""Exact cumulative repair chain and full seven-stage Full89 scope."""
import sys
sys.dont_write_bytecode=True
import full88_controller as parent
import full84_controller as validation
import builder02_controller as controller
from prepare_builder02_full89 import REL

ROOT=parent.ROOT.parent/'full89-resource02'
STAGE='/home/dfredriksen_quantyra_org/full89-builder02-stage'

def validate_successor():
    parent.validate_successor()
    validation.validate_capsule_successor(ROOT,parent.ROOT,'6F56EAF273DB3AA0C3BFD1C8525B36C2BF90B6851A270614EDBED1FB4C6F6C95',REL)

def main(execute=False):
    validate_successor()
    controller.ROOT=ROOT; controller.STAGE=STAGE
    controller.EXTRA_LOCAL_CONTROLS=('full84_controller.py','full85_controller.py','full86_controller.py','full87_controller.py','full88_controller.py','full89_controller.py')
    return controller.main(execute)

if __name__=='__main__':
    if sys.argv[1:] not in ([],['--execute']): raise SystemExit('Default preflight or --execute')
    raise SystemExit(main(sys.argv[1:]==['--execute']))
