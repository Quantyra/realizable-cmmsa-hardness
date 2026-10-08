"""Exact cumulative repair chain and full seven-stage Full88 scope."""
import sys
sys.dont_write_bytecode=True
import full87_controller as parent
import full84_controller as validation
import builder02_controller as controller
from prepare_builder02_full86 import REL

ROOT=parent.ROOT.parent/'full88-resource02'
STAGE='/home/dfredriksen_quantyra_org/full88-builder02-stage'

def validate_successor():
    parent.validate_successor()
    validation.validate_capsule_successor(ROOT,parent.ROOT,'B044690DF471A005A829050F6519B6EF4714FDBE38DA91FD94508C1561D89BCA',REL)

def main(execute=False):
    validate_successor()
    controller.ROOT=ROOT; controller.STAGE=STAGE
    controller.EXTRA_LOCAL_CONTROLS=('full84_controller.py','full85_controller.py','full86_controller.py','full87_controller.py','full88_controller.py')
    return controller.main(execute)

if __name__=='__main__':
    if sys.argv[1:] not in ([],['--execute']): raise SystemExit('Default preflight or --execute')
    raise SystemExit(main(sys.argv[1:]==['--execute']))
