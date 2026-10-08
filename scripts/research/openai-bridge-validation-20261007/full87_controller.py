"""Exact cumulative repair chain and full seven-stage Full87 scope."""
import sys
sys.dont_write_bytecode=True
import full86_controller as parent
import full84_controller as validation
import builder02_controller as controller
from prepare_builder02_full86 import REL

ROOT=parent.ROOT.parent/'full87-resource02'
STAGE='/home/dfredriksen_quantyra_org/full87-builder02-stage'

def validate_successor():
    parent.validate_successor()
    validation.validate_capsule_successor(ROOT,parent.ROOT,'C1C155EC99D00DFD16F6713A62929A29C1326AD05D90506DAA3A3E2CD98171B0',REL)

def main(execute=False):
    validate_successor()
    controller.ROOT=ROOT; controller.STAGE=STAGE
    controller.EXTRA_LOCAL_CONTROLS=('full84_controller.py','full85_controller.py','full86_controller.py','full87_controller.py')
    return controller.main(execute)

if __name__=='__main__':
    if sys.argv[1:] not in ([],['--execute']): raise SystemExit('Default preflight or --execute')
    raise SystemExit(main(sys.argv[1:]==['--execute']))
