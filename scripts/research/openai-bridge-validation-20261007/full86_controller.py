"""Exact cumulative repair chain and full original seven-stage execution scope."""
import sys
sys.dont_write_bytecode=True
import full85_controller as parent
import full84_controller as validation
import builder02_controller as controller
from prepare_builder02_full86 import REL

ROOT=parent.ROOT.parent/'full86-resource02'
STAGE='/home/dfredriksen_quantyra_org/full86-builder02-stage'

def validate_successor():
    parent.validate_successor()
    validation.validate_capsule_successor(ROOT,parent.ROOT,'AB27C1189F95EE111089200651C4F5E30AB3004D0E47AB160683A1222F5E4FF9',REL)

def main(execute=False):
    validate_successor()
    controller.ROOT=ROOT; controller.STAGE=STAGE
    controller.EXTRA_LOCAL_CONTROLS=('full84_controller.py','full85_controller.py','full86_controller.py')
    return controller.main(execute)

if __name__=='__main__':
    if sys.argv[1:] not in ([],['--execute']): raise SystemExit('Default preflight or --execute')
    raise SystemExit(main(sys.argv[1:]==['--execute']))
