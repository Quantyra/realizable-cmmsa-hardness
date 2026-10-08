"""Exact Full83 -> Full84 -> Full85 repair chain; unchanged full seven-stage scope."""
import sys
sys.dont_write_bytecode=True
import full84_controller as parent
import builder02_controller as controller

ROOT=parent.ROOT.parent/'full85-resource02'
STAGE='/home/dfredriksen_quantyra_org/full85-builder02-stage'

def validate_successor():
    parent.validate_successor()
    parent.validate_capsule_successor(ROOT,parent.ROOT,'A30B756D0200A4C4D4290568EF03A86E225B224C3AF1ED087BFA664D7A5ADF7A')

def main(execute=False):
    validate_successor()
    controller.ROOT=ROOT; controller.STAGE=STAGE
    controller.EXTRA_LOCAL_CONTROLS=('full84_controller.py','full85_controller.py')
    return controller.main(execute)

if __name__=='__main__':
    if sys.argv[1:] not in ([],['--execute']): raise SystemExit('Default preflight or --execute')
    raise SystemExit(main(sys.argv[1:]==['--execute']))
