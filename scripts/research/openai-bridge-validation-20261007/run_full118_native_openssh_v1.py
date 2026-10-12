"""Run the unchanged Full114 controller once with an explicitly captured transport."""
import sys
from pathlib import Path
import json
from custody_checks import digest
import full118_builder02_controller as controller
import full118_openssh_control_v1 as transport


def main():
    assert sys.argv[1:] in ([],['--execute'])
    here=Path(__file__).resolve().parent
    assert digest(here/'full118-execution-control-validation-20261011T234200761486Z/result.json')=='376BCA4A3DDD973D72278D1DE461801854EFBF0EEECE91CF8204F7C75A5F2BF2'
    validation=json.loads((here/'full118-execution-control-validation-20261011T234200761486Z/result.json').read_bytes())
    assert digest(here/'full118_builder02_controller.py')==validation['source_snapshots']['full118_builder02_controller.py']
    import shutil
    assert shutil.disk_usage(controller.ROOT).free >= 1536*1024**2 + 3*40*1024**2 + 64*1024**2, 'Native two-copy custody, portable archive and Git margin required'
    original=controller.context
    def context():
        loaded,runner=original()
        return loaded,transport.install(runner)
    controller.context=context
    try:return controller.main(sys.argv[1:]==['--execute'])
    finally:transport.close_all()


if __name__=='__main__':raise SystemExit(main())
