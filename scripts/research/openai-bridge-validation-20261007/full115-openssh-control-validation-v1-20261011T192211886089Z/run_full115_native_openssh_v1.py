"""Run the unchanged Full114 controller once with an explicitly captured transport."""
import sys
from pathlib import Path
import json
from custody_checks import digest
import full115_builder02_controller as controller
import full115_openssh_control_v1 as transport


def main():
    assert sys.argv[1:] in ([],['--execute'])
    here=Path(__file__).resolve().parent
    validation=json.loads((here/'full115-authorized-execution-control-validation-20261011T190919069567Z/result.json').read_bytes())
    assert digest(here/'full115_builder02_controller.py')==validation['source_snapshots']['full115_builder02_controller.py']
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
