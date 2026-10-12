"""Run the unchanged Full114 controller once with an explicitly captured transport."""
import sys
from pathlib import Path
import json
from custody_checks import digest
import full119_builder02_controller as controller
import full119_openssh_control_v1 as transport


def main():
    assert sys.argv[1:] in ([],['--execute'])
    here=Path(__file__).resolve().parent
    assert digest(here/'full119-execution-control-validation-20261012T045013217828Z/result.json')=='7AEC67BDC07BF6C85640C8FFC94F9311587FEB2D3ECB9310D77BF92B81DF2F4B'
    validation=json.loads((here/'full119-execution-control-validation-20261012T045013217828Z/result.json').read_bytes())
    assert digest(here/'full119_builder02_controller.py')==validation['source_snapshots']['full119_builder02_controller.py']
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
