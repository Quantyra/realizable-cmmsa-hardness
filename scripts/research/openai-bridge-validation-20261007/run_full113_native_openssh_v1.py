"""Run the unchanged Full113 controller once with an explicitly captured transport."""
import sys
from pathlib import Path
import json
from custody_checks import digest
import full113_builder02_controller as controller
import full113_openssh_control_v1 as transport


def main():
    assert sys.argv[1:] in ([],['--execute'])
    here=Path(__file__).resolve().parent
    validation=json.loads((here/'full113-execution-control-validation-20261011T053328425826Z/result.json').read_bytes())
    assert digest(here/'full113_builder02_controller.py')==validation['source_snapshots']['full113_builder02_controller.py']
    original=controller.context
    def context():
        loaded,runner=original()
        return loaded,transport.install(runner)
    controller.context=context
    try:return controller.main(sys.argv[1:]==['--execute'])
    finally:transport.close_all()


if __name__=='__main__':raise SystemExit(main())
