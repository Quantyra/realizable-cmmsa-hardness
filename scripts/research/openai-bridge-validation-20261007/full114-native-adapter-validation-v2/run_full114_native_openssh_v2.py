"""Run the unchanged Full114 controller once with an explicitly captured transport."""
import sys
from pathlib import Path
import json
from custody_checks import digest
import full114_builder02_controller as controller
import full114_openssh_control_v1 as transport


def main():
    assert sys.argv[1:] in ([],['--execute'])
    here=Path(__file__).resolve().parent
    validation=json.loads((here/'full114-execution-control-validation-20261011T062522107773Z/result.json').read_bytes())
    assert digest(here/'full114_builder02_controller.py')==validation['source_snapshots']['full114_builder02_controller.py']
    original=controller.context
    def context():
        loaded,runner=original()
        return loaded,transport.install(runner)
    controller.context=context
    try:return controller.main(sys.argv[1:]==['--execute'])
    finally:transport.close_all()


if __name__=='__main__':raise SystemExit(main())
