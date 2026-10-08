"""Dedicated terminal-custody settlement for additive Full91."""
import sys
sys.dont_write_bytecode = True
from full91_capture_gates import validate_successor
from prepare_builder02_full91 import OUTPUT


def main(action):
    validate_successor()
    if action != 'terminate':
        raise ValueError('Use terminate; independent additive native qualification is separate')
    import terminate_builder02_after_custody as termination
    from full91_builder02_controller import audit_terminal
    termination.ROOT = OUTPUT
    termination.audit_terminal = audit_terminal
    termination.main()


if __name__ == '__main__':
    main(sys.argv[1])
