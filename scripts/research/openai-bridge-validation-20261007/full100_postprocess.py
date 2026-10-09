"""Dedicated terminal-custody settlement for additive Full91."""
import sys
sys.dont_write_bytecode = True
from full100_capture_gates import validate_successor
from prepare_builder02_full100 import OUTPUT


def main(action):
    validate_successor()
    if action == 'audit':
        import full100_native_audit
        full100_native_audit.main(OUTPUT)
        return
    if action != 'terminate':
        raise ValueError('Use terminate or audit')
    import terminate_builder02_after_custody as termination
    from full100_builder02_controller import audit_terminal
    termination.ROOT = OUTPUT
    termination.audit_terminal = audit_terminal
    termination.main()


if __name__ == '__main__':
    main(sys.argv[1])
