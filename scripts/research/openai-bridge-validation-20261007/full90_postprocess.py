"""Exact-custody dedicated termination, then frozen172 plus added-material qualification."""
import sys
sys.dont_write_bytecode = True
from full90_capture_gates import validate_successor
from prepare_builder02_full90 import OUTPUT


def main(action):
    validate_successor()
    if action == 'terminate':
        import terminate_builder02_after_custody as termination
        from full90_builder02_controller import audit_terminal
        termination.ROOT = OUTPUT
        termination.audit_terminal = audit_terminal
        termination.main()
    elif action == 'audit':
        import full90_native_audit
        full90_native_audit.main(OUTPUT)
    else:
        raise ValueError('Use terminate or audit')


if __name__ == '__main__':
    main(sys.argv[1])
