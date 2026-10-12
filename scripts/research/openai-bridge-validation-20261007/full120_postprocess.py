"""Dedicated terminal-custody settlement for additive Full91."""
import sys
sys.dont_write_bytecode = True
from full120_capture_gates import validate_successor
from prepare_builder02_full120_v2 import OUTPUT


def main(action):
    validate_successor()
    if action == 'audit':
        import full120_native_audit
        full120_native_audit.main(OUTPUT)
        return
    if action != 'terminate':
        raise ValueError('Use terminate or audit')
    import terminate_full120_builder02_after_custody as termination
    termination.main()


if __name__ == '__main__':
    main(sys.argv[1])
