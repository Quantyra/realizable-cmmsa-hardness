"""Custody-bound termination and unchanged qualification criteria for Full85."""
import sys
sys.dont_write_bytecode=True
import full85_controller

def main(action):
    full85_controller.validate_successor()
    root=full85_controller.ROOT
    if action=='terminate':
        import terminate_builder02_after_custody as termination
        termination.ROOT=root
        termination.main()
    elif action=='audit':
        import builder02_native_audit
        builder02_native_audit.main(root)
    else: raise ValueError('Use terminate or audit')

if __name__=='__main__': main(sys.argv[1])
