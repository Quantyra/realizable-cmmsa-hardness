"""Custody-bound dedicated termination and qualified audit for Full89."""
import sys
sys.dont_write_bytecode=True
import full89_controller

def main(action):
    full89_controller.validate_successor()
    root=full89_controller.ROOT
    if action=='terminate':
        import terminate_builder02_after_custody as termination
        termination.ROOT=root; termination.main()
    elif action=='audit':
        import builder02_native_audit
        builder02_native_audit.main(root)
    else: raise ValueError('Use terminate or audit')

if __name__=='__main__': main(sys.argv[1])
