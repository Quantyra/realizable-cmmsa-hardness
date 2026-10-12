"""Adapt only owned SSH and archive collection; retain original controller gates."""
import json
from pathlib import Path, PurePosixPath
import re
import shlex
from custody_checks import digest
from full114_dedicated_openssh_v2 import Session
from full119_builder02_controller import VM,ROOT

SESSIONS=[]


def install(runner):
    parent=runner.Control
    class OpenSSHControl(parent):
        def cloud(self,args,**kwargs):
            if args[:3]==['compute','instances','describe']:
                assert args[3]==VM
                return super().cloud(args,**kwargs)
            assert self.authenticated, 'Authenticated dedicated preflight required'
            assert args[:2] in (['compute','ssh'],['compute','scp'])
            if args[1]=='ssh':
                assert len(args)==5 and args[2]==VM and args[3]=='--tunnel-through-iap'
                assert args[4].startswith('--command=')
                command=args[4][len('--command='):];destination=None
            else:
                assert len(args)==5 and args[2].startswith(VM+':') and args[4]=='--tunnel-through-iap'
                remote=args[2].split(':',1)[1]
                assert re.fullmatch(r'/home/dfredriksen_quantyra_org/cmmsa_a8_output_\d{8}T\d{6}Z_[a-f0-9]{8}_evidence\.tar\.gz',remote)
                destination=Path(args[3]).resolve()
                assert destination.parent==Path('C:/a8gcp').resolve() and not destination.exists()
                command='cat '+shlex.quote(remote)
            if not hasattr(self,'owned_session'):
                session=Session(self.run/'openssh-transport');self.owned_session=session
                session.__enter__();SESSIONS.append(session)
                here=Path(__file__).resolve().parent
                controls=['full119_openssh_control_v1.py','full114_dedicated_openssh_v2.py','run_full119_native_openssh_v1.py']
                binding=dict(transport='existing-trusted-host-key-IAP-OpenSSH',
                    original_controller=str(here/'full119_builder02_controller.py'),
                    original_controller_sha256=digest(here/'full119_builder02_controller.py'),
                    worker_and_stage_and_axiom_and_resource_gates_unchanged=True,
                    archive_transport='exact remote bytes over SSH stdout directly to first custody copy',
                    controls={n:digest(here/n) for n in controls})
                for n in controls:(self.run/n).open('xb').write((here/n).read_bytes())
                (self.run/'transport-admission.json').open('x').write(json.dumps(binding,indent=2)+'\n')
            session=self.owned_session
            path=session.ssh(command,allow_failure=kwargs.get('allow_failure',False),output_path=destination)
            record=session.records[-1]
            return record['native_exit'],path.read_bytes() if destination is None else b'',Path(record['stderr_path']).read_bytes()
    runner.Control=OpenSSHControl
    return runner


def close_all():
    while SESSIONS:SESSIONS.pop().close()

