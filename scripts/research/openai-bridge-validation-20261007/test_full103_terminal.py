"""Evidence-boundary tests with synthetic receipts, never compilation evidence."""
import sys
sys.dont_write_bytecode=True
import hashlib
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
from types import SimpleNamespace
import full103_builder02_controller as controller
sys.path.insert(0,'C:/Users/dfred/.quantyra/resume-workspaces/full81/realizable-cmmsa-hardness/docs/a8-gcp/r1007')
import common

class EvidenceBoundary(unittest.TestCase):
    def fixture(self, directory, mutation=None, green=False):
        stage={'index':0,'name':'synthetic-only','argv':['lake','build','SyntheticOnly']}
        manifest={'stages':[stage]}
        out=b'synthetic compiler error\n'; err=b''; code=0 if green else 1
        command={'native_exit':code,'gcp_instance_id':controller.VM_ID,'stage':stage,
                 'argv':['timeout','--signal=TERM','--kill-after=20s','900s',*stage['argv']],
                 'stdout_sha256':hashlib.sha256(out).hexdigest().upper(),
                 'stderr_sha256':hashlib.sha256(err).hexdigest().upper()}
        terminal={'run':'synthetic','host':{'id':controller.VM_ID,'name':controller.VM},'failure':None,
                  'native_exits':{'begin':0,'compile':code,'finish':0}}
        data={'dedicated-worker-terminal.json':json.dumps(terminal).encode(),
              'stage-0.native-exit':str(code).encode(),'stage-0.command.json':json.dumps(command).encode(),
              'stage-0.stdout':out,'stage-0.stderr':err}
        if mutation: mutation(data)
        path=Path(directory)/'synthetic.tar.gz'
        with tarfile.open(path,'w:gz') as archive:
            for name,value in data.items():
                member=tarfile.TarInfo(name); member.size=len(value)
                archive.addfile(member,io.BytesIO(value))
        return path,manifest

    def test_red_native_result_stays_red(self):
        with tempfile.TemporaryDirectory() as tmp:
            path,manifest=self.fixture(tmp)
            self.assertFalse(controller.audit_terminal(path,'synthetic',manifest,common)['compile_green'])

    def test_altered_stdout_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            path,manifest=self.fixture(tmp,lambda data:data.update({'stage-0.stdout':b'changed'}))
            with self.assertRaisesRegex(RuntimeError,'output hash'): controller.audit_terminal(path,'synthetic',manifest,common)

    def test_different_stage_command_rejected(self):
        def change(data):
            receipt=json.loads(data['stage-0.command.json']); receipt['argv']=['lake','build','OtherTarget']
            data['stage-0.command.json']=json.dumps(receipt).encode()
        with tempfile.TemporaryDirectory() as tmp:
            path,manifest=self.fixture(tmp,change)
            with self.assertRaisesRegex(RuntimeError,'scope or invocation'): controller.audit_terminal(path,'synthetic',manifest,common)

    def test_builder01_evidence_rejected(self):
        def change(data):
            terminal=json.loads(data['dedicated-worker-terminal.json']); terminal['host']['id']='8337954477286097405'
            data['dedicated-worker-terminal.json']=json.dumps(terminal).encode()
        with tempfile.TemporaryDirectory() as tmp:
            path,manifest=self.fixture(tmp,change)
            with self.assertRaisesRegex(RuntimeError,'Foreign'): controller.audit_terminal(path,'synthetic',manifest,common)

    def test_green_claim_without_axiom_profiles_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            path,manifest=self.fixture(tmp,green=True)
            with self.assertRaisesRegex(ValueError,'Missing axiom'): controller.audit_terminal(path,'synthetic',manifest,common)

    def check_expanded_profile_failure(self, profiles):
        # Isolate the expansion gate after the historical-profile gate. These
        # synthetic maps are test fixtures, not captured native profiles.
        expanded_common = SimpleNamespace(
            diagnostic_counts=common.diagnostic_counts,
            axiom_profiles=lambda text: profiles,
            require_profiles=lambda values: None,
            STANDARD_AXIOMS=common.STANDARD_AXIOMS)
        with tempfile.TemporaryDirectory() as tmp:
            path, manifest = self.fixture(tmp, green=True)
            manifest['requested_axioms'] = ['old.request', 'new.dyadic.request']
            with self.assertRaisesRegex(RuntimeError, 'Full251 standard-axiom scope'):
                controller.audit_terminal(path, 'synthetic', manifest, expanded_common)

    def test_missing_additive_profile_rejected(self):
        self.check_expanded_profile_failure({'old.request': ['propext']})

    def test_nonstandard_additive_profile_rejected(self):
        self.check_expanded_profile_failure({'old.request': ['propext'],
                                             'new.dyadic.request': ['sorryAx']})

if __name__ == '__main__': unittest.main()
