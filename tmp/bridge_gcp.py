import pathlib
import shutil
import subprocess
import sys

VM = 'quantyra-lean-builder-01'
PROJECT = 'quantyra-lean-cert-20260915'
ZONE = 'us-central1-a'
HOME = '/home/dfredriksen_quantyra_org'
BASE = HOME + '/cmmsa_tagged_force_draft_run'
RUN = HOME + '/cmmsa_tagged_decoder_bridge_run'
SOURCE = pathlib.Path(__file__).resolve().parents[1] / 'lean/PvNP/RealizableHardness/ActualTaggedSelectedDecoderBridge.lean'
GCLOUD = shutil.which('gcloud') or 'gcloud'
COMMON = ['--project', PROJECT, '--zone', ZONE, '--quiet']

def call(args):
    print('RUN', args[1], flush=True)
    proc = subprocess.run(args, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                          text=True, creationflags=subprocess.CREATE_NO_WINDOW)
    print(proc.stdout[-14000:], flush=True)
    if proc.returncode:
        sys.exit(proc.returncode)

call([GCLOUD, 'compute', 'ssh', VM, *COMMON,
      '--command', f'test -d {BASE}/.lake && cp -a --reflink=auto {BASE} {RUN}'])
call([GCLOUD, 'compute', 'scp', str(SOURCE),
      f'{VM}:{RUN}/lean/PvNP/RealizableHardness/ActualTaggedSelectedDecoderBridge.lean', *COMMON])
call([GCLOUD, 'compute', 'ssh', VM, *COMMON,
      '--command', f'cd {RUN} && export PATH={HOME}/.elan/bin:$PATH && lake build PvNP.RealizableHardness.ActualTaggedSelectedDecoderBridge'])
