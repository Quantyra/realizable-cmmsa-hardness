import pathlib
import shutil
import subprocess
import sys

VM = 'quantyra-lean-builder-01'
PROJECT = 'quantyra-lean-cert-20260915'
ZONE = 'us-central1-a'
HOME = '/home/dfredriksen_quantyra_org'
RUN = HOME + '/cmmsa_tagged_decoder_bridge_run'
ROOT = pathlib.Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'lean/PvNP/RealizableHardness/ActualTaggedSelectedDecoderBridge.lean'
GCLOUD = shutil.which('gcloud') or 'gcloud'
COMMON = ['--project', PROJECT, '--zone', ZONE, '--quiet']

def call(args):
    proc = subprocess.run(args, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                          text=True, creationflags=subprocess.CREATE_NO_WINDOW)
    return proc

p = call([GCLOUD, 'compute', 'scp', str(SOURCE),
    f'{VM}:{RUN}/lean/PvNP/RealizableHardness/ActualTaggedSelectedDecoderBridge.lean', *COMMON])
if p.returncode:
    print(p.stdout[-2000:]); sys.exit(p.returncode)
print('source uploaded', flush=True)
p = call([GCLOUD, 'compute', 'ssh', VM, *COMMON,
    '--command', f'cd {RUN} && test -L .lake/packages && ln -sfn {HOME}/cmmsa-tagged-build-b5c87492933a/.lake/packages .lake/packages && export PATH={HOME}/.elan/bin:/usr/local/bin:/usr/bin:/bin && lake build PvNP.RealizableHardness.ActualTaggedSelectedDecoderBridge'])
log = ROOT / 'tmp/bridge_gcp_recheck.log'
log.write_text(p.stdout, encoding='utf-8')
lines = p.stdout.splitlines()
for i, line in enumerate(lines):
    if 'error:' in line and 'gcloud.compute.ssh' not in line:
        print('\n'.join(lines[i:i+17]), flush=True)
print(f'EXIT={p.returncode} LOG={log}', flush=True)
sys.exit(p.returncode)
