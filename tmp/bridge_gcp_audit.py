import hashlib
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
NAMES = ['ActualTaggedSelectedDecoderBridge.lean',
         'ActualTaggedSelectedDecoderBridgeChecks.lean']
GCLOUD = shutil.which('gcloud') or 'gcloud'
COMMON = ['--project', PROJECT, '--zone', ZONE, '--quiet']

def call(args):
    return subprocess.run(args, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                          text=True, creationflags=subprocess.CREATE_NO_WINDOW)

for name in NAMES:
    src = ROOT / 'lean/PvNP/RealizableHardness' / name
    h = hashlib.sha256(src.read_bytes()).hexdigest()
    print(f'SOURCE {name} SHA256={h}', flush=True)
    p = call([GCLOUD, 'compute', 'scp', str(src),
        f'{VM}:{RUN}/lean/PvNP/RealizableHardness/{name}', *COMMON])
    if p.returncode:
        print(p.stdout[-2000:]); sys.exit(p.returncode)
for tag in ('build', 'replay'):
    p = call([GCLOUD, 'compute', 'ssh', VM, *COMMON,
        '--command', f'cd {RUN} && export PATH={HOME}/.elan/bin:/usr/local/bin:/usr/bin:/bin && lake build PvNP.RealizableHardness.ActualTaggedSelectedDecoderBridgeChecks'])
    log = ROOT / f'tmp/bridge_gcp_{tag}.log'
    log.write_text(p.stdout, encoding='utf-8')
    print(f'{tag.upper()} EXIT={p.returncode} LOG={log}', flush=True)
    for line in p.stdout.splitlines():
        if line.startswith('error:') or 'axioms' in line or 'Build completed' in line or 'Built PvNP.RealizableHardness.ActualTaggedSelectedDecoderBridgeChecks' in line:
            print(line, flush=True)
    if p.returncode:
        sys.exit(p.returncode)
