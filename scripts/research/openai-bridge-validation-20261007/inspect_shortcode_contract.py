"""Pin upstream interface and actual local consumer bytes; no compiler or acceptance."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
from urllib.request import urlopen

UPSTREAM = 'adc7f1241b42e322a6451854ab7e4b4c146bf78a'
LOCAL = 'eb60107d3cb3220524c573035c2f3476354bc0ff'
FILES = ('ShortcodeTheorem.lean', 'ShortcodeInterfaceLemmas.lean', 'ShortcodeFromGrassmannLemmas.lean')

def main():
    records = []
    for name in FILES:
        rel = 'lean/OAI/Computability/UniqueGames/Inverse/' + name
        url = 'https://raw.githubusercontent.com/openai/math/' + UPSTREAM + '/' + rel
        with urlopen(url, timeout=30) as response:
            data = response.read()
        source = data.decode('utf-8')
        if name == 'ShortcodeInterfaceLemmas.lean':
            for anchor in ('def InversePrinciple', 'def HasAffineSlice', 'def equalityAcceptance', 'def Slice.affineAgreement'):
                if anchor not in source:
                    raise RuntimeError('Expected interface anchor absent: ' + anchor)
        records.append(dict(path=rel, url=url, bytes=len(data), sha256=hashlib.sha256(data).hexdigest().upper()))
    rel = 'lean/PvNP/RealizableHardness/ActualTaggedComplementInverseInput.lean'
    data = subprocess.run(['git', 'show', LOCAL + ':' + rel], check=True, stdout=subprocess.PIPE).stdout
    if b'theorem exists_actual_complement_weighted_functional' not in data:
        raise RuntimeError('Expected actual consumer absent')
    receipt = dict(observed_utc=datetime.now(timezone.utc).isoformat(), upstream_commit=UPSTREAM,
        upstream_files=records, local_commit=LOCAL,
        local_consumer=dict(path=rel, bytes=len(data), sha256=hashlib.sha256(data).hexdigest().upper()),
        comparison_scope='Definition and actual consuming-statement inspection only',
        no_kernel_execution=True, imported_acceptance=False, sampler_bridge_verified=False,
        affine_to_dual_bridge_verified=False, quantitative_mass_bridge_verified=False,
        runtime_bridge_verified=False, novelty_clearance=False)
    destination = Path(__file__).with_name('shortcode-contract-inspection.json')
    with destination.open('x', encoding='utf-8') as stream:
        json.dump(receipt, stream, indent=2)
    print(json.dumps(receipt, indent=2))

if __name__ == '__main__':
    main()
