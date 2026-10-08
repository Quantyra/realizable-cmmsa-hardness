"""Freeze original selected upstream sources/configs; no local Lean or readiness claim."""
import hashlib
import io
import json
from pathlib import Path
import subprocess
import tarfile

REPO = Path('C:/Users/dfred/.quantyra/upstream/openai-math-adc7f124-20261008')
DEST = Path('C:/Users/dfred/.quantyra/upstream/selected-capture-adc7f124-v1')


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    inventory_path = Path(__file__).with_name('upstream-selected-static-import-inventory.json')
    inventory_data = inventory_path.read_bytes()
    inventory = json.loads(inventory_data)
    pin = inventory['commit']
    def git(*args):
        return subprocess.check_output(['git', '-C', str(REPO), *args])
    if git('rev-parse', 'HEAD').decode().strip() != pin or git('status', '--porcelain'):
        raise ValueError('Upstream checkout changed')
    files = {}
    for row in list(inventory['sources'].values()) + [dict(path=p, **r) for p, r in inventory['configs_and_patches'].items()]:
        data = (REPO/row['path']).read_bytes()
        if sha(data) != row['sha256'] or len(data) != row['bytes']:
            raise ValueError('Source/config identity changed: '+row['path'])
        if row['path'] in files:
            raise ValueError('Repeated capture member')
        files[row['path']] = data
    for path in ['LICENSE', 'README.md', 'lean/README.md']:
        data = git('show', pin+':'+path)
        if (REPO/path).read_bytes() != data:
            raise ValueError('License/build README changed')
        files[path] = data
    targets = ['OAI.UniqueGamesTheorem.Inverse.ShortcodeTheorem.inversePrinciple',
               'OAI.UniqueGamesTheorem.Inverse.KMSLowLevel.uniformNoise_energy',
               'OAI.UniqueGamesTheorem.Inverse.KMSLowLevel.rankComponent_bound',
               'OAI.UniqueGamesTheorem.Inverse.KMSLowLevel.uniformNoise_bound_of_fourthMoments',
               'OAI.UniqueGamesTheorem.Inverse.KMSFourthMoment.sliceEnergy_translate',
               'OAI.UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy.coeff_partialRestrict',
               'OAI.UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy.hybrid_fiber_coefficient_factorization']
    driver = '\n'.join('import '+root for root in inventory['roots'])+'\n\n'
    driver += '\n'.join('#check '+name+'\n#print axioms '+name for name in targets)+'\n'
    files['selected-upstream-axioms.lean'] = driver.encode()
    manifest = {'schema': 'original-upstream-selected-capture-v1', 'commit': pin,
                'inventory_sha256': sha(inventory_data), 'roots': inventory['roots'],
                'requested_axiom_profiles': targets,
                'original_toolchain': files['lean/lean-toolchain'].decode().strip(),
                'source_count': inventory['source_count'], 'external_imports': inventory['external_imports'],
                'files': {p: {'sha256': sha(d), 'bytes': len(d)} for p, d in files.items()},
                'compiler_verified': False, 'package_resolution_verified': False,
                'compatibility_patch_application_verified': False, 'gcp_preflight_passed': False,
                'compiled': False, 'accepted': False,
                'scope': 'Original adc7 selected theorem closure inputs and unexecuted axiom driver only. No CMMSA objects/compiler are treated as upstream evidence. Consumer conversions remain unproved.'}
    manifest_data = (json.dumps(manifest, indent=2)+'\n').encode()
    files['selected-capture-manifest.json'] = manifest_data
    DEST.mkdir()
    archive_path = DEST/'input-archive.tar.gz'
    with tarfile.open(archive_path, 'w:gz') as archive:
        for name, data in sorted(files.items()):
            member = tarfile.TarInfo(name); member.size = len(data); member.mode = 0o644
            archive.addfile(member, io.BytesIO(data))
    with tarfile.open(archive_path) as archive:
        if len(archive.getnames()) != len(files):
            raise ValueError('Archive entry mismatch')
        for member in archive.getmembers():
            if archive.extractfile(member).read() != files[member.name]:
                raise ValueError('Archive roundtrip mismatch')
    (DEST/'manifest.json').write_bytes(manifest_data)
    receipt = {'schema': 'original-upstream-selected-capture-receipt-v1',
               'commit': pin, 'archive_path': str(archive_path), 'archive_sha256': sha(archive_path.read_bytes()),
               'archive_bytes': archive_path.stat().st_size, 'entries': len(files),
               'manifest_sha256': sha(manifest_data), 'source_count': inventory['source_count'],
               'requested_profiles': len(targets), 'all_entries_roundtrip_verified': True,
               'compiler_executed': False, 'launch_ready': False, 'accepted': False}
    with Path(__file__).with_name('upstream-selected-capture-receipt.json').open('x', encoding='utf-8') as stream:
        json.dump(receipt, stream, indent=2); stream.write('\n')
    print(json.dumps(receipt))


if __name__ == '__main__': main()
