"""Supply exact native axiom output/root identities to integration; no Lean."""
import hashlib
import json
from pathlib import Path
import re
import tarfile

ROOT = Path('C:/Users/dfred/.quantyra/builder02/full89-resource02')


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    archive_path = Path('C:/a8gcp/e93b94e1.tar.gz')
    if sha(archive_path.read_bytes()) != '0ECFA6657CEB08927A2ED197363DD2539A3319AC8F3945C02BB077AC67424A64':
        raise ValueError('Changed native archive')
    capsule_path = ROOT/'input-archive.tar.gz'
    if sha(capsule_path.read_bytes()) != '7C61F6F96CE4B37433A2C6287E028B4E9D5452A668529F98F31C42FF2CA00AFA':
        raise ValueError('Changed source capsule')
    with tarfile.open(capsule_path) as capsule:
        manifest_data = capsule.extractfile('capture-manifest.json').read()
        if sha(manifest_data) != '81813B3B53BC6112914005E65C4F41CCB96B9D5C0FC45D23D9E3E66B2AE11348':
            raise ValueError('Changed native scope manifest')
        manifest = json.loads(manifest_data)
        for path, pin in manifest['project_sources'].items():
            data = capsule.extractfile(path).read()
            if sha(data) != pin['sha256'] or len(data) != pin['bytes']:
                raise ValueError('Changed source body: '+path)
    with tarfile.open(archive_path) as archive:
        exits = [int(archive.extractfile(f'stage-{i}.native-exit').read()) for i in range(7)]
        if exits != [0]*7:
            raise ValueError('Native scope not GREEN')
        stdout = archive.extractfile('stage-6.stdout').read()
    profiles = {}
    for name, text in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", stdout.decode(), re.S):
        if name in profiles:
            raise ValueError('Duplicate fresh profile')
        axioms = [x.strip() for x in text.split(',') if x.strip()]
        if not set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'}:
            raise ValueError('Unexpected native axiom')
        profiles[name] = axioms
    roots = manifest['requested_axioms']
    trace = json.loads((ROOT/'consumption-v2/qualification/graphs/validated-graphs.json').read_bytes())
    if len(roots) != 172 or len(set(roots)) != 172 or set(profiles) != set(roots) or roots != trace['graphs']['exact172-native']['roots']:
        raise ValueError('Native/capture/trace root scope differs')
    selected = ['GrassmannCounting', 'GrassmannFlagPosterior', 'MatrixGrassmannIncidence', 'MatrixGrassmannMoment', 'MatrixGrassmannFibre']
    source_pins = {path: pin for path, pin in manifest['project_sources'].items()
                   if path.rsplit('/', 1)[-1].removesuffix('.lean') in selected}
    if len(source_pins) != 5:
        raise ValueError('Historical draft-banner sources absent from closure')
    output = ROOT/'consumption-v2/qualification/integration-native-evidence-v1'
    output.mkdir()
    (output/'fresh172-native.stdout').write_bytes(stdout)
    evidence = {'schema': 'full89-integration-native-evidence-v1', 'native_stage_exits': exits,
                'fresh172_native_stdout_sha256': sha(stdout), 'actual_profiles': profiles,
                'requested_root_count': 172, 'native_capture_trace_root_identity_matches': True,
                'all319_actual_capsule_source_hashes_verified': True,
                'historical_draft_banner_source_membership': source_pins,
                'standard_axiom_profiles': True, 'local_compilation': False,
                'inherited_warning_baseline_debt_remains_open': True,
                'independent_integration_complete': False, 'accepted': False}
    (output/'native-review-evidence.json').write_text(json.dumps(evidence, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({'fresh_profiles': len(profiles), 'source_hashes': len(manifest['project_sources']), 'draft_banner_sources_in_scope': len(source_pins)}))


if __name__ == '__main__': main()
