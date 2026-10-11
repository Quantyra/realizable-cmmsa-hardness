"""Preserve the source-pinned route assessment; no Lean, cloud or deletion."""
import hashlib
import json
from pathlib import Path
import tarfile

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
PLANNING = Path('C:/Users/dfred/Desktop/Projects/IGH/Quantyra-AI-Planning')


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    offer = HERE / 'numeric-source-no-edge-assessment-v1'
    manifest = offer / 'manifest.json'
    assert sha(manifest.read_bytes()) == 'C6EB175A7496C2C1710154987993A4A6020B73667196C7F00B4ED417A733AB0A'
    value = json.loads(manifest.read_bytes())
    row = value['assessment_file']
    assessment = offer / row['path']
    assert assessment.stat().st_size == row['bytes'] and sha(assessment.read_bytes()) == row['sha256']
    inp = value['full114_input_archive']
    archive = Path(inp['path'])
    assert sha(archive.read_bytes()) == inp['sha256']
    with tarfile.open(archive, 'r:gz') as tar:
        for row in value['full114_project_sources']:
            data = tar.extractfile(row['path']).read()
            assert len(data) == row['bytes'] and sha(data) == row['sha256']
    for row in value['candidate_pins']:
        source = HERE / row['path']
        assert sha(source.read_bytes()) == row['sha256']
        assert sha((source.parent / 'index.json').read_bytes()) == row['capture_index_sha256']
    paths = [assessment, manifest]
    for row in value['manuscript_pins']:
        name = row['path']
        if name.startswith('realizable-cmmsa-hardness/'):
            path = REPO / name.removeprefix('realizable-cmmsa-hardness/')
        elif name.startswith('docs/'):
            path = PLANNING / name
        else:
            path = Path(name)
        assert sha(path.read_bytes()) == row['sha256'], str(path)
        paths.append(path)
    target = HERE / 'numeric-source-no-edge-assessment-capture-v1'
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_bytes(b'* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    rows = []
    for number, original in enumerate(paths):
        name = f'{number:02d}-' + original.name
        data = original.read_bytes()
        (target / name).open('xb').write(data)
        assert (target / name).read_bytes() == data
        rows.append(dict(original=str(original), copy=name, bytes=len(data), sha256=sha(data)))
    report = dict(files=rows, actual_project_members_verified=len(value['full114_project_sources']),
        candidate_source_and_capture_pins_verified=True,
        root_read_full_assessment_manifest_and_relevant_manuscript_argument=True,
        root_confirmed_fixed_complement_and_row_respect_interface_gaps=True,
        root_clarifications=[
            'No separate bad-U assumption is introduced if robust local force holds pointwise. Keep eligible-U mass for the eventual global decoder success probability.',
            'The numeric height candidate supplies its recorded scalar bounds; all additional refresh-history and many-Q cutoffs still require explicit proof.',
            'Physical and inverse candidates remain uncompiled. A valid weaker source conclusion is not a native acceptance claim.',
            'The question marks around the manuscript lemma title are an author prose transcription artifact, preserved unchanged.',
            'The source-NO obligation needs the actual reduction and promise; adding an unproved final decoder premise would not finish the goal.'
        ],
        mandatory_independent_CLI_review=False, compiler_invoked=False, cloud_operation=False,
        native_acceptance=False, full_goal_complete=False,
        control_sha256=sha(Path(__file__).read_bytes()))
    data = (json.dumps(report, indent=2) + '\n').encode()
    (target / 'index.json').open('xb').write(data)
    print(json.dumps(dict(folder=target.name, index_sha256=sha(data), originals=len(paths),
                         project_members_verified=report['actual_project_members_verified'])))


if __name__ == '__main__':
    main()
