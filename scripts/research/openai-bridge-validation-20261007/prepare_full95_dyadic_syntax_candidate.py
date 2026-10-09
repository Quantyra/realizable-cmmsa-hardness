"""Repair only the two missing final-let delimiters in the dyadic candidate."""
import hashlib
import json
from pathlib import Path
import tarfile

HERE = Path(__file__).parent
PARENT = Path('C:/Users/dfred/.quantyra/builder02/full94-manuscript-moment-call-repair-resource02')
SOURCE = 'lean/PvNP/RealizableHardness/ActualSelectedComplementManuscriptDyadicMoment.lean'
OLD = b'    let fc := coordinateFunctional I copies U A f\n'
NEW = b'    let fc := coordinateFunctional I copies U A f;\n'


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    archive_path = PARENT / 'input-archive.tar.gz'
    with archive_path.open('rb') as stream:
        pin = hashlib.file_digest(stream, 'sha256').hexdigest().upper()
    assert pin == '5DAE29BF1804799C7021B54A2A16D243B5DDD14BA64D7DA2C378B4A693CE5974'
    with tarfile.open(archive_path, 'r:gz') as archive:
        old = archive.extractfile(SOURCE).read()
        manifest = json.loads(archive.extractfile('capture-manifest.json').read())
    assert sha(old) == manifest['project_sources'][SOURCE]['sha256']
    assert old.count(OLD) == 2 and old.count(NEW) == 0
    new = old.replace(OLD, NEW)
    assert new.replace(NEW, OLD) == old and len(new) == len(old) + 2
    destination = HERE / 'full95-dyadic-syntax-candidate-v1'
    destination.mkdir()
    with (destination / Path(SOURCE).name).open('xb') as stream:
        stream.write(new)
    report = {'schema': 'full95-dyadic-final-let-delimiter-candidate-v1',
              'parent_archive_sha256': pin, 'source': SOURCE,
              'old_sha256': sha(old), 'new_sha256': sha(new), 'bytes': len(new),
              'exact_edit_count': 2, 'edit': 'Explicit semicolon after final let fc value before the result proposition',
              'theorem_names_parameters_premises_results_and_proof_bodies_retained': True,
              'inverse_byte_parity': True, 'native_verification_pending': True,
              'local_compilation': False, 'accepted': False, 'launch_clearance': False}
    with (destination / 'derivation.json').open('x', encoding='utf-8') as stream:
        json.dump(report, stream, indent=2)
        stream.write('\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
