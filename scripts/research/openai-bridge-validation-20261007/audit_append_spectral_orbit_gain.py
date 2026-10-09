"""Exact finite Gram checks for the actual binary append/rank Fourier operators.

This is bounded Python evidence, not a Lean certificate or an upstream import.
"""
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import tarfile

HERE = Path(__file__).parent
INPUT = Path('C:/Users/dfred/.quantyra/builder02/full95-manuscript-moment-syntax-repair-resource02/input-archive.tar.gz')


def column_span(matrix, n, d):
    values = {0}
    for col in range(d):
        vector = sum(((matrix >> (row * d + col)) & 1) << row for row in range(n))
        values |= {value ^ vector for value in tuple(values)}
    return tuple(sorted(values))


def hadamard(values):
    result = list(values)
    width = 1
    while width < len(result):
        for start in range(0, len(result), 2 * width):
            for offset in range(width):
                left, right = result[start + offset], result[start + offset + width]
                result[start + offset], result[start + offset + width] = left + right, left - right
        width *= 2
    return result


def embed_prefix(matrix, n, c, d):
    return sum(((matrix >> (row * c)) & ((1 << c) - 1)) << (row * d) for row in range(n))


def gain(c, d, i):
    if i > c:
        return Fraction(0)
    value = Fraction(1)
    for j in range(i):
        value *= Fraction((1 << c) - (1 << j), (1 << d) - (1 << j))
    return value


def check(n, d):
    size = 1 << (n * d)
    spans = [column_span(matrix, n, d) for matrix in range(size)]
    images = sorted(set(spans))
    ranks = [len(image).bit_length() - 1 for image in spans]
    # Indicator functions of each input column-space class span every real
    # function constant on those classes. Integer transforms retain exactness.
    transforms = [hadamard([int(image == value) for value in spans]) for image in images]
    for transform in transforms:
        orbit_values = {}
        for image, value in zip(spans, transform):
            if image in orbit_values:
                assert orbit_values[image] == value, 'Fourier coefficients are not image-class invariant'
            else:
                orbit_values[image] = value
    rows = []
    for c in range(d + 1):
        embeddings = [embed_prefix(matrix, n, c, d) for matrix in range(1 << (n * c))]
        for i in range(d + 1):
            ratio = gain(c, d, i)
            assert ratio <= Fraction(1, 1 << (i * (d - c)))
            full = [matrix for matrix, rank in enumerate(ranks) if rank == i]
            post = [matrix for matrix in embeddings if ranks[matrix] == i]
            checks = 0
            for a, left in enumerate(transforms):
                for right in transforms[a:]:
                    full_gram = sum(left[matrix] * right[matrix] for matrix in full)
                    post_gram = sum(left[matrix] * right[matrix] for matrix in post)
                    assert post_gram * ratio.denominator == full_gram * ratio.numerator
                    checks += 1
            rows.append({'n': n, 'd': d, 'c': c, 's': d - c, 'rank_level': i,
                         'input_matrices': size, 'image_classes': len(images),
                         'all_basis_and_cross_Gram_entries_checked': checks,
                         'exact_energy_ratio': str(ratio),
                         'ratio_le_two_neg_i_s': True})
    return rows


def main():
    rows = []
    for n in range(4):
        for d in range(5):
            rows.extend(check(n, d))
    pins = {}
    with INPUT.open('rb') as stream:
        archive_pin = hashlib.file_digest(stream, 'sha256').hexdigest().upper()
    assert archive_pin == '4BC7F2B3D0129A449A8CB90163970377D1E08ADC27CB708B48AF17E5896CA441'
    with tarfile.open(INPUT, 'r:gz') as archive:
        manifest = json.loads(archive.extractfile('capture-manifest.json').read())
        for name in ['BinaryMatrixFourier', 'ActualFixedFunctionalAppendOperator',
                     'ActualSelectedComplementSourceSizeAnalyticMoment']:
            rel = 'lean/PvNP/RealizableHardness/' + name + '.lean'
            pin = hashlib.sha256(archive.extractfile(rel).read()).hexdigest().upper()
            assert pin == manifest['project_sources'][rel]['sha256']
            pins[rel] = pin
    destination = HERE / 'append-spectral-orbit-gain-audit-v1'
    destination.mkdir()
    report = {'schema': 'actual-binary-append-spectral-image-class-Gram-audit-v1',
              'input_archive_sha256': archive_pin, 'operator_source_pins': pins,
              'n_range': [0, 3], 'd_range': [0, 4], 'all_c_and_rank_levels': True,
              'cases': rows, 'case_count': len(rows),
              'Gram_entries_checked': sum(row['all_basis_and_cross_Gram_entries_checked'] for row in rows),
              'exact_arithmetic': True,
              'candidate_general_identity': 'post rank-i energy = product_j<i ((2^c-2^j)/(2^(c+s)-2^j)) * full rank-i energy; zero for i>c',
              'general_GL_orbit_transitivity_and_cardinality_Lean_proofs_pending': True,
              'general_Fourier_covariance_and_append_energy_Lean_bridge_pending': True,
              'universal_Spectral47_contract_proven': False,
              'upstream_reuse_certified': False, 'local_Lean_Lake_executed': False,
              'accepted': False, 'full_goal_complete': False}
    with (destination / 'receipt.json').open('x', encoding='utf-8') as stream:
        json.dump(report, stream, indent=2)
        stream.write('\n')
    print(json.dumps({'cases_checked': len(rows), 'Gram_entries_checked': report['Gram_entries_checked'],
                      'receipt': str(destination / 'receipt.json'), 'universal_contract_proven': False}, indent=2))


if __name__ == '__main__':
    main()
