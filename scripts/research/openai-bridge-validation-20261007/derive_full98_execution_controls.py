"""Reproduce additive Full98 controls; no compiler or cloud operation."""
import ast
from pathlib import Path

NAMES = ['full97_verify.py', 'full97_worker.py', 'full97_builder02_controller.py',
         'stage_full97_builder02.py', 'full97_postprocess.py',
         'full97_native_audit.py', 'test_full97_terminal.py']

def expected(name):
    source = Path(__file__).with_name(name).read_text(encoding='utf-8')
    source = source.replace('full97', 'full98')
    source = source.replace('full98-spectral-bridge-utf8-section-repair', 'full98-actual-matrix-fourier-bridge')
    source = source.replace('325', '327').replace('184', '192')
    if name == 'full97_verify.py':
        source = source.replace("['requested_axioms'][-3:]", "['requested_axioms'][-8:]")
    if name == 'full97_native_audit.py':
        source = source.replace("len(additive['added_sources']) != 6", "len(additive['added_sources']) != 8")
        source = source.replace('universal_Spectral47_inhabitant_proven=False)',
            'actual_matrix_right_orbit_and_Fourier_covariance_native_verified=not extra_bad, universal_Spectral47_inhabitant_proven=False)')
    return source

def main(write=False):
    for name in NAMES:
        target = Path(__file__).with_name(name.replace('full97', 'full98'))
        text = expected(name)
        ast.parse(text)
        if write:
            with target.open('xb') as stream:
                stream.write(text.encode('utf-8'))
        else:
            assert target.read_text(encoding='utf-8') == text
    print('Seven Full98 controls reproduce parent with additive scope bindings; no compiler or VM action')

if __name__ == '__main__':
    import sys
    assert sys.argv[1:] in ([], ['--write'])
    main(bool(sys.argv[1:]))
