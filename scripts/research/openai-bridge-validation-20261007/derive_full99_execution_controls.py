"""Exact Full98 controls rebound to the immutable syntax-only successor."""
import ast
from pathlib import Path
import sys

NAMES = ['full98_verify.py','full98_worker.py','full98_builder02_controller.py',
         'stage_full98_builder02.py','full98_postprocess.py','full98_native_audit.py','test_full98_terminal.py']

def expected(name):
    return Path(__file__).with_name(name).read_text(encoding='utf-8').replace('full98','full99').replace(
        'full99-actual-matrix-fourier-bridge','full99-matrix-fourier-bullet-repair')

def main(write=False):
    for name in NAMES:
        text = expected(name); ast.parse(text)
        target = Path(__file__).with_name(name.replace('full98','full99'))
        if write:
            with target.open('xb') as stream: stream.write(text.encode())
        else: assert target.read_text(encoding='utf-8') == text
    print('Seven Full99 controls preserve parent algorithms/counts with resource/name rebinding only')

if __name__ == '__main__':
    assert sys.argv[1:] in ([], ['--write'])
    main(bool(sys.argv[1:]))
