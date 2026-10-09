"""Exact Full99 controls rebound to the immutable syntax-only successor."""
import ast
from pathlib import Path
import sys

NAMES = ['full99_verify.py','full99_worker.py','full99_builder02_controller.py',
         'stage_full99_builder02.py','full99_postprocess.py','full99_native_audit.py','test_full99_terminal.py']

def expected(name):
    source=Path(__file__).with_name(name).read_text(encoding='utf-8').replace('full99','full100')
    if name=='full99_builder02_controller.py':
        before="'derive_full100_execution_controls.py')"
        assert source.count(before)==1
        source=source.replace(before,"'derive_full100_execution_controls.py','prepare_full100_bullet_candidates.py')")
    return source

def main(write=False):
    for name in NAMES:
        text = expected(name); ast.parse(text)
        target = Path(__file__).with_name(name.replace('full99','full100'))
        if write:
            with target.open('xb') as stream: stream.write(text.encode())
        else: assert target.read_text(encoding='utf-8') == text
    print('Seven Full100 controls preserve parent algorithms/counts, rebind names and pin the added bullet validator')

if __name__ == '__main__':
    assert sys.argv[1:] in ([], ['--write'])
    main(bool(sys.argv[1:]))
