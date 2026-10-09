"""Reproduction specification for the exact Full96-to-Full97 control binding."""
import ast
from pathlib import Path
NAMES=['full96_verify.py','full96_worker.py','full96_builder02_controller.py','stage_full96_builder02.py','full96_postprocess.py','full96_native_audit.py','test_full96_terminal.py']
def expected(name):
    source=Path(__file__).with_name(name).read_text(encoding='utf-8').replace('full96','full97')
    return source.replace('full97-spectral-orbit-contract-bridge-resource02','full97-spectral-bridge-utf8-section-repair-resource02').replace('full97-spectral-orbit-contract-bridge-builder02-stage','full97-spectral-bridge-utf8-section-repair-builder02-stage')
def main():
    for name in NAMES:
        text=Path(__file__).with_name(name.replace('full96','full97')).read_text(encoding='utf-8')
        assert text==expected(name);ast.parse(text)
    print('Exact seven Full97 controls reproduce parent plus resource/name bindings; no compiler or VM action')
if __name__=='__main__':main()
