"""Preserve all fresh gates while rechecking an existing exact failed-stage extraction."""
import ast
import sys
from pathlib import Path
from custody_checks import digest

HERE=Path(__file__).parent


def main(write=False):
    source=HERE/'full103_verify.py';text=source.read_text(encoding='utf-8')
    old="    if work.exists(): raise RuntimeError('Prepared workspace already exists; inspect it before continuing')\n    work.mkdir()"
    new="""    if not work.is_dir() or work.is_symlink():
        raise RuntimeError('Exact existing prepared directory required')
    if (stage/'dependency-preflight.json').exists():
        raise RuntimeError('Existing successful preflight; inspect rather than repeat')
    if (home/(resource_tag+'-launch-once.json')).exists():
        raise RuntimeError('Compile already launched; existing extraction verifier forbidden')"""
    assert text.count(old)==1;text=text.replace(old,new)
    old="            target = work/member.name\n            target.parent.mkdir(parents=True,exist_ok=True)\n            with target.open('xb') as stream: stream.write(archive.extractfile(member).read())"
    new="""            target = work/member.name
            if target.is_symlink() or not target.resolve(strict=True).is_relative_to(work.resolve()):
                raise RuntimeError('Existing source target escaped or is a symlink')
            expected = archive.extractfile(member).read()
            if not target.is_file() or target.read_bytes() != expected:
                raise RuntimeError('Existing extraction differs from exact immutable capsule: '+member.name)"""
    assert text.count(old)==1;text=text.replace(old,new)
    ast.parse(text);p=HERE/'full103_verify_existing.py';b=text.encode()
    if write:p.open('xb').write(b)
    else:assert p.read_bytes()==b
    print('Existing extraction byte-equality replaces exclusive creation; all downstream resource/dependency gates unchanged',digest(p))


if __name__=='__main__':
    assert sys.argv[1:] in ([],['--write'])
    main(sys.argv[1:]==['--write'])
