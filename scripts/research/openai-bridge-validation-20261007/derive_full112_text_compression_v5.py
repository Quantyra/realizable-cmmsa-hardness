"""Derive a new exact-HEAD compression pass for files still using NTFS compression."""
import ast
import json
from pathlib import Path
from custody_checks import digest

HERE=Path(__file__).resolve().parent

def main():
    parent=HERE/'compress_full112_committed_text_v4.py'
    text=parent.read_text(encoding='utf-8')
    replacements=[
        ("head.startswith('eca22c39')","head.startswith('81d9d655')"),
        ("target = HERE / 'full112-committed-text-lossless-v4'","target = HERE / 'full112-committed-text-lossless-v5'"),
        ("    candidates = []","    attributes = ctypes.windll.kernel32.GetFileAttributesW\n    attributes.argtypes = [ctypes.c_wchar_p]\n    attributes.restype = ctypes.c_uint32\n    candidates = []"),
        ("('.stdout', '.stderr', '.txt', '.patch', '.lean', '.md', '')","('.json', '.jsonl', '.stdout', '.stderr', '.txt', '.patch', '.lean', '.md', '')"),
        ("        high = ctypes.c_uint32()","        if attributes(str(path)) & 1024:\n            continue\n        high = ctypes.c_uint32()"),
        ("        if size > path.stat().st_size * 0.8:","        if size >= 128000:"),
        ("[:120]","[:400]"),
    ]
    for old,new in replacements:
        assert text.count(old)==1,(old,text.count(old))
        text=text.replace(old,new)
    ast.parse(text)
    target=HERE/'compress_full112_committed_text_v5.py'
    target.open('x',encoding='utf-8',newline='\n').write(text)
    report=dict(parent=parent.name,parent_sha256=digest(parent),target=target.name,target_sha256=digest(target),
        exact_replacements=[dict(old=a,new=b) for a,b in replacements],
        current_committed_unchanged_files_only=True,reparse_already_WOF_files_excluded=True,
        all_logical_bytes_verified_against_HEAD_before_and_after=True,files_deleted=False,cloud_action_performed=False)
    (HERE/'full112-text-compression-derivation-v5.json').open('x').write(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report),flush=True)

if __name__=='__main__':main()

