"""Use unambiguous Git blob reads after the preserved Windows long-path failure."""
import ast
import json
from pathlib import Path
from custody_checks import digest

HERE=Path(__file__).resolve().parent


def main():
    source=HERE/'compress_full112_committed_text_v3.py'
    assert not (HERE/'full112-committed-text-lossless-v3').exists()
    text=source.read_text(encoding='utf-8')
    replacements=[("git('show', head + ':' + rel)","git('cat-file', 'blob', head + ':' + rel)"),
        ('full112-committed-text-lossless-v3','full112-committed-text-lossless-v4')]
    for old,new in replacements:
        assert text.count(old)==1;text=text.replace(old,new)
    ast.parse(text)
    target=HERE/'compress_full112_committed_text_v4.py';target.open('xb').write(text.encode())
    (HERE/'full112-text-compression-derivation-v4.json').open('x').write(json.dumps(dict(
        parent=str(source),parent_sha256=digest(source),target=str(target),sha256=digest(target),
        replacements=replacements,original_tool_handle=44487,original_exit=1,
        original_git_exit=128,original_diagnostic='Filename too long during git show revision-path disambiguation',
        original_failed_before_target_creation_or_compression=True,raw_tool_stream_archive_claimed=False,
        compiler_invoked=False,cloud_action=False),indent=2)+'\n')


if __name__=='__main__':main()
