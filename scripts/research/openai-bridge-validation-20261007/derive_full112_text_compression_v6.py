"""Preserve the failed exact-byte gate and exclude historical nonexact worktree files."""
import ast,json
from pathlib import Path
from custody_checks import digest
HERE=Path(__file__).resolve().parent

def main():
    parent=HERE/'compress_full112_committed_text_v5.py'
    assert not (HERE/'full112-committed-text-lossless-v5').exists()
    text=parent.read_text(encoding='utf-8')
    changes=[
        ("'full112-committed-text-lossless-v5'","'full112-committed-text-lossless-v6'"),
        ("    rows = []","    rows = []\n    skipped = []"),
        ("        assert original == committed","        if original != committed:\n            skipped.append(dict(path=rel,reason='Git-clean historical file is not byte-identical to its HEAD blob; excluded'))\n            continue"),
        ("json.dumps(dict(head=head, files=rows), indent=2)","json.dumps(dict(head=head, files=rows, skipped_nonexact=skipped), indent=2)"),
        ("    free_before = shutil.disk_usage(HERE).free","    assert rows\n    free_before = shutil.disk_usage(HERE).free"),
        ("    value = dict(head=head, files=rows, free_before=free_before, free_after=free_after,","    value = dict(head=head, files=rows, skipped_nonexact=skipped, free_before=free_before, free_after=free_after,"),
    ]
    for old,new in changes:
        assert text.count(old)==1,(old,text.count(old));text=text.replace(old,new)
    ast.parse(text)
    target=HERE/'compress_full112_committed_text_v6.py';target.open('x',encoding='utf-8',newline='\n').write(text)
    report=dict(original_handle=55808,native_exit=1,failure='Pre-compression exact-HEAD comparison failed; no target or compression was created',
        original_tool_streams_not_claimed_archived=True,parent=parent.name,parent_sha256=digest(parent),
        target=target.name,target_sha256=digest(target),nonexact_historical_files_excluded=True,
        no_original_file_deleted=True,exact_replacements=[dict(old=a,new=b) for a,b in changes])
    (HERE/'full112-text-compression-reconciliation-v6.json').open('x').write(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(target=target.name,sha256=digest(target))),flush=True)
if __name__=='__main__':main()

