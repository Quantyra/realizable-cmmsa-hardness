"""GCP-only continuation of independently verified interrupted scope3, no replay."""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import stat

HOME=Path('/home/dfredriksen_quantyra_org')
CONTROL=HOME/'full109-storage-cache-repoint-v3'
SOURCE_SHA='4D0FD1669D999F7583369CBAC94411F8449CE2C15CA12C39E63306B7A54184AC'
PLAN_SHA='9B2779606C54C2531688B7CC209E32F7C7AAFA75CFB8C88F5ACACF1CD3AEF581'
PARTIAL_SHA='B2B8FEFC2A7CBF7A004B3590AB2821505995314D87DA36F52789E9B2F9169B3C'
COMPLETED=18781
def digest(path):
    with path.open('rb') as stream:return hashlib.file_digest(stream,'sha256').hexdigest().upper()
def validate_rows(plan,old,canonical):
    assert len(plan['rows'])==19233
    for index,row in enumerate(plan['rows']):
        rel=Path(row['relative']);assert not rel.is_absolute() and '..' not in rel.parts
        path=old/rel;dest=canonical/rel;backup=path.with_name(path.name+'.full95-repoint-backup')
        assert dest.resolve(strict=True).is_relative_to(canonical)
        assert dest.stat().st_size==row['bytes'] and digest(dest)==row['sha256']
        assert not backup.exists() and not backup.is_symlink()
        if index<COMPLETED:
            assert path.is_symlink() and path.readlink()==dest
            assert path.resolve(strict=True)==dest.resolve(strict=True)
        else:
            assert not path.is_symlink() and path.resolve(strict=True).is_relative_to(old)
            info=path.stat()
            assert stat.S_ISREG(info.st_mode) and info.st_nlink==1
            assert info.st_size==row['bytes'] and digest(path)==row['sha256']
def write_new(path,value):
    with path.open('x') as stream:json.dump(value,stream,indent=2);stream.write('\n')
def main():
    source=CONTROL/'full109_storage_cache_repoint_v3.py'
    assert digest(source)==SOURCE_SHA
    spec=importlib.util.spec_from_file_location('original_scope3',source)
    original=importlib.util.module_from_spec(spec);spec.loader.exec_module(original)
    old,canonical=original.guards()
    for entry in Path('/proc').iterdir():
        if not entry.name.isdigit() or int(entry.name)==os.getpid():continue
        try:args=(entry/'cmdline').read_bytes().split(b'\0')
        except (FileNotFoundError,PermissionError):continue
        assert not (any(arg.endswith(b'/full109_storage_cache_repoint_v3.py') for arg in args) and b'--execute' in args)
    assert digest(CONTROL/'plan.json')==PLAN_SHA
    assert digest(CONTROL/'partial-execution.json')==PARTIAL_SHA
    assert not (CONTROL/'receipt.json').exists()
    once=json.loads((CONTROL/'execute-once.json').read_bytes())
    assert once==dict(plan_sha256=PLAN_SHA,compiler_invoked=False)
    plan=json.loads((CONTROL/'plan.json').read_bytes())
    partial=json.loads((CONTROL/'partial-execution.json').read_bytes())
    assert plan['old_root']==str(old) and plan['canonical_root']==str(canonical)
    assert partial['applied']==plan['rows'][:18780]
    for key in ('warm_files_written','source_or_project_object_files_changed','failed_evidence_archive_changed','compiler_invoked'):
        assert partial[key] is False
    validate_rows(plan,old,canonical)
    folder=CONTROL/'remaining-only-v1';folder.mkdir(exist_ok=False)
    write_new(folder/'continue-once.json',dict(plan_sha256=PLAN_SHA,partial_sha256=PARTIAL_SHA,
        independently_verified_completed_rows=COMPLETED,remaining_rows=452,original_execute_replayed=False))
    applied=[]
    for row in plan['rows'][COMPLETED:]:
        path=old/row['relative'];dest=canonical/row['relative']
        assert not path.is_symlink() and digest(path)==row['sha256'] and digest(dest)==row['sha256']
        backup=path.with_name(path.name+'.full95-repoint-backup')
        assert not backup.exists() and not backup.is_symlink()
        path.rename(backup)
        try:
            path.symlink_to(dest)
            assert digest(path)==row['sha256'] and digest(dest)==row['sha256']
        except BaseException:
            if path.is_symlink():path.unlink()
            backup.rename(path)
            raise
        backup.unlink();applied.append(row)
        temporary=folder/'progress.next.json'
        temporary.write_text(json.dumps(dict(applied_remaining=applied),indent=2)+'\n')
        temporary.replace(folder/'progress.json')
    assert len(applied)==452 and digest(CONTROL/'partial-execution.json')==PARTIAL_SHA
    assert digest(HOME/(original.RUN+'_evidence.tar.gz'))==original.ARCHIVE_SHA
    for row in plan['rows']:
        path=old/row['relative'];dest=canonical/row['relative']
        assert path.is_symlink() and path.readlink()==dest and digest(path)==row['sha256']
    receipt=dict(partial)
    receipt.update(applied=plan['rows'],disk_after_bytes=shutil.disk_usage(HOME).free,
        content_identity_verified_after_repoint=True,reversible_by_copying_identical_canonical_bytes=True,
        interrupted_original_preserved=True,original_partial_sha256=PARTIAL_SHA,
        original_plan_sha256=PLAN_SHA,independently_verified_preexisting_rows=COMPLETED,
        remaining_rows_applied=len(applied),original_execute_replayed=False)
    assert receipt['disk_after_bytes']>receipt['disk_before_bytes']
    write_new(folder/'receipt.json',receipt)
    print(json.dumps(dict(receipt_sha256=digest(folder/'receipt.json'),receipt=receipt,
        remaining_rows_applied=len(applied),original_execute_replayed=False,compiler_invoked=False)))

if __name__=='__main__':main()
