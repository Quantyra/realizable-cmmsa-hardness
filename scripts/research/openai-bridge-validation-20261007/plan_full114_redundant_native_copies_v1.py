"""Read-only reviewable proposal for four fully preserved redundant archive copies."""
import hashlib,json,subprocess,tarfile
from pathlib import Path
from custody_checks import digest

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[2]

def main():
    def git(*args):return subprocess.check_output(['git',*args],cwd=REPO)
    head=git('rev-parse','HEAD').decode().strip()
    assert head==git('rev-parse','origin/research/openai-bridge-validation-20261007').decode().strip()
    base=Path('C:/a8gcp').resolve(strict=True)
    rows=[]
    for n in (110,111,112,113):
        folder=HERE/f'full{n}-resume-failed-native-v1'
        index=folder/'index.json'
        assert index.read_bytes()==git('cat-file','blob',head+':'+index.relative_to(REPO).as_posix())
        data=json.loads(index.read_bytes())
        row,=[r for r in data['files'] if r['original'].endswith('_evidence.tar.gz')]
        original=Path(row['original']).resolve(strict=True)
        short=(base/(data['run'].rsplit('_',1)[1]+'.tar.gz')).resolve(strict=True)
        assert short.parent==base and short!=original
        assert digest(short)==digest(original)==row['sha256']
        assert short.stat().st_size==original.stat().st_size==row['bytes']
        receipt=json.loads((original.parent/'terminal-custody.json').read_bytes())
        stop=json.loads((original.parent/'vm-termination.json').read_bytes())
        assert receipt['run']==stop['run']==data['run']
        assert receipt['terminal']['native_terminal'] and stop['independent']['status']=='TERMINATED'
        assert str(stop['independent']['id'])=='7237681467779354904'
        if 'payload' in data:
            archive=folder/data['payload']['file'];pin=data['payload']['sha256']
            with tarfile.open(archive,'r:gz') as tar:
                raw=tar.extractfile(row['member']).read()
            assert len(raw)==row['bytes'] and hashlib.sha256(raw).hexdigest().upper()==row['sha256']
            member=row['member']
        else:
            archive=folder/row['copy'];pin=row['sha256'];member=None
        assert digest(archive)==pin
        rel=archive.relative_to(REPO).as_posix()
        git_bytes=git('cat-file','blob',head+':'+rel)
        assert hashlib.sha256(git_bytes).hexdigest().upper()==pin
        rows.append(dict(remove=str(short),bytes=row['bytes'],sha256=row['sha256'],
            retain_original=str(original),retain_committed_archive=str(archive),committed_member=member,
            committed_archive_sha256=pin,git_blob=git('rev-parse',head+':'+rel).decode().strip(),
            native_terminal_and_independent_stop_verified=True))
    assert git('rev-parse','HEAD').decode().strip()==head
    out=HERE/'full114-redundant-native-copy-cleanup-plan-v1';out.mkdir(exist_ok=False)
    (out/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    (out/'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
    plan=dict(head=head,files=rows,total_bytes=sum(r['bytes'] for r in rows),
        action='Remove only four named redundant C:/a8gcp copies after explicit user authorization',
        all_paths_verified_within_explicit_base=True,two_other_exact_local_representations_retained=True,
        committed_and_pushed_custody_verified=True,files_deleted=False,authorization_received=False)
    (out/'plan.json').open('x').write(json.dumps(plan,indent=2)+'\n')
    print(json.dumps(plan,indent=2),flush=True)

if __name__=='__main__':main()
