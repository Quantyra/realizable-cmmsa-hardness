"""Preserve complete unexecuted Full114 trace tooling; retain exact prior algorithm."""
import json
from pathlib import Path
import tarfile
from custody_checks import digest
from prepare_builder02_full114 import OUTPUT, PARENT

HERE=Path(__file__).resolve().parent


def main():
    source=OUTPUT/'consumption-preparation-v1-dag';old=PARENT/source.name
    readiness=json.loads((source/'readiness.json').read_bytes())
    assert readiness['tooling_archive_sha256']==digest(source/'tooling.tar.gz')
    assert readiness['capture_manifest_sha256']==digest(OUTPUT/'capture-manifest.json')
    assert readiness['input_archive_sha256']==digest(OUTPUT/'input-archive.tar.gz')
    assert readiness['project_modules_exact']==369 and readiness['requested_roots_exact']==347 and readiness['focused_consumers_exact']==179
    for name in ('probe.lean','postprocess.py'):
        assert (source/name).read_bytes()==(old/name).read_bytes()
    a=json.loads((old/'preparation-status.json').read_bytes());b=json.loads((source/'preparation-status.json').read_bytes())
    assert a['status'].replace('Full113','Full114')==b['status']
    b['status']=a['status'];assert a==b
    with tarfile.open(source/'tooling.tar.gz') as archive:
        assert len(archive.getmembers())==3
        for name,row in readiness['files'].items():
            assert archive.extractfile(name).read()==(source/name).read_bytes()
            assert digest(source/name)==row['sha256'] and (source/name).stat().st_size==row['bytes']
    out=HERE/'full114-consumption-tooling-record-v1';out.mkdir(exist_ok=False)
    (out/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    rows=[]
    for name in ('tooling.tar.gz','readiness.json','probe.lean','postprocess.py','preparation-status.json'):
        p=source/name;(out/name).open('xb').write(p.read_bytes());assert digest(out/name)==digest(p)
        rows.append(dict(original=str(p),copy=name,bytes=p.stat().st_size,sha256=digest(p)))
    report=dict(files=rows,original_preparation_handle=54482,original_preparation_exit=0,
        probe_and_postprocessor_bytes_exactly_equal_to_prepared_full113=True,
        only_status_label_changed_in_spec=True,modules=369,roots=347,focused=179,
        parent_native_failed_so_parent_probe_unexecuted=True,actual_qualified_full114_native_required_before_execution=True,
        control_sha256=digest(__file__),compiler_invoked=False,accepted=False)
    (out/'index.json').open('x').write(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(folder=out.name,index_sha256=digest(out/'index.json'),archive_sha256=digest(out/'tooling.tar.gz'))),flush=True)


if __name__=='__main__':main()
