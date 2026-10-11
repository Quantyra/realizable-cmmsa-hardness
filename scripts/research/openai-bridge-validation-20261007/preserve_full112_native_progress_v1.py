"""Preserve two complete read-only observations without upgrading them to native custody."""
import json,shutil
from pathlib import Path
from custody_checks import digest
from full112_builder02_controller import ROOT
HERE=Path(__file__).resolve().parent
def main():
    records=[('20261011T051621594473Z',40136,[]),('20261011T051810499578Z',20423,[0])]
    paths={Path(__file__).resolve(),HERE/'inspect_full112_native_progress_v1.py'}
    observations=[]
    for stamp,handle,exits in records:
        folder=ROOT/'live-native-inspections-v1'/stamp
        report=json.loads((folder/'inspection.json').read_bytes())
        assert report['run']=='cmmsa_a8_output_20261011T051406Z_3ef6ddc2'
        assert report['read_only'] and not report['authoritative_terminal_custody'] and not report['compiler_replayed']
        assert [r['native_exit'] for r in report['stages']]==exits
        commands=json.loads((folder/'transport/commands.json').read_bytes())
        assert all(r['native_exit']==0 for r in commands)
        for i,row in enumerate(commands):
            for stream in ('stdout','stderr'):assert digest(Path(row[stream+'_path']))==row[stream+'_sha256']
            if 'stdin_sha256' in row:assert digest(folder/'transport'/f'{i:03d}.stdin')==row['stdin_sha256']
        paths.update(p for p in folder.rglob('*') if p.is_file())
        observations.append(dict(handle=handle,native_exit=0,folder=str(folder),stage_exits=exits,inspection_sha256=digest(folder/'inspection.json')))
    target=HERE/'full112-native-progress-record-v1';target.mkdir(exist_ok=False)
    (target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    files=[]
    for i,p in enumerate(sorted(paths)):
        copy=f'{i:03d}-'+p.name
        (target/copy).open('xb').write(p.read_bytes())
        assert digest(target/copy)==digest(p)
        files.append(dict(original=str(p),copy=copy,bytes=p.stat().st_size,sha256=digest(p)))
    value=dict(files=files,observations=observations,complete_internal_transport_streams_preserved=True,
        original_outer_tool_streams_not_claimed_archived=True,observations_only=True,authoritative_terminal_custody=False,compiler_replayed=False,accepted=False)
    (target/'index.json').open('x').write(json.dumps(value,indent=2)+'\n')
    assert shutil.disk_usage(HERE).free>=1536*1024**2
    print(json.dumps(dict(folder=str(target),complete_originals=len(files))),flush=True)
if __name__=='__main__':main()

