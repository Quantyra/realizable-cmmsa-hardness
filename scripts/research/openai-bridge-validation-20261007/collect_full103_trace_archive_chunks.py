"""Recover the completed trace archive after diagnosed SCP stall; never compile."""
import base64
from datetime import datetime,timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import sys
from custody_checks import digest,verify_local_custody
from full103_builder02_controller import VM,VM_ID,context,local_gates
from full103_consumption_v2_controller import ROOT,REMOTE,ready
import tarfile
from full103_capture_gates import validate_successor

CHUNK=4*1024**2


def save(path,value):
    with path.open('x',encoding='utf-8') as stream:json.dump(value,stream,indent=2)


def main():
    loaded,runner,binding=ready();local_gates(loaded['common'],loaded)
    marker=json.loads((ROOT/'launch-once.json').read_bytes());check=Path(marker['preflight']).resolve(strict=True)
    assert check.is_relative_to((ROOT/'checks').resolve())
    commands=json.loads((check/'commands.json').read_bytes())
    assert len(commands)==6 and commands[3]['native_exit']==commands[4]['native_exit']==0
    assert commands[5]['native_exit']!=0 and commands[5]['argv'][1:3]==['compute','scp']
    assert not (check/'terminal-custody.json').exists()
    run=marker['run'];assert re.fullmatch(r'cmmsa_a8_output_\d{8}T\d{6}Z_[a-f0-9]{8}',run)
    lines=(check/'control/004.stdout').read_text().splitlines()
    pin=lines[0].split()[0].upper();size=int(lines[1])
    assert re.fullmatch('[A-F0-9]{64}',pin) and size>0
    assert lines[0].split()[1]==REMOTE
    intervention=check/'transfer-stall-intervention-v1/partial-preservation-after-client-stop.json'
    evidence=json.loads(intervention.read_bytes())
    assert evidence['run']==run and evidence['preserved_after_owned_client_stop']
    assert digest(evidence['partial_path'])==evidence['partial_sha256']
    assert evidence['partial_bytes']<size and not evidence['compiler_restarted'] and not evidence['vm_modified']
    stamp=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    folder=check/'custody-chunk-recovery'/stamp;folder.mkdir(parents=True)
    save(folder/'collection-once.json',dict(run=run,expected_archive_sha256=pin,expected_bytes=size,
        control_sha256=digest(__file__),original_transport_failure_preserved=True,compiler_restarted=False))
    runner.VM=VM;control=runner.Control(folder)
    _,out,_=control.cloud(['compute','instances','describe',VM,'--format=json(name,id,status,zone,networkInterfaces)'])
    state=json.loads(out)
    assert state['name']==VM and str(state['id'])==VM_ID and state['status']=='RUNNING'
    assert state['zone'].rsplit('/',1)[-1]=='us-central1-a'
    assert not any(n.get('accessConfigs') for n in state['networkInterfaces'])
    control.authenticated=True
    pieces=[]
    for index,offset in enumerate(range(0,size,CHUNK)):
        count=min(CHUNK,size-offset)
        remote=f'''import base64,hashlib,json,pathlib,sys
p=pathlib.Path('{REMOTE}')
assert sys.platform=='linux' and not p.is_symlink()
before=p.stat()
with p.open('rb') as f:
    archive_pin=hashlib.file_digest(f,'sha256').hexdigest().upper()
    assert archive_pin=={pin!r} and before.st_size=={size}
    f.seek({offset});data=f.read({count})
after=p.stat()
assert (before.st_ino,before.st_size,before.st_mtime_ns)==(after.st_ino,after.st_size,after.st_mtime_ns)
assert len(data)=={count}
row=dict(run={run!r},offset={offset},bytes={count},archive_sha256=archive_pin,chunk_sha256=hashlib.sha256(data).hexdigest().upper())
sys.stdout.buffer.write((json.dumps(row)+'\\n').encode()+base64.b64encode(data)+b'\\n')
'''
        encoded=base64.b64encode(remote.encode()).decode()
        command='python3 -B -c '+chr(34)+'import base64;exec(base64.b64decode('+repr(encoded)+'))'+chr(34)
        _,raw,_=control.cloud(['compute','ssh',VM,'--tunnel-through-iap','--command='+command],timeout=300)
        header,payload=raw.split(b'\n',1);row=json.loads(header)
        data=base64.b64decode(payload.strip(),validate=True)
        assert row['run']==run and row['offset']==offset and row['bytes']==count and row['archive_sha256']==pin
        assert len(data)==count and hashlib.sha256(data).hexdigest().upper()==row['chunk_sha256']
        part=folder/f'chunk-{index:03}.bin'
        with part.open('xb') as stream:stream.write(data)
        save(folder/f'chunk-{index:03}.json',row)
        pieces.append(dict(row,path=str(part)));print('Verified immutable archive chunk',index+1,'bytes',count,flush=True)
    assembled=folder/'complete-trace-evidence.tar.gz'
    with assembled.open('xb') as stream:
        for row in pieces:
            with Path(row['path']).open('rb') as source:shutil.copyfileobj(source,stream)
    assert assembled.stat().st_size==size and digest(assembled)==pin
    short=Path('C:/a8gcp')/(run.rsplit('_',1)[1]+'-trace-chunk-custody-'+stamp+'.tar.gz')
    with assembled.open('rb') as source,short.open('xb') as target:shutil.copyfileobj(source,target)
    custody=verify_local_custody(short,assembled,pin,size)
    with tarfile.open(assembled) as archive:
        members=archive.getmembers()
        assert len({m.name for m in members})==len(members)
        assert all(m.isfile() and not m.name.startswith('/') and all(p not in ('','.','..') for p in m.name.split('/')) for m in members)
        terminal=json.loads(archive.extractfile('terminal.json').read())
        assert terminal['run']==run and terminal['identity']['id']==VM_ID and terminal['identity']['name']==VM
        assert int(archive.extractfile('probe.native-exit').read())==terminal['probe_native_exit']==0
        assert terminal['failure'] is None
        assert terminal['native_archive_sha256']==binding['native_archive_sha256']
        assert terminal['probe_sha256']==binding['tooling_readiness']['files']['probe.lean']['sha256']
        assert (terminal['project_sources_preserved'],terminal['compiled_objects_preserved'],terminal['project_object_closure'])==(340,687,340)
        for name,row in binding['tooling_readiness']['files'].items():
            data=archive.extractfile('tooling/'+name).read()
            assert len(data)==row['bytes'] and hashlib.sha256(data).hexdigest().upper()==row['sha256']
    local_gates(loaded['common'],loaded)
    save(folder/'collection-receipt.json',dict(run=run,custody=custody,chunks=pieces,
        original_failed_transport_commands_sha256=digest(check/'commands.json'),
        original_partial_sha256=evidence['partial_sha256'],compiler_restarted=False,vm_power_operation=False,accepted=False))
    save(check/'terminal-custody.json',dict(run=run,ssh_native_exit=commands[3]['native_exit'],custody=custody,
        probe_terminal=terminal,native_terminal=True,vm_stop_performed=False,custody_collection_method='individually hashed read-only chunks',
        original_controller_transport_failure_preserved=True,collection_receipt=str(folder/'collection-receipt.json')))
    print(json.dumps(dict(run=run,custody_sha256=pin,bytes=size,native_terminal=True,
        probe_native_exit=terminal['probe_native_exit'],compiler_restarted=False)),flush=True)


if __name__=='__main__':main()
