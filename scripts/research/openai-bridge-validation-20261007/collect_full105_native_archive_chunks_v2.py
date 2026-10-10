"""Resume read-only native custody from six fully verified chunks after preserved SSH closure."""
import base64
from datetime import datetime,timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import sys
from custody_checks import digest,verify_local_custody
from full105_builder02_controller import ROOT,VM,VM_ID,context,local_gates,audit_terminal
from full105_capture_gates import validate_successor

CHUNK=4*1024**2


def save(path,value):
    with path.open('x',encoding='utf-8') as stream:json.dump(value,stream,indent=2)


def main():
    validate_successor();loaded,runner=context();local_gates(loaded['common'],loaded)
    marker=json.loads((ROOT/'launch-once.json').read_bytes());check=Path(marker['preflight']).resolve(strict=True)
    assert check.is_relative_to((ROOT/'checks').resolve())
    commands=json.loads((check/'commands.json').read_bytes())
    assert len(commands)==5 and commands[3]['native_exit']==0
    assert commands[4]['native_exit']==3221225477 and not commands[4]['timed_out']
    assert commands[3]['argv'][1:3]==commands[4]['argv'][1:3]==['compute','ssh']
    assert commands[4]['argv'][3]==VM
    assert not any(row['argv'][1:3]==['compute','scp'] for row in commands)
    assert not (check/'terminal-custody.json').exists()
    run=marker['run'];assert re.fullmatch(r'cmmsa_a8_output_\d{8}T\d{6}Z_[a-f0-9]{8}',run)
    lines=(check/'control/004.stdout').read_text().splitlines()
    pin=lines[0].split()[0].upper();size=int(lines[1])
    assert re.fullmatch('[A-F0-9]{64}',pin) and size>0
    assert lines[0].split()[1]=='/home/dfredriksen_quantyra_org/'+run+'_evidence.tar.gz'
    native=json.loads((check/'control/003.stdout').read_bytes())
    assert native['archive']=='/home/dfredriksen_quantyra_org/'+run+'_evidence.tar.gz'
    assert native['sha256']==pin and native['size']==size
    assert native['terminal']['run']==run and native['terminal']['host']['id']==VM_ID
    assert native['terminal']['native_exits']=={'begin':0,'compile':0,'finish':0}
    assert native['terminal']['failure'] is None and native['terminal']['warm_baseline_preserved']
    assert not (Path('C:/a8gcp')/(run.rsplit('_',1)[1]+'.tar.gz')).exists()
    assert commands[4]['argv'][5]=='--command=sha256sum '+native['archive']+'; stat -c %s '+native['archive']
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
    previous=check/'custody-chunk-recovery/20261010T014652594079Z'
    previous_once=json.loads((previous/'collection-once.json').read_bytes())
    assert previous_once['run']==run and previous_once['expected_archive_sha256']==pin and previous_once['expected_bytes']==size
    assert previous_once['control_sha256']==digest(Path(__file__).with_name('collect_full105_native_archive_chunks.py'))
    previous_commands=json.loads((previous/'commands.json').read_bytes())
    assert len(previous_commands)==8 and all(row['native_exit']==0 for row in previous_commands[:7])
    assert previous_commands[7]['native_exit']==1 and not previous_commands[7]['timed_out']
    assert 'Remote side unexpectedly closed network connection' in (previous/'control/007.stderr').read_text()
    verified_previous=[]
    for index in range(6):
        raw=previous/('control/'+str(index+1).zfill(3)+'.stdout')
        assert digest(raw)==previous_commands[index+1]['stdout_sha256']
        header,payload=raw.read_bytes().split(b'\n',1);row=json.loads(header)
        data=base64.b64decode(payload.strip(),validate=True)
        assert row==json.loads((previous/f'chunk-{index:03}.json').read_bytes())
        assert row['run']==run and row['offset']==index*CHUNK and row['bytes']==CHUNK and row['archive_sha256']==pin
        assert len(data)==CHUNK and hashlib.sha256(data).hexdigest().upper()==row['chunk_sha256']
        part=previous/f'chunk-{index:03}.bin';assert part.read_bytes()==data and digest(part)==row['chunk_sha256']
        verified_previous.append(dict(row,path=str(part)))
    save(folder/'previous-chunks-verified.json',dict(previous=str(previous),commands_sha256=digest(previous/'commands.json'),chunks=verified_previous,original_failed_receipts_preserved=True))
    pieces=[]
    for index,offset in enumerate(range(0,size,CHUNK)):
        count=min(CHUNK,size-offset)
        if index<6:
            row=verified_previous[index];part=folder/f'chunk-{index:03}.bin'
            with Path(row['path']).open('rb') as source,part.open('xb') as target:shutil.copyfileobj(source,target)
            assert digest(part)==row['chunk_sha256']
            save(folder/f'chunk-{index:03}.json',{k:v for k,v in row.items() if k!='path'})
            pieces.append(dict(row,path=str(part)))
            print('Reused verified original archive chunk',index+1,flush=True)
            continue
        remote=f'''import base64,hashlib,json,pathlib,sys
p=pathlib.Path('/home/dfredriksen_quantyra_org/{run}_evidence.tar.gz')
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
    assembled=folder/'complete-native-evidence.tar.gz'
    with assembled.open('xb') as stream:
        for row in pieces:
            with Path(row['path']).open('rb') as source:shutil.copyfileobj(source,stream)
    assert assembled.stat().st_size==size and digest(assembled)==pin
    short=Path('C:/a8gcp')/(run.rsplit('_',1)[1]+'-chunk-custody-'+stamp+'.tar.gz')
    with assembled.open('rb') as source,short.open('xb') as target:shutil.copyfileobj(source,target)
    custody=verify_local_custody(short,assembled,pin,size)
    terminal=audit_terminal(assembled,run,json.loads((ROOT/'capture-manifest.json').read_bytes()),loaded['common'])
    local_gates(loaded['common'],loaded)
    save(folder/'collection-receipt.json',dict(run=run,custody=custody,chunks=pieces,
        original_failed_transport_commands_sha256=digest(check/'commands.json'),
        original_hash_client_crash_preserved=True,original_partial_created=False,compiler_restarted=False,vm_power_operation=False,accepted=False))
    save(check/'terminal-custody.json',dict(run=run,ssh_native_exit=commands[3]['native_exit'],custody=custody,
        terminal=terminal,vm_stop_performed=False,custody_collection_method='individually hashed read-only chunks',
        original_controller_transport_failure_preserved=True,collection_receipt=str(folder/'collection-receipt.json')))
    print(json.dumps(dict(run=run,custody_sha256=pin,bytes=size,native_terminal=terminal['native_terminal'],
        compile_green=terminal['compile_green'],compiler_restarted=False)),flush=True)


if __name__=='__main__':main()
