"""Capture complete Full112 failure streams and immutable sources for disjoint repairs."""
import hashlib,json,re,tarfile
from pathlib import Path
from custody_checks import digest,verify_local_custody
from full112_builder02_controller import ROOT
HERE=Path(__file__).resolve().parent
def main():
    marker=json.loads((ROOT/'launch-once.json').read_bytes());check=Path(marker['preflight'])
    receipt=json.loads((check/'terminal-custody.json').read_bytes())
    assert marker['run']==receipt['run']=='cmmsa_a8_output_20261011T051406Z_3ef6ddc2'
    assert receipt['terminal']['native_terminal'] and not receipt['terminal']['compile_green']
    assert [r['native_exit'] for r in receipt['terminal']['stages']]==[0,0,0,0,1,125,125]
    custody=receipt['custody'];verify_local_custody(custody['short_path'],custody['repository_path'],custody['remote_sha256'],custody['bytes'])
    assert custody['remote_sha256']=='0392E798A4234ADC4386703FDB1817217D99DFBEA7FF48D4184E614AA42FD6B2'
    assert digest(ROOT/'input-archive.tar.gz')=='1686A96C43231E3E02D88468C6EE5B176D131FF96B2A1F44C3C85C3E5CE531AA'
    target=HERE/'full112-native-diagnostic-packet-v1';target.mkdir(exist_ok=False)
    (target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    files=[]
    def retain(name,data,origin):
        (target/name).open('xb').write(data)
        assert (target/name).read_bytes()==data
        files.append(dict(copy=name,original=origin,bytes=len(data),sha256=hashlib.sha256(data).hexdigest().upper()))
    with tarfile.open(custody['repository_path'],'r:gz') as tar:
        for name in ('stage-4.stdout','stage-4.stderr','dedicated-worker-terminal.json'):
            retain(name,tar.extractfile(name).read(),custody['repository_path']+'!'+name)
    with tarfile.open(ROOT/'input-archive.tar.gz','r:gz') as tar:
        manifest=json.loads(tar.extractfile('capture-manifest.json').read())
        for stem in ('ExactComplexAppendContinuation','RectangularGLRowCompletion'):
            for suffix in ('.lean','Checks.lean'):
                name='lean/PvNP/RealizableHardness/'+stem+suffix;data=tar.extractfile(name).read()
                assert manifest['project_sources'][name]==dict(bytes=len(data),sha256=hashlib.sha256(data).hexdigest().upper())
                retain(stem+suffix,data,str(ROOT/'input-archive.tar.gz')+'!'+name)
    raw=(target/'stage-4.stdout').read_text(encoding='utf-8')
    headers=re.findall(r'(?m)^error: lean/.*\.lean:\d+:\d+:.*$',raw)
    assert len(headers)==9
    assert sum('ExactComplexAppendContinuation.lean:' in line for line in headers)==6
    assert sum('RectangularGLRowCompletion.lean:' in line for line in headers)==3
    assert receipt['terminal']['stages'][4]['diagnostics']['errors']==10
    parts=re.split(r'(?m)(?=^(?:error: |warning: |[✔⚠✖] |Some required targets))',raw)
    for stem in ('ExactComplexAppendContinuation','RectangularGLRowCompletion'):
        selected=''.join(p for p in parts if re.match(r'^(?:error|warning): lean/PvNP/RealizableHardness/'+stem+r'\.lean:',p))
        retain(stem+'-diagnostics.txt',selected.encode('utf-8'),'Complete derived diagnostic blocks from the exact raw stage-4.stdout')
    retain('terminal-custody.json',(check/'terminal-custody.json').read_bytes(),str(check/'terminal-custody.json'))
    retain('control.snapshot.py',Path(__file__).read_bytes(),str(Path(__file__).resolve()))
    value=dict(files=files,run=marker['run'],original_handle=78875,native_exit=1,complete_stage4_streams=True,
        stages=[0,0,0,0,1,125,125],exact_source_error_headers=headers,source_error_count=9,
        original_terminal_broad_error_count=10,unsolved_goals=3,derived_diagnostics_are_not_raw_streams=True,accepted=False)
    (target/'index.json').open('x').write(json.dumps(value,indent=2)+'\n')
    print(json.dumps(dict(folder=str(target),complete_files=len(files),source_errors=9,broad_terminal_error_count=10,
        index_sha256=digest(target/'index.json'))),flush=True)
if __name__=='__main__':main()

