"""Capture complete Full114 failure streams and immutable sources for disjoint repairs."""
import hashlib,json,re,tarfile
from pathlib import Path
from custody_checks import digest,verify_local_custody
from full114_builder02_controller import ROOT
HERE=Path(__file__).resolve().parent
def main():
    marker=json.loads((ROOT/'launch-once.json').read_bytes());check=Path(marker['preflight'])
    receipt=json.loads((check/'terminal-custody.json').read_bytes())
    assert marker['run']==receipt['run']=='cmmsa_a8_output_20261011T070000Z_135b1f28'
    assert receipt['terminal']['native_terminal'] and not receipt['terminal']['compile_green']
    assert [r['native_exit'] for r in receipt['terminal']['stages']]==[0,0,0,0,1,125,125]
    custody=receipt['custody'];verify_local_custody(custody['short_path'],custody['repository_path'],custody['remote_sha256'],custody['bytes'])
    assert custody['remote_sha256']=='F94CD8899B40E42802B5294EF4EFD0189F9584EBE8E1FAEABCC5826FED8A56A3'
    assert digest(ROOT/'input-archive.tar.gz')=='70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
    target=HERE/'full114-native-diagnostic-packet-v1';target.mkdir(exist_ok=False)
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
        for stem in ('RectangularGLRowCompletion',):
            for suffix in ('.lean','Checks.lean'):
                name='lean/PvNP/RealizableHardness/'+stem+suffix;data=tar.extractfile(name).read()
                assert manifest['project_sources'][name]==dict(bytes=len(data),sha256=hashlib.sha256(data).hexdigest().upper())
                retain(stem+suffix,data,str(ROOT/'input-archive.tar.gz')+'!'+name)
    raw=(target/'stage-4.stdout').read_text(encoding='utf-8')
    headers=re.findall(r'(?m)^error: lean/.*\.lean:\d+:\d+:.*$',raw)
    assert len(headers)==1
    assert sum('RectangularGLRowCompletion.lean:' in line for line in headers)==1
    assert receipt['terminal']['stages'][4]['diagnostics']['errors']==2
    parts=re.split(r'(?m)(?=^(?:error: |warning: |[✔⚠✖] |Some required targets))',raw)
    for stem in ('RectangularGLRowCompletion',):
        selected=''.join(p for p in parts if re.match(r'^(?:error|warning): lean/PvNP/RealizableHardness/'+stem+r'\.lean:',p))
        retain(stem+'-diagnostics.txt',selected.encode('utf-8'),'Complete derived diagnostic blocks from the exact raw stage-4.stdout')
    retain('terminal-custody.json',(check/'terminal-custody.json').read_bytes(),str(check/'terminal-custody.json'))
    retain('control.snapshot.py',Path(__file__).read_bytes(),str(Path(__file__).resolve()))
    value=dict(files=files,run=marker['run'],original_handle=50327,native_exit=1,complete_stage4_streams=True,
        stages=[0,0,0,0,1,125,125],exact_source_error_headers=headers,source_error_count=1,
        original_terminal_broad_error_count=2,unsolved_goals=0,derived_diagnostics_are_not_raw_streams=True,accepted=False)
    (target/'index.json').open('x').write(json.dumps(value,indent=2)+'\n')
    print(json.dumps(dict(folder=str(target),complete_files=len(files),source_errors=1,broad_terminal_error_count=2,
        index_sha256=digest(target/'index.json'))),flush=True)
if __name__=='__main__':main()

