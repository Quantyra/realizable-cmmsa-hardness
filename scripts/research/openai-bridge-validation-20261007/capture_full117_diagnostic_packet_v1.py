"""Preserve exact failed-stage source and complete raw diagnostic contexts."""
import hashlib,json,tarfile
from pathlib import Path
H=Path(__file__).resolve().parent
R=Path('C:/Users/dfred/.quantyra/builder02/full117-exact-real-complex-operators-repair7-resource02')
def sha(b):return hashlib.sha256(b).hexdigest().upper()
def main():
 m=json.loads((R/'launch-once.json').read_bytes());assert m['run']=='cmmsa_a8_output_20261011T231800Z_f8f19b01'
 c=Path(m['preflight']);receipt=json.loads((c/'terminal-custody.json').read_bytes());assert receipt['terminal']['native_terminal'] and not receipt['terminal']['compile_green']
 a=Path(receipt['custody']['repository_path']);assert sha(a.read_bytes())==receipt['custody']['remote_sha256']
 with tarfile.open(a,'r:gz') as t:data={n:t.extractfile(n).read() for n in ('stage-4.stdout','stage-4.stderr','stage-4.native-exit','stage-4.command.json','dedicated-worker-terminal.json')}
 assert data['stage-4.stdout'].decode().count('error: lean/PvNP/RealizableHardness/ExactRestrictedAdjoint.lean:')==6
 member='lean/PvNP/RealizableHardness/ExactRestrictedAdjoint.lean'
 with tarfile.open(R/'input-archive.tar.gz','r:gz') as t:data['ExactRestrictedAdjoint.lean']=t.extractfile(member).read()
 data['terminal-custody.json']=(c/'terminal-custody.json').read_bytes();data['launch-once.json']=(R/'launch-once.json').read_bytes()
 d=H/'full117-restricted-adjoint-diagnostic-packet-v1';d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text\n');rows=[]
 for n,b in data.items():p=d/n;p.write_bytes(b);assert p.read_bytes()==b;rows.append(dict(path=n,bytes=len(b),sha256=sha(b)))
 (d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
 value=dict(run=m['run'],original_handle=39869,native_exit=1,first_failed_module='PvNP.RealizableHardness.ExactRestrictedAdjoint',stage4_errors=6,stage4_unsolved_goals=2,complete_untruncated_failed_stage_retained=True,files=rows,input_archive_sha256=sha((R/'input-archive.tar.gz').read_bytes()),native_archive_sha256=sha(a.read_bytes()),compiler_replayed=False,accepted=False)
 (d/'index.json').write_text(json.dumps(value,indent=2)+'\n',encoding='utf-8');print(json.dumps(dict(packet=str(d),index_sha256=sha((d/'index.json').read_bytes()),source_sha256=sha(data['ExactRestrictedAdjoint.lean']))))
if __name__=='__main__':main()
