"""Capture two frozen source boundaries and honest missing metadata."""
import hashlib,json,tarfile
from pathlib import Path
H=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest().upper()
def main():
 s=H/'numeric-fixed-score-conditional-agreement-offer-20261011-v1'
 pins={'ActualFixedScoreConditionalAgreement.lean':'5F57CC8D216A41722D822EF049747806B5F3860831326E9F7D191380B1F43EB2','ARGUMENT.md':'C710CB25C4E9D82A8ADC95E53562672744AEA50219B1B6A632C10D619DD1841D','first-offer-reconstruction-v1/ActualFixedScoreConditionalAgreement.lean':'B0E094560A638DB4AF4D9AAC9820F3B8CF7F60AA3FAB3C0A91B4A28CA85616E9'}
 data={n:(s/n).read_bytes() for n in pins}
 for n,b in data.items():assert sha(b)==pins[n];b.decode('utf-8');assert not b.startswith(bytes.fromhex('efbbbf'))
 new=b'((actualRowGrassEquiv I copies U d).symm L).val \xe2\x89\x83\xe2\x82\x97[ZMod 2] L.val := by'
 old=b'(actualRowGrassEquiv I copies U d).symm L |>.val \xe2\x89\x83\xe2\x82\x97[ZMod 2] L.val := by'
 assert data['ActualFixedScoreConditionalAgreement.lean'].count(new)==1
 assert data['ActualFixedScoreConditionalAgreement.lean'].replace(new,old)==data['first-offer-reconstruction-v1/ActualFixedScoreConditionalAgreement.lean']
 a=Path('C:/Users/dfred/.quantyra/builder02/full114-exact-real-complex-operators-repair4-resource02/input-archive.tar.gz')
 assert sha(a.read_bytes())=='70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
 deps=[]
 with tarfile.open(a,'r:gz') as t:
  for n in ('lean/PvNP/RealizableHardness/ZoomOutTransfer.lean','lean/PvNP/RealizableHardness/ActualFiniteLaw.lean','lean-toolchain','lake-manifest.json'):
   b=t.extractfile(n).read();deps.append(dict(member=n,bytes=len(b),sha256=sha(b)))
 p=H/'numeric-row-deletion-capture-v1/ActualTaggedRowDeletion.lean';assert sha(p.read_bytes())=='F844D422FEF025399462872F9F59D6EC1E8BA41C28DCE4D95B20C463B876390B'
 deps.append(dict(path=str(p),sha256=sha(p.read_bytes())))
 d=H/'numeric-fixed-score-conditional-agreement-capture-v1';d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text\n')
 rows=[]
 for n,b in data.items():
  p=d/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b);assert p.read_bytes()==b;rows.append(dict(path=n,bytes=len(b),sha256=sha(b)))
 (d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
 index=dict(original_directory=str(s),files=rows,verified_direct_dependencies=deps,observations=['First offered B0E094 source reconstructed by exact inverse parenthesization edit after current source changed before capture ACK; inverse bytes verified.','No original manifest or Checks.lean was offered at this boundary.','Earlier overwritten mojibake/provider intermediate bytes unavailable, not claimed preserved.'],compiler_invoked=False,accepted=False,immutable_capture=True)
 (d/'index.json').write_text(json.dumps(index,indent=2)+'\n',encoding='utf-8');print(sha((d/'index.json').read_bytes()))
if __name__=='__main__':main()
