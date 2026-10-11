import tarfile,io,hashlib
outer=r'''C:\Users\dfred\.quantyra\builder02\full112-exact-real-complex-operators-repair2-resource02\checks\20261011T051347974720Z\cmmsa_a8_output_20261011T051406Z_3ef6ddc2_evidence.tar.gz'''
with tarfile.open(outer,'r:gz') as t:
 b=t.extractfile('package-sources.tar.gz').read(); print('package archive',len(b),hashlib.sha256(b).hexdigest())
 with tarfile.open(fileobj=io.BytesIO(b),mode='r:gz') as p:
  names=[m for m in p.getmembers() if m.name.endswith('/Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Card.lean') or m.name.endswith('Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Card.lean')]
  for m in names:
   bb=p.extractfile(m).read(); print(m.name,m.size,hashlib.sha256(bb).hexdigest())
archive=r'''C:\Users\dfred\builder02\full112-exact-real-complex-operators-repair2-resource02\input-archive.tar.gz'''
