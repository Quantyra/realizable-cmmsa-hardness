import tarfile
p=r'''C:\Users\dfred\.quantyra\builder02\full112-exact-real-complex-operators-repair2-resource02\checks\20261011T051347974720Z\cmmsa_a8_output_20261011T051406Z_3ef6ddc2_evidence.tar.gz'''
with tarfile.open(p,'r:gz') as t:
 for m in t.getmembers():
  if 'package-sources' in m.name or 'input-archive' in m.name or 'manifest' in m.name: print(m.name,m.size)
