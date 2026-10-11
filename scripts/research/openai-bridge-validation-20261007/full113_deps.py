import tarfile,hashlib
p=r'''C:\Users\dfred\.quantyra\builder02\full112-exact-real-complex-operators-repair2-resource02\input-archive.tar.gz'''
with tarfile.open(p,'r:gz') as t:
 names=[m for m in t.getmembers() if any(x in m.name for x in ['RectangularFrameFiberAverage.lean','BinaryMatrixRightOrbit.lean','ActualFiniteBinarySurjectionCounting.lean','RectangularGLRowCompletion.lean','ExactComplexAppendContinuation.lean'])]
 for m in names:
  b=t.extractfile(m).read(); print(m.name,m.size,hashlib.sha256(b).hexdigest())
