"""Read frozen compiler source for profiling output behavior; no compilation."""
import tarfile,re,json
from pathlib import Path
p=Path(__file__).resolve().parent
archive=p.parent/'captures/capture-integrated-48/dependency-baseline/core-sources.tar.gz'
rows=[]
with tarfile.open(archive) as t:
    for m in t.getmembers():
        if not m.isfile() or not re.search(r'(Profiler|Profiling|TopLevel|Shell|Main)\.(lean|cpp)$',m.name): continue
        data=t.extractfile(m).read().decode('utf-8','replace').splitlines()
        for i,line in enumerate(data):
            if 'profil' in line.lower():
                a=max(0,i-4); b=min(len(data),i+7)
                rows.append({'file':m.name,'line':i+1,'context':'\n'.join(f'{j+1}: {data[j]}' for j in range(a,b))})
with (p/'profile-implementation-inspection.json').open('x',encoding='utf-8') as f:json.dump({'frozen_core_archive':str(archive),'matches':rows,'local_compilation':False},f,indent=2)
for row in rows: print(row['file'],row['line'],row['context'],sep='\n')
