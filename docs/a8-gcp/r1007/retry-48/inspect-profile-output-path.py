"""Read exact frozen profiling runtime declarations and output callsites."""
import tarfile,json
from pathlib import Path
p=Path(__file__).resolve().parent
archive=p.parent/'captures/capture-integrated-48/dependency-baseline/core-sources.tar.gz'
needles=['displayCumulativeProfilingTimes','profileitM','def profileitIO','profiler.threshold','lean_profileit','profiler.emit']
rows=[]
with tarfile.open(archive) as t:
    for m in t.getmembers():
        if not m.isfile() or not m.name.endswith(('.lean','.cpp','.h')): continue
        lines=t.extractfile(m).read().decode('utf-8','replace').splitlines()
        for i,line in enumerate(lines):
            if any(n in line for n in needles):
                a=max(0,i-3); b=min(len(lines),i+10)
                rows.append({'file':m.name,'line':i+1,'context':'\n'.join(f'{j+1}: {lines[j]}' for j in range(a,b))})
with (p/'profile-output-implementation.json').open('x',encoding='utf-8') as f:json.dump({'matches':rows,'frozen_core_only':True,'local_compilation':False},f,indent=2)
for r in rows: print(json.dumps(r,ensure_ascii=True))
