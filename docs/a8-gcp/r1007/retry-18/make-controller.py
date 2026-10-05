"""Generate a successor harness; preserve retry17 immutable inputs unchanged."""
from pathlib import Path
import ast
HERE=Path(__file__).resolve().parent
prior=(HERE.parent/'retry-17/controller.py').read_text(encoding='utf-8')
text=prior.replace('integrated17_import','integrated18_import').replace('capture-integrated-17','capture-integrated-18').replace('retry-17/','retry-18/').replace("'prepare17'","'prepare18'")
needle="    common.write_new(HERE/'cloud_capture.snapshot.py',cloud)"
replacement='''    start=cloud.index('    removed = []\\n')
    end=cloud.index('    snapshot(evidence)',start)
    invalidation="""    removed = []
    invalidated = {}
    for rel in manifest['owned_sources']:
        suffix=rel.removeprefix('lean/').removesuffix('.lean')
        for root in [work/'.lake/build/lib/lean',work/'.lake/build/ir']:
            stem=root/suffix
            for path in sorted(stem.parent.glob(stem.name+'.*')):
                assert path.is_file() and path.resolve().is_relative_to(work.resolve())
                name=str(path.relative_to(work))
                invalidated[name]={'sha256':digest(path),'nlink_before':path.stat().st_nlink}
                path.unlink()
                removed.append(name)
            assert not list(stem.parent.glob(stem.name+'.*')), 'Owned auxiliary remains'
    save(evidence/'invalidated-project-objects.json',removed)
    save(evidence/'invalidated-owned-artifacts.json',invalidated)
    save(evidence/'owned-artifact-absence-before-compile.json',{'owned_sources':manifest['owned_sources'],'roots':['.lake/build/lib/lean','.lake/build/ir'],'all_absent':True,'prior_cache_untouched':True})
"""
    cloud=cloud[:start]+invalidation+cloud[end:]
    ast.parse(cloud)
    common.write_new(HERE/'cloud_capture.snapshot.py',cloud)'''
assert text.count(needle)==1
text=text.replace(needle,replacement)
ast.parse(text)
with (HERE/'controller.py').open('x',encoding='utf-8',newline='\n') as stream: stream.write(text)
print('Successor controller syntax verified; no compiler executed')
