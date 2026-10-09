"""Derive full251/focused83 controls only from actual qualified native custody."""
import ast
import json
import re
import sys
import tarfile
from pathlib import Path
from custody_checks import digest, verify_local_custody
from prepare_builder02_full103 import OUTPUT

HERE=Path(__file__).parent
NAMES=['full100_consumption_v2_controller.py','full100_consumption_v2_worker.py',
       'stage_full100_consumption_v2.py','terminate_full100_consumption_v2.py',
       'qualify_full100_consumption_v2.py','test_full100_consumption_v2_gates.py']


def main(write=False):
    marker=json.loads((OUTPUT/'launch-once.json').read_bytes());check=Path(marker['preflight'])
    receipt=json.loads((check/'terminal-custody.json').read_bytes());custody=receipt['custody']
    stop=json.loads((check/'vm-termination.json').read_bytes())
    q=check/'qualified-native'/marker['run']/'material-expanded-native-report.json'
    qualified=json.loads(q.read_bytes())
    assert marker['run']==receipt['run']==stop['run'] and receipt['terminal']['compile_green']
    assert qualified['full103_expanded_native_gates_green'] and qualified['expanded_requested_axiom_count']==251
    assert qualified['owned_warning_headers']==qualified['inherited_regression_headers']==[0]*7
    assert qualified['project_closure_sources']==340 and qualified['cache_objects_unchanged']==566
    assert stop['independent']['status']=='TERMINATED' and str(stop['independent']['id'])=='7237681467779354904'
    verify_local_custody(custody['short_path'],custody['repository_path'],custody['remote_sha256'],custody['bytes'])
    with tarfile.open(custody['repository_path']) as archive:
        objects=json.loads(archive.extractfile('object-after.json').read())
        manifest=json.loads(archive.extractfile('capture-manifest.json').read())
    expected={'.lake/build/lib/lean/'+p.removeprefix('lean/').removesuffix('.lean')+'.olean' for p in manifest['project_sources']}
    assert len(expected)==340 and expected<=set(objects)
    rows=[]
    for name in NAMES:
        text=(HERE/name).read_text(encoding='utf-8')
        text=text.replace('full100-matrix-fourier-bullet-repair','full103-spectral-owned-warning-repair')
        text=text.replace('full100','full103').replace('Full100','Full103')
        text=text.replace('cmmsa_a8_output_20261009T092534Z_c0fd3e11',marker['run'])
        for old,new in [('327','340'),('192','251'),('661',str(len(objects)))]:text=text.replace(old,new)
        text=re.sub(r'\b24\b','83',text)
        text=text.replace('focused-twentyfour-consumer','focused-eighty-three-consumer')
        if name=='full100_consumption_v2_controller.py':
            old="readiness['additional_roots'] != REQUESTS"
            assert text.count(old)==1
            text=text.replace(old,"readiness['additional_roots'] != SPECTRAL_ADDITIONS()[1]")
            old='from prepare_builder02_full103 import OUTPUT'
            assert text.count(old)==1
            text=text.replace(old,old+'\nfrom prepare_builder02_full101 import additions as SPECTRAL_ADDITIONS')
        ast.parse(text);path=HERE/name.replace('full100','full103');data=text.encode()
        if write:path.open('xb').write(data)
        else:assert path.read_bytes()==data
        rows.append(dict(source=name,source_sha256=digest(HERE/name),target=path.name,target_sha256=digest(path)))
    result=dict(schema='full103-qualified-actual-run-consumption-control-derivation-v1',records=rows,
        run=marker['run'],native_archive_sha256=custody['remote_sha256'],qualified_report_sha256=digest(q),
        actual_native_object_entries=len(objects),project_sources=340,requested_roots=251,focused_consumers=83,
        all_parent_trace_algorithms_and_source_object_dependency_resource_guards_preserved=True,
        preparation59_spectral_additions_distinguished_from_cumulative78_requests=True,
        compiler_invoked=False,probe_executed=False,accepted=False)
    path=HERE/'full103-consumption-control-derivation.json';data=(json.dumps(result,indent=2)+'\n').encode()
    if write:path.open('xb').write(data)
    else:assert path.read_bytes()==data
    print(json.dumps(dict(controls=6,run=marker['run'],actual_object_entries=len(objects),roots=251,focused=83)))


if __name__=='__main__':
    assert sys.argv[1:] in ([],['--write'])
    main(sys.argv[1:]==['--write'])
