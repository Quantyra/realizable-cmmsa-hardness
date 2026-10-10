"""Derive two existing-boot settled duplicate recovery scopes; no power operation."""
import ast
import json
import sys
from pathlib import Path
from custody_checks import digest,verify_local_custody
from prepare_builder02_full105 import OUTPUT

HERE=Path(__file__).parent
SCOPES=['full104-actual-consumer-exact-energy-resource02','full87-resource02']
TARGETS=[5,5]


def once(text,old,new):
    assert text.count(old)==1,old
    return text.replace(old,new,1)


def main(write=False):
    remote_template=HERE/'full100_cache_repoint_v1.py'
    runner_template=HERE/'run_full97_trace_cache_repoint_v1.py'
    assert digest(remote_template)=='C29A9BC269BAFB04FB231D0E372B7DA0B4F65136834C988185EEAEA1E5A78762'
    assert digest(runner_template)=='CA698B63C718F7D6D2EBF887C17B8595F1F98939528266D7AF474F7FD661167C'
    records=[]
    for i,resource in enumerate(SCOPES,1):
        parent=OUTPUT.parent/resource;m=json.loads((parent/'launch-once.json').read_bytes())
        check=Path(m['preflight']);t=json.loads((check/'terminal-custody.json').read_bytes());c=t['custody']
        verify_local_custody(c['short_path'],c['repository_path'],c['remote_sha256'],c['bytes'])
        stop=json.loads((check/'vm-termination.json').read_bytes())
        assert stop['run']==t['run']==m['run'] and stop['independent']['status']=='TERMINATED'
        assert str(stop['independent']['id'])=='7237681467779354904' and t['terminal']['native_terminal']
        remote='full105-storage-cache-repoint-v'+str(i+2)
        text=remote_template.read_text(encoding='utf-8')
        text=once(text,"RUN = 'cmmsa_a8_output_20261009T080216Z_9e248b8e'",'RUN = '+repr(m['run']))
        text=once(text,"CONTROL = HOME / 'full100-cache-repoint-v1'",'CONTROL = HOME / '+repr(remote))
        text=once(text,"MANIFEST_SHA = '98537853DEE1623F6455AD1FA75116FE65FC47134B061EEE3F93E3FE0EC418EF'",'MANIFEST_SHA = '+repr(digest(parent/'capture-manifest.json')))
        text=once(text,"ARCHIVE_SHA = 'C18468B03B793BF120B89A266622718FF299F082FF536B8D4D85A421A17C94BA'",'ARCHIVE_SHA = '+repr(c['remote_sha256']))
        text=text.replace('full100-matrix-fourier-bullet-repair-resource02-launch-once.json','full105-actual-consumer-exact-energy-repair-resource02-launch-once.json')
        text=text.replace('full100_verify.py','full105_verify.py')
        text=once(text,'TARGET = 5 * 1024**3','TARGET = '+str(TARGETS[i-1])+' * 1024**3')
        name='full105_storage_cache_repoint_v'+str(i+2)+'.py'
        templates={name:text}
        runner=runner_template.read_text(encoding='utf-8')
        runner=runner.replace('from full97_builder02_controller import VM, VM_ID, context, local_gates','from full105_builder02_controller import ROOT, VM, VM_ID, context, local_gates')
        runner=runner.replace('from full97_consumption_controller import ROOT, ready','')
        runner=runner.replace('from full97_capture_gates import validate_successor','from full105_capture_gates import validate_successor')
        runner=runner.replace('full97-trace-cache-repoint-v1',remote).replace('full97_trace_cache_repoint_v1.py',name)
        ready='''def ready():
    validate_successor()
    loaded,runner=context()
    local_gates(loaded['common'],loaded)
    paths=sorted((ROOT/'staging-controls').glob('*/commands.json'))
    assert paths
    failed=json.loads(paths[-1].read_bytes())
    assert failed[-1]['native_exit']==1 and 'full105_verify.py' in ' '.join(failed[-1]['argv'])
    assert not (ROOT/'launch-once.json').exists()
    return loaded,runner,json.loads((ROOT/'resource-binding.json').read_bytes())


'''
        runner=once(runner,'def main(action):',ready+'def main(action):')
        templates['run_full105_storage_cache_repoint_v'+str(i+2)+'.py']=runner
        for filename,source in templates.items():
            ast.parse(source);p=HERE/filename;b=source.encode()
            if write:p.open('xb').write(b)
            else:assert p.read_bytes()==b
            records.append(dict(path=filename,sha256=digest(p),settled_resource=resource,
                                run=m['run'],archive_sha256=c['remote_sha256'],manifest_sha256=digest(parent/'capture-manifest.json')))
    result=dict(schema='full105-existing-boot-storage-recovery-derivation-v1',controls=records,targets_GiB=TARGETS,
                existing_staging_boot_only=True,power_operations=False,
                all_per_file_identity_and_reversible_transaction_guards_preserved=True,
                current_full105_and_canonical_cache_excluded=True,compiler_invoked=False,accepted=False)
    p=HERE/'full105-storage-v3-v4-recovery-derivation.json';b=(json.dumps(result,indent=2)+'\n').encode()
    if write:p.open('xb').write(b)
    else:assert p.read_bytes()==b
    print('Measured settled5GiB+5GiB scopes retain exact per-file review, provenance and reversibility guards')


if __name__=='__main__':
    assert sys.argv[1:] in ([],['--write'])
    main(sys.argv[1:]==['--write'])
