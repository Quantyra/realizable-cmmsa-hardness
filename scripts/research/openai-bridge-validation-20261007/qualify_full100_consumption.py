"""Custody/termination-bound graph and exact type-DAG qualification; no Lean."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
from full100_consumption_controller import ROOT, ready, VM_ID
from custody_checks import verify_local_custody


def main():
    loaded, runner, binding = ready()
    marker = json.loads((ROOT/'launch-once.json').read_bytes())
    check = Path(marker['preflight'])
    receipt = json.loads((check/'terminal-custody.json').read_bytes())
    stop = json.loads((check/'vm-termination.json').read_bytes())
    if receipt['run'] != binding['run'] or stop['run'] != binding['run'] or not stop['custody_verified_before_stop']:
        raise RuntimeError('Foreign trace custody/termination')
    if str(stop['independent']['id']) != VM_ID or stop['independent']['status'] != 'TERMINATED':
        raise RuntimeError('Independent dedicated termination unproven')
    terminal = receipt['probe_terminal']
    if terminal['probe_native_exit'] != 0 or terminal['failure'] is not None or (terminal['project_sources_preserved'],terminal['compiled_objects_preserved']) != (327,661):
        raise RuntimeError('Trace success/preservation unproven')
    custody = receipt['custody']
    verify_local_custody(custody['short_path'],custody['repository_path'],custody['remote_sha256'],custody['bytes'])
    destination = ROOT/'qualification'
    destination.mkdir()
    names = ['probe.stdout','probe.stderr','tooling/probe.lean','tooling/postprocess.py','tooling/preparation-status.json']
    with tarfile.open(custody['repository_path'],'r:gz') as archive:
        for name in names:
            member = archive.getmember(name)
            if not member.isfile(): raise RuntimeError('Non-file trace tooling/output')
            target = destination/name; target.parent.mkdir(parents=True,exist_ok=True)
            with target.open('xb') as output: shutil.copyfileobj(archive.extractfile(member),output)
    for name, pin in binding['tooling_readiness']['files'].items():
        data = (destination/'tooling'/name).read_bytes()
        if len(data) != pin['bytes'] or hashlib.sha256(data).hexdigest().upper() != pin['sha256']:
            raise RuntimeError('Executed tooling identity mismatch')
    commands = [
        [sys.executable,'-B','-X','utf8',str(destination/'tooling/postprocess.py'),str(destination/'probe.stdout'),str(destination/'graphs')],
        [sys.executable,'-B','-X','utf8',str(Path(__file__).with_name('qualify_full89_type_dags.py')),str(destination/'graphs/validated-graphs.json'),str(destination/'type-dag-qualification.json')]]
    for index, command in enumerate(commands):
        child = subprocess.Popen(command,stdout=subprocess.PIPE,stderr=subprocess.PIPE,creationflags=subprocess.CREATE_NO_WINDOW)
        while True:
            try: out,err = child.communicate(timeout=30); break
            except subprocess.TimeoutExpired: print('Same local Python graph qualification remains live',child.pid,flush=True)
        (destination/f'{index}.stdout').write_bytes(out); (destination/f'{index}.stderr').write_bytes(err)
        (destination/f'{index}.command.json').write_text(json.dumps({'argv':command,'native_exit':child.returncode})+'\n',encoding='utf-8')
        print(out.decode('utf-8'),end='',flush=True)
        if child.returncode: raise RuntimeError('Graph qualification failed; retain exact outputs')
    graph = json.loads((destination/'graphs/validated-graphs.json').read_bytes())
    if len(graph['graphs']['exact192-native']['roots']) != 192 or len(graph['graphs']['focused-twentyfour-consumer']['roots']) != 24:
        raise RuntimeError('Expanded graph scope incomplete')
    qualified = json.loads((destination/'type-dag-qualification.json').read_bytes())
    summary = {'schema':'full100-exact192-consumption-qualified-structure-v1','run':binding['run'],
               'custody':custody,'termination':stop,'nodes':qualified['nodes'],
               'exact_type_edge_matches':qualified['exact_type_edge_matches'],
               'project_modules':qualified['project_modules'],'external_boundary_count':len(qualified['external_boundaries']),
               'unresolved_by_graph':{k:len(v['unresolved']) for k,v in graph['graphs'].items()},
               'structural_trace_qualification':True,'source_selection_complete':False,
               'independent_body_review_complete':False,'accepted':False,'full_goal_complete':False,'local_compilation':False}
    (destination/'qualification-summary.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'nodes':summary['nodes'],'modules':len(summary['project_modules']),
                      'external_boundaries':summary['external_boundary_count'],'accepted':False}),flush=True)


if __name__ == '__main__':
    main()
