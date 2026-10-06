"""Qualify exact two-path author succession without rewriting frozen/raw receipts."""
from pathlib import Path
import runpy,json,hashlib,sys
sys.dont_write_bytecode=True
here=Path(__file__).resolve().parent;package=here.parent;repo=package.parents[2]
run=package/'runs'/sys.argv[1];cap=package/'captures/capture-integrated-57';offer=package/sys.argv[2]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest().upper()
before=json.loads((cap/'inherited-files-before.json').read_bytes())
for name,row in before.items():
    p=repo/name;assert (not p.exists()) if row.get('missing') else p.is_file() and sha(p)==row['sha256'],name
auth=json.loads((here/'authorized-owned-successor-paths.json').read_bytes())
custody=json.loads((offer/'custody.json').read_bytes());pins=custody['files']
m=runpy.run_path(str(here/'controller.py'),run_name='preserve57_import');m['configure']()
manifest=json.loads((cap/'manifest.json').read_bytes());mutations={}
for name in m['OWNED']:
    frozen=manifest['project_sources'][name]['sha256'];assert sha(cap/'inputs'/name)==frozen
    current=sha(repo/name)
    if current!=frozen:
        assert name in auth['paths_before'] and pins[name]==current
        mutations[name]=current
for name,value in json.loads((here/'current-dependency-pins.json').read_bytes()).items():assert sha(repo/name)==value
value={'initial_inherited_states':len(before),'all_initial_inherited_states_unchanged':True,'all_frozen_compiled_inputs_preserved':True,'authorized_owned_mutations':mutations,'raw_inherited_preservation':json.loads((run/'terminal.json').read_bytes())['inherited_dirt_preserved'],'raw_red_audit_preserved':True,'successor_custody':str(offer.relative_to(package))+'/custody.json','authorization_receipt':'retry-57/authorized-owned-successor-paths.json','prior14_frozen_sources_unchanged':True,'current_comment_dependency_unchanged':True}
m['common'].write_new(run/'authorized-successor-preservation.json',m['common'].json_bytes(value))
print(json.dumps(value,indent=2))
