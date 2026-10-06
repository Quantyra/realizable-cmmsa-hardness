"""Supplement preserved raw drift with exact authorized successor custody; no Lean or Git writes."""
from pathlib import Path
import json,hashlib,runpy,sys
HERE=Path(__file__).resolve().parent; PACKAGE=HERE.parent; REPO=PACKAGE.parents[2]
run=PACKAGE/'runs'/sys.argv[1]; capture=PACKAGE/'captures'/sys.argv[2]; successor=PACKAGE/'retry-16'/sys.argv[3]
before=json.loads((capture/'inherited-files-before.json').read_bytes())
for name,row in before.items():
    path=REPO/name
    assert (not path.exists()) if row.get('missing') else path.is_file() and hashlib.sha256(path.read_bytes()).hexdigest().upper()==row['sha256'],name
m=runpy.run_path(str(HERE/'controller.py'),run_name='preservation_import'); m['configure']()
after=m['common'].inherited_now(); extras=set(after)-set(before)
auth=json.loads((HERE/'authorized-owned-successor-paths.json').read_bytes()); assert extras<=set(auth['paths_before']),extras
custody=json.loads((successor/'custody.json').read_bytes())
for offer_name in sys.argv[4:]:
    extra=json.loads((PACKAGE/'retry-16'/offer_name/'custody.json').read_bytes())
    assert not set(custody['exact_sha256']) & set(extra['exact_sha256'])
    custody['exact_sha256'].update(extra['exact_sha256'])
for name in extras: assert after[name]['sha256']==custody['exact_sha256'][Path(name).name],name
manifest=json.loads((capture/'manifest.json').read_bytes())
for name in m['OWNED']: assert hashlib.sha256((capture/'inputs'/name).read_bytes()).hexdigest().upper()==manifest['project_sources'][name]['sha256'],name
value={'initial_inherited_states':len(before),'all_initial_inherited_states_unchanged':True,'raw_inherited_preservation':json.loads((run/'terminal.json').read_bytes())['inherited_dirt_preserved'],'raw_red_audit_preserved':True,'authorized_owned_mutations':sorted(extras),'successor_custody':str(successor.relative_to(PACKAGE))+'/custody.json','authorization_receipt':str(HERE.relative_to(PACKAGE))+'/authorized-owned-successor-paths.json','all_frozen_compiled_inputs_preserved':True,'owner_hashes_after':{name:after[name]['sha256'] for name in extras}}
value['additional_successor_custodies']=['retry-16/'+n+'/custody.json' for n in sys.argv[4:]]
m['common'].write_new(run/'authorized-successor-preservation.json',m['common'].json_bytes(value))
print(json.dumps(value,indent=2))
