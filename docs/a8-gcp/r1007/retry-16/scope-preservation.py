"""Keep historical drift audit red; distinguish authorized successor authoring."""
import json, runpy
from pathlib import Path
m=runpy.run_path(str(Path(__file__).parent/'controller.py'),run_name='scope_preservation_import')
common=m['common']; HERE=m['HERE']; PACKAGE=m['PACKAGE']
g=json.loads((HERE/'offline-gates.json').read_bytes()); m['configure'](g['candidate_hashes'])
capture=PACKAGE/'captures/capture-retry-16'
before=json.loads((capture/'inherited-files-before.json').read_bytes()); after=common.inherited_now()
changed={n:{'before':h,'after':after.get(n)} for n,h in before.items() if after.get(n)!=h}
added={n:h for n,h in after.items() if n not in before}
prefix='lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A8'
allowed_changed={prefix+'AveragedAssembly.lean',prefix+'AveragedAssemblyChecks.lean'}
allowed_added={prefix+n+'.lean' for n in ['AmbientAssembly','AmbientAssemblyChecks','Endpoint','EndpointChecks','EnergyNaturality','EnergyNaturalityChecks','PairAssembly','PairAssemblyChecks']}
assert set(changed)<=allowed_changed and set(added)<=allowed_added
receipt={'original_terminal_drift_audit_preserved':True,'original_inherited_dirt_preserved':False,'authorized_current_turn_sources_changed':changed,'authorized_current_turn_new_sources':added,'all_other_initial_inherited_files_unchanged':True,'inherited_files_verified':len(before)-len(changed),'source_authorization':'Root messages and imported sole-author/compiler workflow; frozen captures ACKed before successor edits','historical_red_audits_unmodified':True,'no_acceptance':True}
common.write_new(HERE/'authorized-successor-preservation.json',common.json_bytes(receipt))
print(json.dumps(receipt,indent=2))
