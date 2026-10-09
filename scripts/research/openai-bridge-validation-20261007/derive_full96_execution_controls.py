"""Derive full325/full184 controls, preserving frozen native qualification gates."""
import ast
import json
from pathlib import Path
from custody_checks import digest
HERE=Path(__file__).parent

def main():
    rows=[]
    for name in ['full95_verify.py','full95_worker.py','full95_builder02_controller.py','stage_full95_builder02.py','full95_postprocess.py','full95_native_audit.py','test_full95_terminal.py']:
        text=(HERE/name).read_text(encoding='utf-8').replace('full95','full96').replace('Full181','Full184')
        text=text.replace('full96-manuscript-moment-syntax-repair-resource02','full96-spectral-orbit-contract-bridge-resource02')
        text=text.replace('full96-manuscript-moment-syntax-repair-builder02-stage','full96-spectral-orbit-contract-bridge-builder02-stage')
        text=text.replace('!= 323','!= 325').replace('!= 181','!= 184').replace('expanded_requested_axiom_count=181','expanded_requested_axiom_count=184')
        if name=='full95_native_audit.py':
            text=text.replace('REQUESTS = SOURCE_REQUESTS + DYADIC_REQUESTS','from prepare_builder02_full96 import REQUESTS as BRIDGE_REQUESTS\n    REQUESTS = SOURCE_REQUESTS + DYADIC_REQUESTS + BRIDGE_REQUESTS')
            text=text.replace("if len(additive['added_sources']) != 4:","if len(additive['added_sources']) != 6:")
            line="    expanded.update(added_project_sources=additive['added_sources'], added_object_hashes={rel:objects[obj] for rel,obj in added_objects.items()}, original173_requests_preserved=True, source_row_independence_native_verified=not extra_bad, manuscript_dyadic_consumer_native_verified=not extra_bad, numeric_NO_proven=False)"
            assert line in text
            text=text.replace(line,line+"\n    expanded.update(added_source_object_identities=[dict(source_path=rel, source_sha256=inner['project_sources'][rel]['sha256'], compiled_object_path=obj, compiled_object_sha256=objects[obj]) for rel,obj in added_objects.items()], legacy_source_keyed_object_hash_field_retained_for_compatibility=True, explicit_contract_bridges_and_right_orbit_helper_native_verified=not extra_bad, universal_Spectral47_inhabitant_proven=False)")
        output=HERE/name.replace('full95','full96');ast.parse(text,filename=str(output))
        with output.open('x',encoding='utf-8',newline='\n') as stream:stream.write(text)
        rows.append(dict(parent=name,parent_sha256=digest(HERE/name),output=output.name,output_sha256=digest(output)))
    with (HERE/'full96-execution-control-derivation.json').open('x',encoding='utf-8') as stream:
        json.dump(dict(schema='full96-exact325-source184-request-controls-v1',controls=rows,sources=325,profiles=184,cumulative_added_source_overlay=6,
            frozen_finisher_sha256='AE79CB1B154685AF9DB0E43885225F49C7EB750C5F6F5A8D2B5595ED3EEE7156',
            typed_source_and_object_identity_pairs_added=True,all_original_native_resource_custody_warning_scope_guards_preserved=True,
            compiler_invoked=False,VM_operation_performed=False,accepted=False,full_goal_complete=False),stream,indent=2);stream.write('\n')
    print('Derived exact full325/full184 controls; frozen finisher unchanged, no launch')
if __name__=='__main__':main()
