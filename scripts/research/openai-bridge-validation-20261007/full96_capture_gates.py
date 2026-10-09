"""Exact additive Full96 input gates; never compile or operate a VM."""
import json
from custody_checks import digest
from prepare_builder02_full90 import capsule
from prepare_builder02_full96 import OUTPUT,PARENT,CANDIDATES,ADDED,validate_expansion

def validate_successor():
    from full95_capture_gates import validate_successor as parent_gate
    parent_gate()
    binding=json.loads((OUTPUT/'resource-binding.json').read_bytes())
    for name,pin in binding['files'].items():assert digest(OUTPUT/name)==pin
    assert digest(OUTPUT/'source-expansion.json')==binding['source_expansion_sha256']
    expansion=json.loads((OUTPUT/'source-expansion.json').read_bytes())
    assert digest(CANDIDATES/'derivation.json')==expansion['candidate_derivation_sha256']
    derivation=json.loads((CANDIDATES/'derivation.json').read_bytes())
    for rel in ADDED:
        path=CANDIDATES/rel.rsplit('/',1)[-1];row=derivation['sources'][path.name]
        assert digest(path)==row['sha256'] and path.stat().st_size==row['bytes']
    assert digest(PARENT/'resource-binding.json')==binding['parent_resource_binding_sha256']
    old=capsule(PARENT/'input-archive.tar.gz');new=capsule(OUTPUT/'input-archive.tar.gz');validate_expansion(old,new)
    assert new['capture-manifest.json']==(OUTPUT/'capture-manifest.json').read_bytes()
    print(json.dumps({'full96_additive_orbit_contract_bridge_scope_verified':True,'sources':325,'profiles':184,'local_compilation':False,'launch_clearance':False}))
if __name__=='__main__':validate_successor()
