"""Correct only the stale local validation reference before any native launch."""
import ast,json
from pathlib import Path
from custody_checks import digest

HERE=Path(__file__).resolve().parent

def main():
    source=HERE/'run_full114_native_openssh_v1.py'
    assert digest(source)=='51D704921D969E21B13BF24856B85B3AC3722422EF5C2FA6146449732B1E77CF'
    old=b'full114-execution-control-validation-20261011T053328425826Z/result.json'
    new=b'full114-execution-control-validation-20261011T062522107773Z/result.json'
    raw=source.read_bytes();assert raw.count(old)==1 and not (HERE/old.decode()).exists()
    validation=HERE/new.decode()
    assert digest(validation)=='E403DE62595FFD7D7F8DF0682B2E96B630981D953AD94911555CE8586EB90C16'
    evidence=json.loads(validation.read_bytes())
    for name,pin in evidence['source_snapshots'].items():assert digest(HERE/name)==pin
    target=HERE/'run_full114_native_openssh_v2.py';updated=raw.replace(old,new)
    ast.parse(updated);assert updated.replace(new,old)==raw
    target.open('xb').write(updated)
    wrapper=HERE/'run_full114_resume_step_v4.py'
    wrapper_raw=wrapper.read_bytes();previous=b"'run_full114_native_openssh_v1.py'"
    assert wrapper_raw.count(previous)==1
    successor=HERE/'run_full114_resume_step_v5.py'
    wrapper_updated=wrapper_raw.replace(previous,previous+b", 'run_full114_native_openssh_v2.py'")
    ast.parse(wrapper_updated);successor.open('xb').write(wrapper_updated)
    result=dict(original_adapter_sha256=digest(source),successor_adapter_sha256=digest(target),
        original_wrapper_sha256=digest(wrapper),successor_wrapper_sha256=digest(successor),
        original_missing_path=old.decode(),actual_validation_path=new.decode(),validation_sha256=digest(validation),
        all_core_source_snapshots_verified=True,sole_adapter_change='Existing validation reference corrected to actual Full114 validation',
        original_adapter_executed=False,compiler_invoked=False,cloud_action=False,core_controls_changed=False)
    (HERE/'full114-native-adapter-derivation-v2.json').open('x').write(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result),flush=True)

if __name__=='__main__':main()
