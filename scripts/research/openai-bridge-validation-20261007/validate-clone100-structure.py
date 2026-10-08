"""Finite structural validation of direct Clone100 bridge rejection; no Lean."""
import hashlib,json,urllib.request,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parent
URL='https://raw.githubusercontent.com/openai/math/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/UniqueGames/PCP/Clone100.lean'
PIN='c11afe1c779208ac9e428ac478c2a76283344589fcd8e07b2c7cd488123fadd7'
with urllib.request.urlopen(URL,timeout=60) as response:source=response.read()
assert hashlib.sha256(source).hexdigest()==PIN
LOCAL_COMMIT='8c3d3f741a1435d671df6325e14e66338a1c22dd'
LOCAL_PATH='lean/PvNP/RealizableHardness/ActualMZOuterSourceContract.lean'
local_source=subprocess.check_output(['git','show',LOCAL_COMMIT+':'+LOCAL_PATH],cwd=ROOT)
local_text=local_source.decode()
assert 'degree_ten' in local_text and 'card \u2264 10' in local_text
assert 'overlap_one' in local_text and 'card \u2264 1' in local_text
patterns=[(0,1,2),(0,0,1),(0,1,0),(0,1,1),(0,0,0)]
results=[]
for variables in patterns:
    total=first_zero=incidence=0
    for i in range(100):
        for j in range(100):
            if i==j:continue
            for k in range(100):
                if k==i or k==j:continue
                total+=1
                first_zero+=i==0
                support={(variables[0],i),(variables[1],j),(variables[2],k)}
                assert len(support)==3
                incidence+=(variables[0],0) in support
    one={(variables[0],0),(variables[1],1),(variables[2],2)}
    two={(variables[0],0),(variables[1],1),(variables[2],3)}
    assert total==970200 and first_zero==9702
    assert incidence==9702*variables.count(variables[0]) and incidence>10
    assert len(one&two)==2 and len(one&two)>1
    results.append({'equality_pattern':variables,'indexed_rows':total,'first_clone_zero_rows':first_zero,'target_name_row_degree':incidence,'two_row_overlap':len(one&two)})
result={'local_contract':{'commit':LOCAL_COMMIT,'path':LOCAL_PATH,'sha256':hashlib.sha256(local_source).hexdigest()},'upstream_url':URL,'source_sha256':PIN,'local_degree_cap':10,'local_overlap_cap':1,'all_five_equality_patterns_checked':results,'decision':'Reject direct Clone100 output for the existing Encoded3Lin structural interface','basis':'Exact indexed-row enumeration and pair-support intersection;bijections of names preserve both quantities','lean_kernel_verified':False,'upstream_proof_closure_verified':False,'new_transformation_ruled_out':False}
(ROOT/'clone100-structural-result.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2))
