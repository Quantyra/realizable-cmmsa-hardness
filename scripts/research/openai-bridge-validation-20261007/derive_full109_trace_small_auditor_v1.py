from pathlib import Path
import ast
here=Path(__file__).parent
text=(here/'audit_full109_trace_cache_large_v2.py').read_text()
text=text.replace("number in (107,109)","number in range(84,90)")
text=text.replace('full109-trace-cache-large-control-derivation-v1.json','full109-trace-small-cache-control-derivation-v1.json')
text=text.replace(" and native['terminal']['compile_green']",'')
anchor=" qualified=json.loads((check/'qualified-native'/marker['run']/'material-expanded-native-report.json').read_bytes())\n assert qualified[f'full{number}_expanded_native_gates_green']"
assert text.count(anchor)==1;text=text.replace(anchor,' # Cleanup requires settled custody/termination, not mathematical qualification of old failed attempts.')
start=text.index(" prior=ROOT.parent/");end=text.index(" baseline=json.loads",start)
text=text[:start]+''' prior=ROOT.parent/'full107-exact-product-energy-repair-resource02/consumption-v3/complete-trace-cache-plan-review-v1-v4-v8.json'
 assert digest(prior)=='14532AA9BF8EC20D6CF1B90934FDF481EB3B90B35AD8B310419F6C03E48A813D'
 baseline_record=next(r for r in json.loads(prior.read_bytes())['plans'] if r['scope']==4)['operation']
 assert digest(baseline_record['local_result'])==baseline_record['result_sha256']
'''+text[end:]
text=text.replace("Path(baseline_record['plan_path'])","Path(baseline_record['local_result'])")
text=text.replace('==9672','==19233')
text=text.replace(" assert len(plan['rows'])==9666 if number==109 else len(plan['rows'])>0", " assert len(plan['rows'])>0")
text=text.replace("row['bytes']>=65536","row['bytes']>=1")
text=text.replace('>=5*1024**3','>=896*1024**2')
text=text.replace("f'cache-large-{action}-audit-native{number}-v2.json'", "f'cache-small-{action}-audit-native{number}-v1.json'")
ast.parse(text)
target=here/'audit_full109_trace_cache_small_v1.py'
with target.open('x',encoding='utf-8',newline='\n') as stream:stream.write(text)
print('Derived complete current-row identity and custody audit; old failed attempts do not become qualified')
