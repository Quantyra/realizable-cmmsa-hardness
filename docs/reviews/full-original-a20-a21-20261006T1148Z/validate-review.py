import pathlib,json,hashlib,re,datetime
out=pathlib.Path(__file__).resolve().parent
repo=out.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
pkt=json.loads((out/'packet-manifest.json').read_text())
b=(out/'common-source-packet.txt').read_bytes();assert sha(b)==pkt['packet_sha256']
cap=repo/'docs/a8-gcp/r1007/captures/capture-integrated-64'
old=repo/'docs/a8-gcp/r1007/captures/capture-integrated-59'
m=json.loads((cap/'manifest.json').read_text());prior=json.loads((old/'manifest.json').read_text())
run=repo/'docs/a8-gcp/r1007/runs'/pkt['run']
g=json.loads((run/'full-original-a20-a21-native-gates.json').read_text())
assert g['full_original_A20_A21_native_gates_green'] and not g['accepted']
assert json.loads((run/'independent-termination/control/000.stdout').read_text())['status']=='TERMINATED'
reviews=[]
for lens in ['proof-adversarial','complexity-theory','non-claims-boundary']:
 raw=(out/(lens+'-stdout.json')).read_bytes();err=(out/(lens+'-stderr.txt')).read_bytes()
 t=json.loads((out/(lens+'-terminal.json')).read_text());c=json.loads((out/(lens+'-command.json')).read_text());p=json.loads((out/(lens+'-process.json')).read_text());r=json.loads(raw)
 assert t['exit_code']==0 and sha(raw)==t['stdout_sha256'].upper() and sha(err)==t['stderr_sha256'].upper()
 assert not err and r['is_error'] is False and r['stop_reason']=='end_turn' and not r.get('permission_denials')
 assert r['result'].strip() and c['common_packet_sha256']==pkt['packet_sha256']
 inp=('REQUESTED LENS: '+lens+' ONLY. Separate top-level review; do not combine other lens verdicts.\n').encode()+b
 assert hashlib.sha256(inp).hexdigest()==c['input_sha256']
 assert len(r['modelUsage'])==1 and 'claude-opus-5-5[1m]' in r['modelUsage']
 u=r['modelUsage']['claude-opus-5-5[1m]'];ni=u['inputTokens']+u['cacheReadInputTokens']+u['cacheCreationInputTokens']
 assert u['contextWindow']==1000000 and ni+u['outputTokens']<=u['contextWindow']
 v=re.search(r'\b(GO-WITH-NOTES|NO-GO|INCOMPLETE|GO)\b(?:\s|\*)*$',r['result']);assert v,lens
 report=out/(lens+'-report.md');report.write_text(r['result'].rstrip()+'\n',encoding='utf-8')
 reviews.append({'lens':lens,'verdict':v.group(1),'actual_model':'claude-opus-5-5[1m]','cli_session_id':r['session_id'],'cli_pid':p['pid'],'exit_code':0,'stdout_sha256':sha(raw),'stderr_sha256':sha(err),'finished_utc':t['finished_utc'],'model_usage':u,'actual_total_input_tokens':ni,'input_plus_output_tokens':ni+u['outputTokens'],'report_sha256':sha(report.read_bytes())})
assert len({r['cli_session_id'] for r in reviews})==3 and len({r['cli_pid'] for r in reviews})==3
selected={r['path'] for r in pkt['input_records'] if r['label']=='complete critical source'};assert len(selected)==128
text=b.decode('utf-8');idx=[]
for p,v in sorted(m['project_sources'].items()):
 src=(cap/'inputs'/p).read_bytes();assert sha(src)==v['sha256']
 line=p+' SHA256 '+v['sha256']+' BYTES '+str(v['bytes'])+' '+('COMPLETE-BODY' if p in selected else 'EXCLUDED-BODY');assert line in text
 om=prior['project_sources'].get(p)
 relation='new A20/A21 source/Checks' if om is None else 'exact capture59 identity; earlier review coverage is NOT inferred'
 if om:assert om['sha256']==v['sha256'],p
 idx.append({'path':p,'sha256':v['sha256'],'bytes':v['bytes'],'complete_text_supplied':p in selected,'explicit_current_hash_printed_in_actual_packet':True,'capture59_relation':relation})
index={'scope':'Root identity custody and actual packet coverage; no additional independent review implied','packet_sha256':pkt['packet_sha256'],'complete_sources':128,'excluded_bodies':93,'indexed_current_hashes':221,'sources':idx}
(out/'source-coverage-and-lineage.json').write_text(json.dumps(index,indent=2)+'\n',encoding='utf-8')
rec={'reviewed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Original A20/A21 plus complete critical A17/A18 path as consumed; prior accepted A7/A12/A19 reused within actual scope','reviews':reviews,'all_three_provider_reports_validated':True,'all_three_go_or_notes':all(r['verdict'] in ['GO','GO-WITH-NOTES'] for r in reviews),'packet_sha256':pkt['packet_sha256'],'packet_bytes':pkt['packet_bytes'],'manifest_sha256':sha((cap/'manifest.json').read_bytes()),'coverage_index_sha256':sha((out/'source-coverage-and-lineage.json').read_bytes()),'native_gate_sha256':sha((run/'full-original-a20-a21-native-gates.json').read_bytes()),'accepted':False,'required_notes_adopted':False,'full_manuscript_certified':False,'warning_debt_discharged':False,'helper_credit':0}
(out/'review-validation.json').write_text(json.dumps(rec,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'all_three_go_or_notes':rec['all_three_go_or_notes'],'reviews':[{k:r[k] for k in ['lens','verdict','actual_model','cli_session_id','actual_total_input_tokens','input_plus_output_tokens','stdout_sha256']} for r in reviews],'accepted':False},indent=2))