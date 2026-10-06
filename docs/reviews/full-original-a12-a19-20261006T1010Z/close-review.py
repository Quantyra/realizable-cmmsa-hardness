import datetime, hashlib, json, pathlib, re

out=pathlib.Path(__file__).resolve().parent
repo=out.parents[2]
base=repo/'docs/a8-gcp/r1007'
capture=base/'captures/capture-integrated-59'
old=base/'captures/capture-integrated-56'
run=base/'runs/cmmsa_a8_output_20261006T095324Z_3ea31944'
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
manifest=json.loads((capture/'manifest.json').read_text(encoding='utf-8'))
prior=json.loads((old/'manifest.json').read_text(encoding='utf-8'))
packet=json.loads((out/'packet-manifest.json').read_text(encoding='utf-8'))
assert sha((out/'common-source-packet.txt').read_bytes())==packet['packet_sha256']
gate=json.loads((run/'full-original-a12-a19-native-gates.json').read_text(encoding='utf-8'))
assert gate['full_original_A12_A19_native_gates_green']
assert not gate['accepted'], 'Preserve pre-review gate: never backdate acceptance.'
reviews=[]
for lens in ['proof-adversarial','complexity-theory','non-claims-boundary']:
    raw=(out/(lens+'-stdout.json')).read_bytes()
    stderr=(out/(lens+'-stderr.txt')).read_bytes()
    terminal=json.loads((out/(lens+'-terminal.json')).read_text(encoding='utf-8'))
    command=json.loads((out/(lens+'-command.json')).read_text(encoding='utf-8'))
    report=json.loads(raw)
    assert terminal['exit_code']==0 and sha(raw)==terminal['stdout_sha256'].upper()
    assert sha(stderr)==terminal['stderr_sha256'].upper() and not stderr
    assert report['is_error'] is False and report['stop_reason']=='end_turn'
    assert report['result'].strip() and not report.get('permission_denials')
    assert command['common_packet_sha256']==packet['packet_sha256']
    assert len(report['modelUsage'])==1 and 'claude-opus-5-5[1m]' in report['modelUsage']
    usage=report['modelUsage']['claude-opus-5-5[1m]']
    assert usage['contextWindow']==1000000
    assert usage['inputTokens']+usage['cacheReadInputTokens']+usage['cacheCreationInputTokens']<usage['contextWindow']
    assert re.search(r'GO-WITH-NOTES\s*(?:\*\*)?\s*$',report['result'])
    (out/(lens+'-report.md')).write_text(report['result'].rstrip()+'\n',encoding='utf-8')
    reviews.append({'lens':lens,'verdict':'GO-WITH-NOTES','actual_model':'claude-opus-5-5[1m]','cli_session_id':report['session_id'],'exit_code':0,'stdout_sha256':sha(raw),'stderr_sha256':sha(stderr),'finished_utc':terminal['finished_utc'],'model_usage':usage,'report_sha256':sha((out/(lens+'-report.md')).read_bytes())})
assert len({r['cli_session_id'] for r in reviews})==3

# Disjoint coverage buckets: identities verified here, not retroactively presented
# as additional source text reviewed by the three original CLI invocations.
selected={x['path'] for x in packet['input_records'] if x['label']=='complete critical source'}
text=(out/'common-source-packet.txt').read_text(encoding='utf-8')
omitted={'lean/PvNP/RealizableHardness/'+p for p in re.findall(r'^- (\w+\.lean)$',text,re.M)}
assert len(selected)==94 and len(omitted)==64 and not selected&omitted
remaining=set(manifest['project_sources'])-selected-omitted
assert len(remaining)==59 and all(p in prior['project_sources'] for p in remaining)
def strip_block_comments(b):
    answer=bytearray();depth=0;i=0
    while i<len(b):
        if b[i:i+2]==b'/-':depth+=1;i+=2
        elif depth and b[i:i+2]==b'-/':depth-=1;i+=2
        elif depth:i+=1
        else:answer.append(b[i]);i+=1
    assert depth==0
    return bytes(answer)
identities=[]
successions=[]
for p,meta in sorted(manifest['project_sources'].items()):
    b=(capture/'inputs'/p).read_bytes();assert sha(b)==meta['sha256']
    bucket='complete text supplied (94)' if p in selected else ('omitted A16 umbrella closure (64)' if p in omitted else 'remaining frozen56 lineage build closure (59)')
    old_meta=prior['project_sources'].get(p)
    relation='new A12 milestone source' if old_meta is None else 'exact frozen56 identity'
    if old_meta and old_meta['sha256']!=meta['sha256']:
        old_bytes=(old/'inputs'/p).read_bytes()
        assert sha(old_bytes)==old_meta['sha256']
        a=strip_block_comments(old_bytes);c=strip_block_comments(b);assert a==c,p
        relation='comment-only successor; bytes outside nested block comments identical'
        successions.append({'path':p,'frozen56_sha256':old_meta['sha256'],'capture59_sha256':meta['sha256'],'outside_block_comment_bytes_sha256':sha(c),'outside_block_comment_bytes_equal':True})
    identities.append({'path':p,'capture59_sha256':meta['sha256'],'bytes':len(b),'coverage_bucket':bucket,'frozen56_relation':relation})
index={'prepared_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Root post-review identity/coverage custody; no extra independent source review claimed','reviewed_packet_sha256':packet['packet_sha256'],'reviewed_packet_index_limit':'217 project paths, with full-text hashes for94 supplied sources; complete capture217 hash map is added here after reviews','bucket_counts':{'complete':94,'omitted_a16':64,'remaining_frozen56':59},'sources':identities,'comment_only_successions':successions}
(out/'source-coverage-and-lineage.json').write_text(json.dumps(index,indent=2),encoding='utf-8')
record={'reviewed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'accepted':'ACCEPTED WITH NOTES AT FORMAL-STATEMENT LEVEL','scope':'manuscript_A12_actual and manuscript_A19_actual; A16 only as consumed by A19','source_sha256':manifest['project_sources']['lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A12InfluenceBound.lean']['sha256'],'checks_sha256':manifest['project_sources']['lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A12InfluenceBoundChecks.lean']['sha256'],'manifest_sha256':sha((capture/'manifest.json').read_bytes()),'packet_sha256':packet['packet_sha256'],'packet_bytes':packet['packet_bytes'],'reviews':reviews,'coverage_index_sha256':sha((out/'source-coverage-and-lineage.json').read_bytes()),'native_gate_sha256':sha((run/'full-original-a12-a19-native-gates.json').read_bytes()),'full_manuscript_certified':False,'helper_credit':0,'warning_debt_discharged':False,'required_notes_adopted':True}
(out/'review-verdicts.json').write_text(json.dumps(record,indent=2),encoding='utf-8')
print(json.dumps({k:v for k,v in record.items() if k!='reviews'},indent=2))
