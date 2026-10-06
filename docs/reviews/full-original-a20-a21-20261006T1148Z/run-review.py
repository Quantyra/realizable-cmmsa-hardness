import pathlib,subprocess,json,sys,hashlib,datetime
out=pathlib.Path(__file__).resolve().parent
repo=out.parents[2]
lens=sys.argv[1]
assert lens in ['proof-adversarial','complexity-theory','non-claims-boundary']
assert not (out/(lens+'-command.json')).exists(), 'Existing invocation: recover same handle; do not restart.'
manifest=json.loads((out/'packet-manifest.json').read_text(encoding='utf-8'))
raw=(out/'common-source-packet.txt').read_bytes()
assert hashlib.sha256(raw).hexdigest().upper()==manifest['packet_sha256']
run=repo/'docs/a8-gcp/r1007/runs'/manifest['run']
gate=json.loads((run/'full-original-a20-a21-native-gates.json').read_text(encoding='utf-8'))
assert gate['full_original_A20_A21_native_gates_green'] is True
assert json.loads((run/'independent-termination/control/000.stdout').read_text(encoding='utf-8'))['status']=='TERMINATED'
packet=('REQUESTED LENS: '+lens+' ONLY. Separate top-level review; do not combine other lens verdicts.\n').encode()+raw
args=[r'C:\Users\Dan\.local\bin\claude.exe','-p','--model','opus[1m]','--effort','high','--permission-mode','plan','--tools','','--output-format','json']
record={'args':args,'cwd':str(repo),'lens':lens,'scope':'Full original A20/A21 and complete critical A17/A18 consumer path; frozen64; no tools/edits/compile/cloud/delegation','common_packet_sha256':manifest['packet_sha256'],'input_sha256':hashlib.sha256(packet).hexdigest(),'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
(out/(lens+'-command.json')).write_text(json.dumps(record,indent=2),encoding='utf-8')
stdout=out/(lens+'-stdout.json');stderr=out/(lens+'-stderr.txt')
with stdout.open('wb') as so,stderr.open('wb') as se:
    p=subprocess.Popen(args,cwd=repo,stdin=subprocess.PIPE,stdout=so,stderr=se)
    (out/(lens+'-process.json')).write_text(json.dumps({'pid':p.pid,'started_utc':record['started_utc']},indent=2),encoding='utf-8')
    p.communicate(packet)
record={'exit_code':p.returncode,'stdout_sha256':hashlib.sha256(stdout.read_bytes()).hexdigest(),'stderr_sha256':hashlib.sha256(stderr.read_bytes()).hexdigest(),'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
(out/(lens+'-terminal.json')).write_text(json.dumps(record,indent=2),encoding='utf-8')
print(json.dumps(record));sys.exit(p.returncode)
