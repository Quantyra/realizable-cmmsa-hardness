import pathlib,subprocess,json,sys,hashlib,datetime
out=pathlib.Path(__file__).resolve().parent
repo=out.parents[2]
lens=sys.argv[1]
assert lens in ['proof-adversarial','complexity-theory','non-claims-boundary']
packet='REQUESTED LENS: '+lens+' ONLY. This must be a separate top-level review; do not combine verdicts for other lenses.\n'+(out/'common-source-packet.txt').read_text(encoding='utf-8')
args=[r'C:\Users\Dan\.local\bin\claude.exe','-p','--model','opus[1m]','--effort','high','--permission-mode','plan','--tools','','--output-format','json']
record={'args':args,'cwd':str(repo),'lens':lens,'scope':'Full original A8 milestone; frozen46 packet; no tools/edits/compile/cloud/delegation','input_sha256':hashlib.sha256(packet.encode()).hexdigest(),'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
(out/(lens+'-command.json')).write_text(json.dumps(record,indent=2),encoding='utf-8')
stdout=out/(lens+'-stdout.json');stderr=out/(lens+'-stderr.txt')
with stdout.open('wb') as so,stderr.open('wb') as se:
 p=subprocess.Popen(args,cwd=repo,stdin=subprocess.PIPE,stdout=so,stderr=se);p.communicate(packet.encode('utf-8'))
record={'exit_code':p.returncode,'stdout_sha256':hashlib.sha256(stdout.read_bytes()).hexdigest(),'stderr_sha256':hashlib.sha256(stderr.read_bytes()).hexdigest(),'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
(out/(lens+'-terminal.json')).write_text(json.dumps(record,indent=2),encoding='utf-8');print(json.dumps(record));sys.exit(p.returncode)
