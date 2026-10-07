import pathlib,subprocess,json,sys,hashlib
repo=pathlib.Path(__file__).resolve().parents[3]
out=pathlib.Path(__file__).resolve().parent
kind=sys.argv[1]
assert kind in ['claude','gemini']
packet=(out/'review-packet.txt').read_text(encoding='utf-8')
if kind=='claude':
 args=[r'C:\Users\Dan\.local\bin\claude.exe','-p','--model','opus[1m]','--effort','high','--permission-mode','plan','--tools','','--output-format','json']
 message=packet.encode('utf-8')
else:
 args=[r'C:\Users\Dan\AppData\Local\agy\bin\agy.exe','--input-format','stream-json','--output-format','stream-json','--model','gemini-3.1-pro-high','--effort','high','--mode','plan','--sandbox','--print=']
 message=(json.dumps({'event':'user','message':{'role':'user','content':[{'type':'text','text':packet}]}},ensure_ascii=False)+'\n').encode('utf-8')
(out/(kind+'-command.json')).write_text(json.dumps({'args':args,'cwd':str(repo),'scope':'Pinned counting ingredient, all three lenses; provided source packet only; no writes/compiler/cloud/delegation'},indent=2))
stdout=out/(kind+'-stdout.txt');stderr=out/(kind+'-stderr.txt')
with stdout.open('wb') as so,stderr.open('wb') as se:
 p=subprocess.Popen(args,cwd=repo,stdin=subprocess.PIPE,stdout=so,stderr=se);p.communicate(message)
record={'exit_code':p.returncode,'stdout_sha256':hashlib.file_digest(stdout.open('rb'),'sha256').hexdigest(),'stderr_sha256':hashlib.file_digest(stderr.open('rb'),'sha256').hexdigest()}
(out/(kind+'-terminal.json')).write_text(json.dumps(record,indent=2));print(json.dumps(record));sys.exit(p.returncode)
