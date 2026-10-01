import pathlib,subprocess,json,hashlib,sys
repo=pathlib.Path(__file__).resolve().parents[3]
out=pathlib.Path(__file__).resolve().parent
packet=(out/'gemini-source-packet.txt').read_text(encoding='utf-8')
args=[r'C:\Users\Dan\AppData\Local\agy\bin\agy.exe','--input-format','stream-json','--output-format','stream-json','--model','gemini-3.1-pro-high','--effort','high','--mode','plan','--sandbox','--print','Review the exact source packet supplied as a user message on stdin. No tools or commands. Return final report with separate3lens verdicts.']
message=json.dumps({'type':'user','message':{'role':'user','content':[{'type':'text','text':packet}]}},ensure_ascii=False)+'\n'
(out/'gemini-packet-command.json').write_text(json.dumps({'args':args,'cwd':str(repo),'inputFormat':'one NDJSON user/message/content text containing exact24sourcepacket'},indent=2))
with (out/'gemini-packet-stdout.ndjson').open('wb') as stdout,(out/'gemini-packet-stderr.txt').open('wb') as stderr:
    p=subprocess.Popen(args,cwd=repo,stdin=subprocess.PIPE,stdout=stdout,stderr=stderr)
    p.communicate(message.encode('utf-8'))
record={'exit_code':p.returncode,'stdout_sha256':hashlib.file_digest((out/'gemini-packet-stdout.ndjson').open('rb'),'sha256').hexdigest(),'stderr_sha256':hashlib.file_digest((out/'gemini-packet-stderr.txt').open('rb'),'sha256').hexdigest()}
(out/'gemini-packet-terminal.json').write_text(json.dumps(record,indent=2));print(json.dumps(record));sys.exit(p.returncode)
