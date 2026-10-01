import pathlib,subprocess,json,sys,hashlib,time
repo=pathlib.Path(__file__).resolve().parents[3]
out=pathlib.Path(__file__).resolve().parent
kind=sys.argv[1]
prompt=(out/'review-prompt.txt').read_text(encoding='utf-8')
if kind=='claude':
    args=[r'C:\Users\Dan\.local\bin\claude.exe','-p','--model','opus[1m]','--effort','high','--permission-mode','plan','--tools','Read,Glob,Grep','--output-format','json',prompt]
else:
    args=[r'C:\Users\Dan\AppData\Local\agy\bin\agy.exe','--print',prompt,'--model','gemini-3.1-pro-high','--effort','high','--mode','plan','--sandbox','--output-format','json']
(out/(kind+'-command.json')).write_text(json.dumps({'args':args,'cwd':str(repo),'claim':'Actual headless final conditional-core review; no compiler/source edits authorized.'},indent=2),encoding='utf-8')
with (out/(kind+'-stdout.json')).open('wb') as stdout,(out/(kind+'-stderr.txt')).open('wb') as stderr:
    process=subprocess.Popen(args,cwd=repo,stdout=stdout,stderr=stderr)
    code=process.wait()
record={'exit_code':code,'stdout_sha256':hashlib.file_digest((out/(kind+'-stdout.json')).open('rb'),'sha256').hexdigest(),'stderr_sha256':hashlib.file_digest((out/(kind+'-stderr.txt')).open('rb'),'sha256').hexdigest()}
(out/(kind+'-terminal.json')).write_text(json.dumps(record,indent=2),encoding='utf-8')
print(json.dumps(record));sys.exit(code)
