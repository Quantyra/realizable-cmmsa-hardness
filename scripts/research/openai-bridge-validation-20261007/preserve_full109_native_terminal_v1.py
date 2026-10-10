import hashlib
import json
from pathlib import Path
from full109_builder02_controller import ROOT
from custody_checks import verify_local_custody
here=Path(__file__).parent
marker=json.loads((ROOT/'launch-once.json').read_bytes());check=Path(marker['preflight'])
terminal=json.loads((check/'terminal-custody.json').read_bytes());custody=terminal['custody']
assert terminal['run']==marker['run'] and terminal['terminal']['native_terminal']
assert terminal['terminal']['compile_green'] and len(terminal['terminal']['stages'])==7
verify_local_custody(custody['short_path'],custody['repository_path'],custody['remote_sha256'],custody['bytes'])
assert all(c['native_exit']==0 for c in json.loads((check/'commands.json').read_bytes()))
target=here/'full109-native-terminal-record-v1';target.mkdir(exist_ok=False)
(target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
paths=[check/'commands.json',check/'terminal-custody.json',Path(custody['repository_path'])]
paths+=sorted((check/'control').glob('*'))
rows=[]
for i,path in enumerate(paths):
 dest=target/f'{i:03d}-{path.name}';data=path.read_bytes();dest.open('xb').write(data)
 rows.append(dict(source=str(path),target=dest.name,bytes=len(data),sha256=hashlib.sha256(data).hexdigest().upper()))
(target/'index.json').write_text(json.dumps(dict(records=rows,run=marker['run'],
 original_tool_handle=70186,tool_native_exit=0,two_copy_custody_verified=True,
 qualification_pending=True,accepted=False),indent=2)+'\n')
print(json.dumps(dict(files=len(rows),archive_sha256=custody['remote_sha256'],archive_bytes=custody['bytes'])))
