"""Explicitly relocate inherited warning debt for proven comment-only line shifts."""
from pathlib import Path
from collections import Counter
import json,re,hashlib,difflib
here=Path(__file__).resolve().parent; package=here.parent; repo=package.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
seal=json.loads((package/'warning-baseline-seal.json').read_bytes())
assert all(sha((package/n).read_bytes())==h for n,h in seal['files'].items())
baseline=Counter()
for i in range(4):
    rows=Counter()
    for suffix in ['stdout','stderr']:
        for line in (package/'warning-baseline'/('stage-'+str(i)+'.'+suffix)).read_text(encoding='utf8').splitlines():
            if re.match(r'^(?:warning\s*:|[^\s].*:\d+:\d+:\s*warning\s*:)',line):
                rows[re.sub(r'/home/dfredriksen_quantyra_org/cmmsa_[^/]+/','<RUN>/',line)]+=1
    baseline|=rows
assert sum(baseline.values())==981
cap=package/'captures/capture-integrated-56'
manifest=json.loads((cap/'manifest.json').read_bytes())
changed=['ActualBinaryMatrixHC46A7Transfer.lean','ActualBinaryMatrixHC46A8AveragedTransport.lean','ActualBinaryMatrixHC46A8AveragedAssembly.lean','ActualBinaryMatrixHC46A11WeightedAggregate.lean']
maps={};pinrows={}
for short in changed:
    name='lean/PvNP/RealizableHardness/'+short
    before=(cap/'inputs'/name).read_bytes(); after=(repo/name).read_bytes()
    a=before.decode('utf8').splitlines();b=after.decode('utf8').splitlines();mapping={}
    for block in difflib.SequenceMatcher(a=a,b=b,autojunk=False).get_matching_blocks():
        for off in range(block.size):mapping[block.a+off+1]=block.b+off+1
    maps[name]=(mapping,a,b)
    pinrows[name]={'frozen56_sha256':sha(before),'current_comment_sha256':sha(after)}
current=Counter();relocations=[]
for header,count in baseline.items():
    replacement=header
    for name,(mapping,a,b) in maps.items():
        match=re.search(re.escape(name)+r':(\d+):(\d+):',header)
        if not match:continue
        oldline=int(match.group(1)); assert oldline in mapping
        newline=mapping[oldline]; assert a[oldline-1]==b[newline-1]
        replacement=header[:match.start(1)]+str(newline)+header[match.end(1):]
        relocations.append({'original_header':header,'current_header':replacement,'count':count,'original_line':oldline,'current_line':newline,'column':int(match.group(2)),'identical_source_line_sha256':sha(a[oldline-1].encode())})
    current[replacement]+=count
assert sum(current.values())==981 and len(current)==len(baseline)
receipt={'policy':'Frozen inherited debt retained; only explicit proven comment-line relocation. No new headers accepted, no suppression, no old receipt rewrite.','original_seal_sha256':sha((package/'warning-baseline-seal.json').read_bytes()),'frozen56_manifest_sha256':sha((cap/'manifest.json').read_bytes()),'original_union_headers':981,'current_union_headers':981,'baseline_headers':dict(current),'comment_source_identities':pinrows,'relocations':relocations,'frozen_config_identities':manifest['configs'],'accepted':False}
target=here/'current-warning-baseline.json'
with target.open('xb') as f:f.write(json.dumps(receipt,indent=2).encode())
print(json.dumps({'inherited_headers':981,'explicit_header_relocations':len(relocations),'new_owned_warning_allowance':0,'receipt_sha256':sha(target.read_bytes())}))
