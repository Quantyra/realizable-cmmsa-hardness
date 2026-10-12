from pathlib import Path
import json,hashlib,re
H=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
def main():
 s=H/'tm2-cobham-transfer-offer-20261012-v3';raw=(s/'manifest.json').read_bytes();assert sha(raw)=='9135815A73B2E72BC73763DA05091402C221334C804E7B27FD06F3F1179DB4B6';m=json.loads(raw);data={'manifest.json':raw}
 for n,r in m['files'].items():
  b=(s/n).read_bytes();assert sha(b)==r['sha256'] and len(b)==r['bytes'];b.decode('utf8');assert not b.startswith(bytes.fromhex('efbbbf'));assert not re.search(rb'\\u[0-9a-fA-F]{4}',b) if n.endswith('.lean') else True;data[n]=b
 deps={}
 for module in ['OAI.Computability.UniqueGames.Model','OAI.Computability.UniqueGames.Machines.Runtime']:
  p=H/'joint-codec-environment-source-plan-v1/upstream-sources'/Path(module.replace('.','/')+'.lean');b=p.read_bytes();assert sha(b)==m['source_inputs'][module];name='dependency.'+module.rsplit('.',1)[-1]+'.source';data[name]=b;deps[module]=dict(sha256=sha(b),verified=True)
 d=H/'tm2-cobham-transfer-capture-20261012-v3';d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n');rows=[]
 for n,b in data.items():(d/n).write_bytes(b);rows.append(dict(path=n,bytes=len(b),sha256=sha(b)))
 (d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes());j=dict(files=rows,manifest_sha256=sha(raw),dependencies=deps,local_complexity_TM_snapshot_verification_pending=True,prior_unhashed_v2_handoff_not_treated_as_custody=True,latest_explicit_hash_offer_verified=True,sentinel_layout_mismatch_requires_distinct_successor=True,superseded_v1_offer_uncaptured=True,compiler_invoked=False,accepted=False,axiom_requests=data['Checks.lean'].count(b'#print axioms '),literal_ascii_unicode_escapes_found=False)
 (d/'index.json').write_text(json.dumps(j,indent=2)+'\n',encoding='utf8');print(json.dumps(dict(index_sha256=sha((d/'index.json').read_bytes()),axiom_requests=j['axiom_requests'])))
if __name__=='__main__':main()
