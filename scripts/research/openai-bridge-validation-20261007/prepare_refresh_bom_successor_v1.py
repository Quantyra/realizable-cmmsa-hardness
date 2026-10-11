"""Source-only exact three-byte encoding repair, preserving immutable original."""
import hashlib,json
from pathlib import Path
H=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest().upper()
def main():
 s=H/'numeric-refresh-formal-capture-v1/ExactRefresh.lean';raw=s.read_bytes()
 assert sha(raw)=='B68497790D514D4941E70E68F9AEF4D10493C572C9039058EB347C3963CD2BF3'
 bom=bytes.fromhex('efbbbf');assert raw.startswith(bom);fixed=raw[len(bom):]
 fixed.decode('utf-8');assert not fixed.startswith(bom);assert bom+fixed==raw
 d=H/'numeric-refresh-formal-encoding-successor-v1';d.mkdir(exist_ok=False)
 (d/'.gitattributes').write_bytes(b'* -text\n');p=d/'ExactRefresh.lean';p.write_bytes(fixed);assert p.read_bytes()==fixed
 (d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
 index=dict(original_source=str(s),original_sha256=sha(raw),original_capture_index_sha256=sha((s.parent/'index.json').read_bytes()),files=[dict(path=p.name,bytes=len(fixed),sha256=sha(fixed))],transformation='Remove exactly initial UTF-8 BOM EF BB BF; every remaining source byte unchanged.',inverse_reconstruction_verified=True,canonical_module_destination='PvNP.RealizableHardness.NumericRefreshFormalOffer',compiler_invoked=False,cloud_operation=False,accepted=False,immutable_capture=True,observations=['Source-only preparation following preserved inventory V7 lexical failure. Original author source/capture and candidate dependency pins remain unchanged. Accepted operator successor rebind remains required before execution.'])
 (d/'index.json').write_text(json.dumps(index,indent=2)+'\n',encoding='utf-8');print(json.dumps(dict(index_sha256=sha((d/'index.json').read_bytes()),source_sha256=sha(fixed))))
if __name__=='__main__':main()
