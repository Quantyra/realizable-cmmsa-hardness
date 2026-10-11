"""Select only launched native resources and preserve the earlier pre-compression failure."""
import ast,json
from pathlib import Path
from custody_checks import digest
HERE=Path(__file__).resolve().parent
def main():
    parent=HERE/'compress_full112_settled_native_metadata_v3.py'
    assert not (HERE/'full112-settled-native-metadata-lossless-v3').exists()
    text=parent.read_text(encoding='utf-8')
    changes=[
        ("resource,=BASE.glob('full'+str(n)+'-*')","resource,=[p for p in BASE.glob('full'+str(n)+'-*') if p.is_dir() and (p/'launch-once.json').is_file()]"),
        ("'full112-settled-native-metadata-lossless-v3'","'full112-settled-native-metadata-lossless-v4'"),
    ]
    for old,new in changes:
        assert text.count(old)==1;text=text.replace(old,new)
    ast.parse(text)
    target=HERE/'compress_full112_settled_native_metadata_v4.py'
    target.open('x',encoding='utf-8',newline='\n').write(text)
    record=dict(original_tool_chunk='94b4b7',original_exit=1,original_failure='Two Full84 directories; the unlaunched original and launched warning-clean successor. No compression or destination creation occurred.',
        original_tool_streams_not_claimed_archived=True,parent_sha256=digest(parent),target_sha256=digest(target),
        exact_replacements=[dict(old=a,new=b) for a,b in changes])
    (HERE/'full112-native-metadata-compression-reconciliation-v4.json').open('x').write(json.dumps(record,indent=2)+'\n')
    print(json.dumps(dict(target=target.name,sha256=digest(target))),flush=True)
if __name__=='__main__':main()

