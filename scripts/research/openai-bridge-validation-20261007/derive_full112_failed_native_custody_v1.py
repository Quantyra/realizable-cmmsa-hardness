"""Derive complete Full112 failed-native custody from the preserved Full111 control."""
import ast,json,subprocess
from pathlib import Path
from custody_checks import digest
HERE=Path(__file__).resolve().parent
REPO=HERE.parents[2]
PREFIX=HERE.relative_to(REPO).as_posix()+'/'
def main():
    parent=HERE/'preserve_full111_failed_native_v1.py'
    raw=parent.read_bytes()
    assert raw==subprocess.check_output(['git','cat-file','blob','099b2ee5:'+PREFIX+parent.name],cwd=REPO)
    text=raw.decode('utf-8')
    changes=[
        ('full111','full112'),
        ("('20261011T035530486815Z-56b79f751c14', 60064, 1)","('20261011T051302333252Z-b320c73bc980', 78875, 1)"),
        ("('20261011T040646428071Z-4b510d9eb357', 28272, 0)","('20261011T052209447813Z-6b27632b3aa8', 96042, 0)"),
        ("('20261011T041028768897Z-7f57c25d74f1', 23769, 1)","('20261011T052514074529Z-3dd1e6748b01', 97233, 1)"),
        ('cmmsa_a8_output_20261011T035621Z_498f7ba6','cmmsa_a8_output_20261011T051406Z_3ef6ddc2'),
        ('29A942FBF1594E1C09EC34ECE58DB02F1742E8B9FDCDA0E88B3084E3F4B7F192','0392E798A4234ADC4386703FDB1817217D99DFBEA7FF48D4184E614AA42FD6B2'),
        ("native['owned_error_headers'] == 8","native['owned_error_headers'] == 9"),
        ("native['owned_warning_headers'] == [0, 0, 0, 0, 9, 0, 0]","native['owned_warning_headers'] == [0, 0, 0, 0, 3, 0, 0]"),
        ("native['missing_objects'] == 31","native['missing_objects'] == 30"),
        ('if handle == 23769:','if handle == 97233:'),
        ("    total = sum(p.stat().st_size for p in paths)","    for observation in (ROOT/'live-native-inspections-v1').iterdir():\n        assert (observation/'inspection.json').is_file()\n        for record in json.loads((observation/'transport/commands.json').read_bytes()):\n            assert record['native_exit'] == 0\n            for stream in ('stdout','stderr'):\n                assert digest(Path(record[stream+'_path'])) == record[stream+'_sha256']\n        paths.update(p for p in observation.rglob('*') if p.is_file())\n    total = sum(p.stat().st_size for p in paths)"),
        ('original_handles=dict(native=60064, stop=28272, audit=23769)','original_handles=dict(native=78875, stop=96042, audit=97233)'),
        ("'a1cecd13:full112-native-progress-record-v1'","'597cf9f3:full112-native-progress-record-v1; all three full original observations are included here'"),
        ("'adf1e917:full112-native-diagnostic-packet-v2'","'099b2ee5:full112-native-diagnostic-packet-v1'"),
    ]
    records=[]
    for old,new in changes:
        count=text.count(old);assert count>0,old;text=text.replace(old,new)
        records.append(dict(old=old,new=new,occurrences=count))
    ast.parse(text)
    target=HERE/'preserve_full112_failed_native_v1.py';target.open('x',encoding='utf-8',newline='\n').write(text)
    report=dict(parent=parent.name,parent_commit='099b2ee5',parent_sha256=digest(parent),target=target.name,target_sha256=digest(target),
        exact_replacements=records,original_native_and_audit_failures_retained=True,cloud_action_performed=False,compiler_invoked=False)
    (HERE/'full112-failed-native-custody-derivation-v1.json').open('x').write(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(target=target.name,sha256=digest(target))),flush=True)
if __name__=='__main__':main()

