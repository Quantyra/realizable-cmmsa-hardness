"""Preserve the report's one mistyped member hash and check its actual archive bytes."""
import ast
import importlib.util
import json
from pathlib import Path
from custody_checks import digest

HERE=Path(__file__).resolve().parent


def main():
    source=HERE/'capture_numeric_height_v2_and_static_review_v1.py';text=source.read_text(encoding='utf-8')
    old="            assert hashlib.sha256(data).hexdigest().upper()==row['sha256'].upper()"
    new="            actual=hashlib.sha256(data).hexdigest().upper()\n            if actual!=row['sha256'].upper():\n                assert name=='GrassmannCounting.lean'\n                assert row['sha256']=='E572157EA4B6C3245FA02C09162B4B00359A89CF08314D8BFD9D9E2FE84D73F'\n                assert actual=='E572157EA4B6C3245FA02C09162B4B00359A89CF08314D8BFDF9D9E2FE84D73F'\n                CORRECTIONS.append(dict(member=row['archive_member'],reported=row['sha256'],actual=actual,bytes=len(data)))"
    assert text.count(old)==2;text=text.replace(old,new,1)
    text=text.replace('HERE=Path(__file__).resolve().parent','HERE=Path(__file__).resolve().parent\nCORRECTIONS=[]')
    old='all_reported_source_archive_and_member_hashes_verified=True,'
    new='all_reported_source_archive_and_member_hashes_verified=False,exactly_one_reported_member_hash_typo=CORRECTIONS,all_other_reported_hashes_verified=True,'
    assert text.count(old)==1;text=text.replace(old,new)
    ast.parse(text)
    target=HERE/'capture_numeric_height_v2_and_static_review_v2.py';target.open('xb').write(text.encode())
    (HERE/'numeric-height-static-capture-reconciliation-v2.json').open('x').write(json.dumps(dict(
        original_control=source.name,original_control_sha256=digest(source),original_tool_chunk='510fb2',original_exit=1,
        original_diagnostic='AssertionError on reported GrassmannCounting member hash',
        failed_before_any_capture_folder_creation=True,raw_tool_stream_archive_claimed=False,
        original_report_preserved_unchanged=True,successor=target.name,successor_sha256=digest(target),
        compiler_invoked=False,native_verified=False),indent=2)+'\n')
    spec=importlib.util.spec_from_file_location('capture_successor',target);module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module);module.main()
    assert len(module.CORRECTIONS)==1


if __name__=='__main__':main()
