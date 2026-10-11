"""Capture exact scalar-v6 and explicit-height-v1 offers, without native acceptance."""
import difflib
import hashlib
import json
from pathlib import Path
import re
import tarfile
from custody_checks import digest
from lean_source_static_preflight_v2 import inspect_bytes

HERE = Path(__file__).resolve().parent


def capture(folder, target_name, manifest_name, manifest_pin, prior_names, findings):
    source=HERE/folder; manifest=source/manifest_name
    assert digest(manifest)==manifest_pin
    offer=json.loads(manifest.read_bytes())
    pins=offer['files']
    if isinstance(pins,list): pins={r['path']:r for r in pins}
    prior=[]
    for name,index_pin,filename,source_pin in prior_names:
        root=HERE/name
        assert digest(root/'index.json')==index_pin and digest(root/filename)==source_pin
        old=json.loads((root/'index.json').read_bytes())
        for row in old['files']:
            assert digest(root/row['path'])==row['sha256'].upper()
        prior.append(dict(folder=name,index_sha256=index_pin,source=filename,source_sha256=source_pin))
    api_rows=[]
    if 'dependencies' in offer:
        archive=Path(offer['dependency_archive']['path'])
        assert digest(archive)==offer['dependency_archive']['sha256'].upper()
        with tarfile.open(archive,'r:gz') as tar:
            for row in offer['dependencies']:
                data=tar.extractfile(row['member']).read()
                assert len(data)==row['bytes'] and hashlib.sha256(data).hexdigest().upper()==row['sha256'].upper()
        for key in ('mathlib_api_source','mathlib_api_source_v6'):
            api=offer[key]; path=Path(api['path'])
            assert path.stat().st_size==api['bytes'] and digest(path)==api['sha256'].upper()
            with tarfile.open(path,'r:gz') as tar:
                members=api.get('members') or [dict(path=n) for n in api['read_only_inspected_members']]
                for member in members:
                    data=tar.extractfile(member['path']).read(); sha=hashlib.sha256(data).hexdigest().upper()
                    if 'sha256' in member: assert sha==member['sha256'].upper() and len(data)==member['bytes']
                    api_rows.append(dict(archive=str(path),member=member['path'],bytes=len(data),sha256=sha))
        assert all(api_rows[i]['sha256']==api_rows[i+2]['sha256'] for i in range(2))
    contents={}; rows=[]; lexical=[]
    for path in sorted(source.iterdir()):
        assert path.is_file()
        data=path.read_bytes(); assert not data.startswith(b'\xef\xbb\xbf')
        text=data.decode('utf-8'); sha=hashlib.sha256(data).hexdigest().upper()
        if path.name!=manifest_name:
            assert len(data)==pins[path.name]['bytes'] and sha==pins[path.name]['sha256'].upper()
        if path.suffix=='.lean':
            assert not re.search(r'\?(?!_)',text)
            lexical.append(inspect_bytes(data,path.name))
        contents[path.name]=data; rows.append(dict(path=path.name,bytes=len(data),sha256=sha))
    assert set(contents)==set(pins)|{manifest_name}
    target=HERE/target_name; target.mkdir(exist_ok=False)
    (target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    for name,data in contents.items():
        (target/name).open('xb').write(data); assert (target/name).read_bytes()==(source/name).read_bytes()
    (target/'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
    value=dict(original_directory=str(source),files=rows,prior_captures=prior,lexical_preflight=lexical,
        independently_verified_mathlib_members=api_rows,root_static_findings=findings,
        full_source_review='complete height source or prior full scalar source plus complete v6 diff',
        complete_argument_map_read=True,immutable_capture=True,development_candidate=True,
        compiler_invoked=False,native_verified=False,accepted=False,full_goal_complete=False)
    if 'ActualNumericNoScalar.lean' in contents:
        value['complete_source_diff']=''.join(difflib.unified_diff(
            (HERE/'numeric-scalar-offer-capture-v5/ActualNumericNoScalar.lean').read_text(encoding='utf-8').splitlines(True),
            contents['ActualNumericNoScalar.lean'].decode().splitlines(True),fromfile='v5',tofile='v6'))
    (target/'index.json').open('x').write(json.dumps(value,indent=2)+'\n')
    print(json.dumps(dict(folder=str(target),exact_files=len(rows),index_sha256=digest(target/'index.json'),native_verified=False)),flush=True)


def main():
    scalar=('numeric-scalar-offer-capture-v5','3026BCA76A941ED298733F3CCBC2AEDDA3C28BF196B977A7E9D3E0AF93C10701','ActualNumericNoScalar.lean','8AE08AC67F689AA7A5CD5CFB91C42EDF735D73D5BAE7CB194E24B4624129DE43')
    height=('numeric-source-height-offer-capture-v3','7CD8C1D6463A39ECDE018F278360847F6874C3F8A2A3CB57FFC2D687B025C96D','ActualNumericSourceHeight.lean','98661E33A9C272CB983368B60C12BF7AA7BE833076A5545CAB1CDF4917209BDF')
    capture('actual-numeric-no-scalar-candidate-v6','numeric-scalar-offer-capture-v6','OFFER-MANIFEST.json',
        'FDFFF8028BB33B3384DC7FB9FDA1960D6B2657854F0A6FBDBDDDC034188088B6',[scalar],
        ['Exact rpow strict-positivity and product-association repairs inspected; other translation defects may remain.'])
    capture('actual-numeric-explicit-height-candidate-v1','numeric-explicit-height-offer-capture-v1','manifest.json',
        '5FF3A143746721A5F212760E6604BB87A74C4AE25F0CA624AFDE80AF7AB79B91',[height,scalar],
        ['The eventual theorem and hcuts put theorem proof terms numericK_rounding and numeric_scalar_cutoffs in And proposition positions; replace by their actual proposition statements.',
         'hfour uses m*4 <= m*T as exact evidence for 4*m <= m*T without commutation.',
         'hAbs hhR composes only the outer max inequality; it still needs the inner r+7 <= max(r+7,Hfinal) step.',
         'hlarge hmulN applies hmReal (256 <= m), producing 256*N <= m*N while declaring N <= m*N; derive 1 <= m first.',
         'Static rejection pending separate repair and GCP diagnostics; original mathematical argument remains assessed, not kernel verified.'])


if __name__ == '__main__': main()
