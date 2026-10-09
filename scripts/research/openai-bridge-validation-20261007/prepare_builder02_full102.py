"""Freeze full340/full251 warning-only successor; no local Lean or cloud operation."""
import copy
import io
import json
import tarfile
from pathlib import Path
from custody_checks import digest, verify_local_custody
from prepare_builder02_full90 import capsule
from prepare_builder02_full101 import OUTPUT as PARENT, REQUESTS
from prepare_full101_warning_repair import ROOT as REPAIRS

OUTPUT = PARENT.parent / 'full102-spectral-owned-warning-repair-resource02'
HERE = Path(__file__).parent


def validate_expansion(old, new):
    repair=json.loads((REPAIRS/'derivation.json').read_bytes())
    rows=repair['files'];assert len(rows)==8
    assert set(old)==set(new)
    changed={r['path'] for r in rows}
    assert {p for p in old if old[p]!=new[p]}==changed|{'capture-manifest.json'}
    a=json.loads(old['capture-manifest.json']);b=json.loads(new['capture-manifest.json'])
    assert len(b['project_sources'])==340 and len(b['requested_axioms'])==251 and len(b['stages'])==7
    normal=copy.deepcopy(b)
    for row in rows:
        rel=row['path'];p=REPAIRS/Path(rel).name
        assert digest(p)==row['sha256'] and row['all_declaration_headers_preserved']
        assert row['no_linter_disable_added'] and new[rel]==p.read_bytes()
        assert a['project_sources'][rel]['sha256']==row['original_sha256']
        assert b['project_sources'][rel]==dict(sha256=row['sha256'],bytes=row['bytes'])
        normal['project_sources'][rel]=a['project_sources'][rel]
    assert normal==a,'Only eight proof source pins may change'
    return True


def main():
    from full101_capture_gates import validate_successor
    validate_successor()
    marker=json.loads((PARENT/'launch-once.json').read_bytes());check=Path(marker['preflight'])
    terminal=json.loads((check/'terminal-custody.json').read_bytes());c=terminal['custody']
    verify_local_custody(c['short_path'],c['repository_path'],c['remote_sha256'],c['bytes'])
    stop=json.loads((check/'vm-termination.json').read_bytes())
    assert stop['run']==marker['run']==terminal['run'] and terminal['terminal']['compile_green']
    assert stop['independent']['status']=='TERMINATED' and str(stop['independent']['id'])=='7237681467779354904'
    q=check/'qualified-native'/marker['run']/'material-expanded-native-report.json'
    report=json.loads(q.read_bytes())
    assert not report['full101_expanded_native_gates_green']
    assert report['owned_warning_headers']==[0,0,0,0,26,26,0]
    assert report['inherited_regression_headers']==[0]*7 and report['bad_profiles']==report['missing_objects']==0
    old=capsule(PARENT/'input-archive.tar.gz');new=dict(old)
    manifest=json.loads(old['capture-manifest.json']);repairs=json.loads((REPAIRS/'derivation.json').read_bytes())
    for row in repairs['files']:
        rel=row['path'];new[rel]=(REPAIRS/Path(rel).name).read_bytes()
        manifest['project_sources'][rel]=dict(sha256=row['sha256'],bytes=row['bytes'])
    new['capture-manifest.json']=(json.dumps(manifest,indent=2)+'\n').encode()
    validate_expansion(old,new)
    OUTPUT.mkdir()
    with tarfile.open(OUTPUT/'input-archive.tar.gz','x:gz') as archive:
        for name,data in sorted(new.items()):
            m=tarfile.TarInfo(name);m.size=len(data);m.mode=0o644
            archive.addfile(m,io.BytesIO(data))
    (OUTPUT/'capture-manifest.json').write_bytes(new['capture-manifest.json'])
    expansion=json.loads((PARENT/'source-expansion.json').read_bytes())
    expansion.update(schema='full102-full340-full251-owned-warning-repair-v1',parent_run=marker['run'],
                     parent_custody=c,parent_qualified_report_sha256=digest(q),
                     parent_qualified_green=False,parent_warning_hold_retained=True,
                     repaired_sources=repairs['files'],repair_derivation_sha256=digest(REPAIRS/'derivation.json'),
                     parent_capture_sources=340,parent_capture_profiles=251,added_sources=[],additional_profiles=[],
                     all340_source_paths_and251_profiles_and7_stage_commands_preserved=True,
                     all332_other_source_bytes_preserved=True,compiler_invoked=False,native_verification_pending=True,
                     launch_clearance=False,accepted=False)
    (OUTPUT/'source-expansion.json').write_bytes((json.dumps(expansion,indent=2)+'\n').encode())
    binding=json.loads((PARENT/'resource-binding.json').read_bytes())
    binding.update(parent_resource_binding_sha256=digest(PARENT/'resource-binding.json'),parent_run=marker['run'],
                   source_expansion_sha256=digest(OUTPUT/'source-expansion.json'),
                   changed_files=[r['path'] for r in repairs['files']]+['capture-manifest.json'],added_files=[],
                   files={name:digest(OUTPUT/name) for name in ['input-archive.tar.gz','capture-manifest.json']})
    (OUTPUT/'resource-binding.json').write_bytes((json.dumps(binding,indent=2)+'\n').encode())
    assert capsule(OUTPUT/'input-archive.tar.gz')==new
    print(json.dumps(dict(root=str(OUTPUT),sources=340,profiles=251,input_sha256=digest(OUTPUT/'input-archive.tar.gz'),manifest_sha256=digest(OUTPUT/'capture-manifest.json'),launch_clearance=False)))


if __name__=='__main__':main()
