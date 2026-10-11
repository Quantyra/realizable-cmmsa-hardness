"""Preserve the uncompiled offer and verify its actual Full113 dependencies."""
import hashlib,json,re,tarfile
from pathlib import Path
from custody_checks import digest
from lean_source_static_preflight_v2 import inspect_bytes

HERE=Path(__file__).resolve().parent

def main():
    offer=HERE/'numeric-exact-threshold-offer-v1'
    manifest=offer/'manifest.json'
    assert digest(manifest)=='7BA8DAE22C015D63E3C681F6D4599849A594DE0D7366D92BC6B5DDDD387196E7'
    value=json.loads(manifest.read_bytes())
    assert {p.name for p in offer.iterdir()}=={'manifest.json'}|{r['path'] for r in value['offer_files']}
    for r in value['offer_files']:
        p=offer/r['path'];assert p.stat().st_size==r['bytes'] and digest(p)==r['sha256']
    inp=value['source_input'];archive=Path(inp['path'])
    assert archive.stat().st_size==inp['bytes'] and digest(archive)==inp['sha256']
    with tarfile.open(archive,'r:gz') as tar:
        baseline=json.load(tar.extractfile('capture-manifest.json'))
        for r in value['project_dependencies']+[value['project_lake_manifest']]:
            data=tar.extractfile(r['member']).read()
            assert len(data)==r['bytes'] and hashlib.sha256(data).hexdigest().upper()==r['sha256']
            category='project_sources' if r['member'].endswith('.lean') else 'configs'
            assert baseline[category][r['member']]['sha256']==r['sha256']
        lake=json.load(tar.extractfile('lake-manifest.json'))
        mathlib,=[p for p in lake['packages'] if p['name']=='mathlib']
        assert mathlib['rev']==value['project_lake_manifest']['mathlib_revision']
    api=value['mathlib_api_source'];historical=Path(api['path'])
    assert historical.stat().st_size==api['bytes'] and digest(historical)==api['sha256']
    actual=archive.parent/'checks/20261011T060052629965Z/qualified-native/cmmsa_a8_output_20261011T060110Z_204d10cd/remote-evidence/package-sources.tar.gz'
    assert digest(actual)=='3D4C0038AC4CFC0D8A901DC8CFD8887EC71F172EF33CF19C4B0D9D1AFBAED638'
    assert baseline['cache_provenance']['package_sources'][api['member']]==api['sha256_member']
    for p in (actual,historical):
        with tarfile.open(p,'r:gz') as tar:
            data=tar.extractfile(api['member']).read()
            assert len(data)==api['bytes_member'] and hashlib.sha256(data).hexdigest().upper()==api['sha256_member']
    source=offer/'ActualNumericExactThreshold.lean';checks=offer/'ActualNumericExactThresholdChecks.lean'
    lexical=[inspect_bytes(p.read_bytes(),p.name) for p in (source,checks)]
    declarations=re.findall(r'(?m)^theorem (\w+)',source.read_text(encoding='utf-8'))
    requested=re.findall(r'(?m)^#print axioms (.+)$',checks.read_text(encoding='utf-8'))
    assert len(requested)==5 and set(requested)=={'PvNP.RealizableHardness.ActualNumericExactThreshold.'+n for n in declarations}
    target=HERE/'numeric-exact-threshold-capture-v1';target.mkdir(exist_ok=False)
    (target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    rows=[]
    for p in sorted(offer.iterdir()):
        data=p.read_bytes();(target/p.name).open('xb').write(data)
        assert digest(target/p.name)==digest(p)
        rows.append(dict(original=str(p),copy=p.name,bytes=len(data),sha256=digest(p)))
    report=dict(files=rows,project_dependencies_verified=4,lake_manifest_verified=True,
        actual_full113_package_source_verified=True,actual_package_archive=str(actual),
        actual_package_archive_sha256=digest(actual),lexical_preflight=lexical,requested_axioms=requested,
        root_read_complete_source_checks_map_manifest=True,
        static_review_concerns=['In actualSelectedRho_eq_fixedRho_of_dvd_pos, positivity after dsimp [bOf] has no m-positive hypothesis. Derive bOf m > 0 explicitly from bOf m dividing positive h, preserving the existing theorem hypotheses.'],
        capture_control_sha256=digest(__file__),compiler_invoked=False,accepted=False,repair_requested=True)
    (target/'index.json').open('x').write(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(folder=target.name,index_sha256=digest(target/'index.json'),requests=len(requested),uncompiled=True)),flush=True)

if __name__=='__main__':main()
