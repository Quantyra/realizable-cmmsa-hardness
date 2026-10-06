"""Full integrated A8 capture and serialized GCP development; never local Lean."""
import ast, json, re, runpy, sys, types
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent; PACKAGE=HERE.parent
m=runpy.run_path(str(PACKAGE/'retry-16/controller.py'),run_name='integrated40_import')
common=m['common']; REPO=common.REPO
NAMES=['AveragedTransport','AveragedAssembly','EnergyNaturality','PairAssembly','AmbientAssembly','Endpoint']
OWNED=['lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A8'+n+s+'.lean' for n in NAMES for s in ['', 'Checks']]
OWNED+=['lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A11WeightedAggregate'+s+'.lean' for s in ['', 'Checks']]
SOURCE=OWNED[-2]; CHECKS=OWNED[-1]; REPORT='docs/a8-gcp/r1007/retry-40/author-report.md'
CAPTURE='capture-integrated-40'; PRIOR='cmmsa_a8_output_20261005T191951Z_7ea37ffb'
def module(name,text):
    ast.parse(text); mod=types.ModuleType(name); mod.__file__=str(PACKAGE/'prepare.py')
    sys.modules[name]=mod; exec(compile(text,mod.__file__,'exec'),mod.__dict__); return mod
def configure():
    common.SOURCE=SOURCE; common.CHECKS=CHECKS; common.REPORT=REPORT
    common.FROZEN={n:common.file_sha(REPO/n) for n in OWNED+[REPORT]}
    raw_requests=list(dict.fromkeys(n for rel in OWNED if rel.endswith('Checks.lean') for n in re.findall(r'^#print axioms (\S+)',(REPO/rel).read_text(encoding='utf-8'),re.M)))
    owner_map=json.loads((HERE/'axiom-declaration-owner-map.json').read_bytes())['requests']
    assert raw_requests==[row['original_request'] for row in owner_map]
    common.REQUESTED_AXIOMS=[row['qualified'] for row in owner_map]
    assert len(common.REQUESTED_AXIOMS)==49 and len(set(common.REQUESTED_AXIOMS))==49
    import runner
    original_render=runner.render_remote
    def render(run,manifest):
        prior_tag=manifest['resource_plan']['reuse_workspace']
        shim=json.loads(json.dumps(manifest)); shim['resource_plan']['reuse_workspace']='cmmsa_analytic_20261004T002601Z'
        text=original_render(run,shim)
        assert re.fullmatch(r'cmmsa_a8_output_\d{8}T\d{6}Z_[a-f0-9]{8}',prior_tag)
        return text.replace('cmmsa_analytic_20261004T002601Z',prior_tag)
    runner.render_remote=render
    original_cloud=runner.Control.cloud
    def cloud(self,args,**kwargs):
        chunk=next((a for a in args if a.startswith('--command=dd if=')),None)
        if chunk is not None:
            assert re.fullmatch(r'--command=dd if=/home/dfredriksen_quantyra_org/cmmsa-evidence/cmmsa_a8_output_\d{8}T\d{6}Z_[a-f0-9]{8}-evidence\.tar\.gz bs=4194304 skip=\d+ count=1 status=none \| base64 -w0',chunk)
            kwargs['allow_failure']=True
            code,out,err=original_cloud(self,args,**kwargs)
            if code:
                common.write_new(self.run/('archive-chunk-native-nonzero-'+str(len(self.records)-1)+'.json'),common.json_bytes({'native_exit':code,'raw_receipts_preserved':True,'payload_sha256':common.sha(out),'compiler_outcome_unmodified':True,'custody_requires_exact_base64_length_and_full_remote_sha256':True}))
            return code,out,err
        if any(a.startswith('--command=ps -eo') for a in args):
            args=[('--command='+m['old'].old.PROBE_COMMAND) if a.startswith('--command=ps -eo') else a for a in args]
            code,out,err=original_cloud(self,args,**kwargs)
            assert code==0 and out.strip()==b'CMMSA_RETRY14_IDLE'
            return code,b'',err
        return original_cloud(self,args,**kwargs)
    runner.Control.cloud=cloud
    return runner
def offline():
    configure(); previous=PACKAGE/'runs'/PRIOR; priorcap=PACKAGE/'captures/capture-retry-16'
    terminal=json.loads((previous/'terminal.json').read_bytes())
    assert terminal['vm_terminal_receipt']['status']=='TERMINATED'
    m['old'].old.verify_custody(json.loads((previous/'custody.json').read_bytes()))
    old_manifest=json.loads((priorcap/'manifest.json').read_bytes())
    old=m['old'].old
    for rel in OWNED:
        data=(REPO/rel).read_bytes(); old.utf8(data); assert not common.forbidden_tokens(data)
    r=previous/'remote-evidence'
    objects=json.loads((r/'object-after.json').read_bytes())
    stems={'.lake/build/lib/lean/'+n.removeprefix('lean/').removesuffix('.lean')+'.olean' for n in old_manifest['project_sources'] if n not in OWNED}
    cache_objects={n:h for n,h in objects.items() if any(n==s or n.startswith(s+'.') for s in stems)}
    assert len(json.loads((r/'compiled-project-objects.json').read_bytes()))==200
    provenance={'run':PRIOR,'cloud_archive_sha256':terminal['evidence_archive_sha256'],'project_sources':{n:v['sha256'] for n,v in old_manifest['project_sources'].items() if n not in OWNED},'objects':cache_objects,'compiler':json.loads((r/'compiler-identity.json').read_bytes()),'package_sources':json.loads((r/'package-source-hashes.json').read_bytes()),'core_sources':json.loads((r/'core-source-hashes.json').read_bytes()),'dependency_exit':0,'source_exit':1,'acceptance':False}
    cloud=(PACKAGE/'cloud_capture.py').read_text(encoding='utf-8')
    insertion="""    cache=manifest['cache_provenance']
    assert digest(compiler)==cache['compiler']['sha256']
    assert package_sources==cache['package_sources'] and core_sources==cache['core_sources']
    assert all(manifest['project_sources'][n]['sha256']==h for n,h in cache['project_sources'].items())
    assert all(digest(work/n)==h for n,h in cache['objects'].items()), 'Cached dependency object changed'
    save(evidence/'verified-cache-provenance.json',cache)
"""
    cloud=cloud.replace('    removed = []\n',insertion+'    removed = []\n').replace('for rel in manifest["project_sources"]:\n        stem = build', 'for rel in manifest["owned_sources"]:\n        stem = build')
    start=cloud.index('    removed = []\n')
    end=cloud.index('    snapshot(evidence)',start)
    invalidation="""    removed = []
    invalidated = {}
    for rel in manifest['owned_sources']:
        suffix=rel.removeprefix('lean/').removesuffix('.lean')
        for root in [work/'.lake/build/lib/lean',work/'.lake/build/ir']:
            stem=root/suffix
            for path in sorted(stem.parent.glob(stem.name+'.*')):
                assert path.is_file() and path.resolve().is_relative_to(work.resolve())
                name=str(path.relative_to(work))
                invalidated[name]={'sha256':digest(path),'nlink_before':path.stat().st_nlink}
                path.unlink()
                removed.append(name)
            assert not list(stem.parent.glob(stem.name+'.*')), 'Owned auxiliary remains'
    save(evidence/'invalidated-project-objects.json',removed)
    save(evidence/'invalidated-owned-artifacts.json',invalidated)
    save(evidence/'owned-artifact-absence-before-compile.json',{'owned_sources':manifest['owned_sources'],'roots':['.lake/build/lib/lean','.lake/build/ir'],'all_absent':True,'prior_cache_untouched':True})
"""
    cloud=cloud[:start]+invalidation+cloud[end:]
    ast.parse(cloud)
    cloud=cloud.replace("for rel in manifest['owned_sources']:","for rel in manifest['owned_sources']+['lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A9AmbientReindex.lean']:")
    common.write_new(HERE/'cloud_capture.snapshot.py',cloud)
    text=(PACKAGE/'prepare.py').read_text(encoding='utf-8')
    text=text.replace('SCRIPTS = [',"SCRIPTS = ['retry-40/axiom-declaration-owner-map.json', 'retry-40/controller.py', 'retry-40/cloud_capture.snapshot.py', 'retry-40/adapted-prepare.snapshot.py', ")
    text=text.replace('rel in {SOURCE, CHECKS} else dependency_bytes(rel)','rel in OWNED else dependency_bytes(rel)').replace('for rel in [SOURCE, CHECKS]:','for rel in OWNED:')
    text=text.replace('save("inputs/cloud_capture.py", (PACKAGE / "cloud_capture.py").read_bytes())','save("inputs/cloud_capture.py", (PACKAGE / "retry-40/cloud_capture.snapshot.py").read_bytes())')
    start=text.index('    stages = ['); end=text.index('    inner = {',start)
    text=text[:start]+"    stages=STAGES\n    save('inputs/fresh-integrated-axioms.lean', FRESH.encode('utf-8'))\n"+text[end:]
    text=text.replace('"claims_boundary": CLAIM}', '"claims_boundary": CLAIM,"owned_sources":OWNED,"cache_provenance":CACHE}')
    text=text.replace('"project_modules": len(records) - 1, "check_modules": 1','"project_modules": len(records) - 7, "check_modules": 7')
    text=text.replace('"reuse_workspace": "cmmsa_analytic_20261004T002601Z"','"reuse_workspace": PRIOR')
    common.write_new(HERE/'adapted-prepare.snapshot.py',text)
    p=module('prepare30',text); p.OWNED=OWNED; p.PRIOR=PRIOR; p.CACHE=provenance
    def dep(rel):
        if rel=='lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A9AmbientReindex.lean':
            data=(HERE/'accepted-a9-source.lean.snapshot').read_bytes(); assert common.sha(data)=='5B4958CE0B86D02F578457715F05382EF6037535C5CDB7177F48945FF1E8A2BE'
            return data,'accepted A9 exact frozen bytes; fresh native dependency build with owned-artifact invalidation'
        assert rel in old_manifest['project_sources'], 'Unmapped dependency '+rel
        data=(priorcap/'inputs'/rel).read_bytes(); assert common.sha(data)==old_manifest['project_sources'][rel]['sha256']
        return data,'retry16 exact GCP-green dependency closure; cache object identities tracked'
    p.dependency_bytes=dep
    module_names=lambda names:[n.removeprefix('lean/').removesuffix('.lean').replace('/','.') for n in names]
    p.STAGES=[{'index':0,'name':'unchanged-dependency-closure','argv':['lake','build','PvNP.RealizableHardness.ActualBinaryMatrixHC46A7Transfer','PvNP.RealizableHardness.ActualBinaryMatrixHC46A9AmbientFiber','PvNP.RealizableHardness.ActualBinaryMatrixHC46T2Transfer','PvNP.RealizableHardness.ActualBinaryMatrixHC46A8OutputCoordinateTransport','PvNP.RealizableHardness.ActualBinaryMatrixHC46A9AmbientReindex']},{'index':1,'name':'complete-integrated-source','argv':['lake','build',*module_names(OWNED[::2])]},{'index':2,'name':'complete-integrated-checks','argv':['lake','build',*module_names(OWNED[1::2])]},{'index':3,'name':'fresh-integrated-axioms','argv':['lake','env','lean','fresh-integrated-axioms.lean']}]
    p.FRESH='\n'.join('import '+n for n in module_names(OWNED[1::2]))+'\n'+'\n'.join('#print axioms '+n for n in common.REQUESTED_AXIOMS)+'\n'
    sys.argv=['prepare','--name',CAPTURE]; p.main()
    manifest=common.verify_capture(PACKAGE/'captures'/CAPTURE,live=False)
    assert all(manifest['project_sources'][n]['sha256']==common.FROZEN[n] for n in OWNED)
    common.write_new(HERE/'offline-gates.json',common.json_bytes({'candidate_hashes':common.FROZEN,'manifest_sha256':common.file_sha(PACKAGE/'captures'/CAPTURE/'manifest.json'),'closure_modules':len(manifest['project_sources']),'axiom_requests':common.REQUESTED_AXIOMS,'cache_objects':len(cache_objects),'original_warning_baseline':981,'endpoint_accepted':False}))
    print('IMMUTABLE INTEGRATED CAPTURE ACK',CAPTURE,flush=True)
def launch():
    runner=configure(); gates=json.loads((HERE/'offline-gates.json').read_bytes())
    assert common.FROZEN==gates['candidate_hashes']
    capture=PACKAGE/'captures'/CAPTURE; manifest=common.verify_capture(capture,live=False)
    common.local_process_check()
    assert not (HERE/'launch-once.json').exists()
    control=runner.Control(HERE/'control'); state=control.describe(); assert state['status']=='TERMINATED'
    common.write_new(HERE/'launch-once.json',common.json_bytes({'state':state,'manifest_sha256':common.file_sha(capture/'manifest.json'),'controller_sha256':common.file_sha(__file__)}))
    return runner.execute(capture,manifest)
if __name__=='__main__':
    if sys.argv[1]=='offline': offline()
    elif sys.argv[1]=='launch': sys.exit(launch())
