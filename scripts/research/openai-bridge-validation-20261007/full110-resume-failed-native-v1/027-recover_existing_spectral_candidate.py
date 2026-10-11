"""Recover exact eleven-module handoff candidate from Git; never invoke Lean."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
from custody_checks import digest

HERE=Path(__file__).parent
HEAD='c38451c80345f8170b36582bd17e58d2fd7a6bd1'
HANDOFF=Path('C:/Users/dfred/Desktop/Projects/IGH/Quantyra-AI-Planning/docs/research/pvnp/original-spectral47-proof-and-application-handoff-2026-10-06.md')
CAPTURE=Path('C:/Users/dfred/.quantyra/builder02/full100-matrix-fourier-bullet-repair-resource02/capture-manifest.json')
ROOT=HERE/'existing-spectral-candidate-recovery-v1'

def main(verify=False):
    manifest=json.loads(CAPTURE.read_bytes())
    assert digest(CAPTURE)=='8E71DE454150DEAC5FE9F12B1DCCF8BA768D7788A70D5F159D436C2682D73D3D'
    rows=re.findall(r'^\| (ActualFinite\w+) \| ([A-F0-9]{64}) \|$',HANDOFF.read_text(encoding='utf-8'),re.M)
    assert len(rows)==11
    owned={'PvNP.RealizableHardness.'+name for name,_ in rows}
    if not verify:ROOT.mkdir()
    recovered=[];common={};external=set()
    for name,pin in rows:
        rel='lean/PvNP/RealizableHardness/'+name+'.lean'
        data=subprocess.check_output(['git','show',HEAD+':'+rel]);text=data.decode('utf-8')
        assert hashlib.sha256(data).hexdigest().upper()==pin
        assert rel not in manifest['project_sources'] and not data.startswith(b'\xef\xbb\xbf')
        assert not re.search(r'^\s*-[ \t]+',text,re.M)
        stripped=re.sub(r'/\-.*?\-/|--[^\n]*','',text,flags=re.S)
        assert not re.search(r'\b(?:sorry|admit|axiom)\b',stripped)
        imports=re.findall(r'^import (\S+)',text,re.M)
        for module in imports:
            if module.startswith('PvNP.') and module not in owned:
                path='lean/'+module.replace('.','/')+'.lean'
                assert path in manifest['project_sources'], 'Missing common import: '+path
                source=subprocess.check_output(['git','show',HEAD+':'+path])
                value=hashlib.sha256(source).hexdigest().upper()
                common[path]=dict(git_source_sha256=value,captured_sha256=manifest['project_sources'][path]['sha256'],
                    matches_current_capture=value==manifest['project_sources'][path]['sha256'])
            elif not module.startswith('PvNP.'):
                external.add(module)
        output=ROOT/(name+'.lean')
        if verify:assert output.read_bytes()==data
        else:
            with output.open('xb') as stream:stream.write(data)
        recovered.append(dict(path=rel,recovered_path=str(output),sha256=pin,bytes=len(data),imports=imports,
            matches_original_handoff=True,in_Full100_capture=False))
    assert all(r['matches_current_capture'] for r in common.values()), 'Common dependency needs explicit reconciliation'
    value=dict(schema='existing-eleven-module-spectral-handoff-recovery-v1',source_git_head=HEAD,
        handoff_path=str(HANDOFF),handoff_sha256=digest(HANDOFF),full100_manifest_sha256=digest(CAPTURE),
        recovered_modules=recovered,total_bytes=sum(r['bytes'] for r in recovered),
        direct_common_imports=common,external_imports=sorted(external),
        valid_UTF8_no_BOM_no_ASCII_bullets_no_forbidden_owned_tokens=True,
        original_candidate_and_Full100_captures_unchanged=True,all_327_existing_sources_must_be_preserved_in_successor=True,
        native_reverification_and_complete_import_closure_required=True,
        actual_application_removing_hSpectral_required=True,manuscript_exact_energy_and_G_Phi_laws_remain_in_scope=True,
        compiler_invoked=False,cloud_operation=False,launch_clearance=False,accepted=False,full_goal_complete=False)
    p=ROOT/'recovery.json';data=(json.dumps(value,indent=2)+'\n').encode('utf-8')
    if verify:assert p.read_bytes()==data
    else:
        with p.open('xb') as stream:stream.write(data)
    print(json.dumps(dict(modules=11,bytes=value['total_bytes'],common_imports=len(common),handoff_matches=True,
        recovery_sha256=digest(p),native_verified=False)))

if __name__=='__main__':
    assert sys.argv[1:] in ([],['--verify'])
    main(bool(sys.argv[1:]))
