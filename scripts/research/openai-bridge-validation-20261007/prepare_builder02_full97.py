"""Immutable repair of malformed Full96 new-source tokens and section endings."""
import copy
import io
import json
from pathlib import Path
import re
import tarfile
from custody_checks import digest,verify_local_custody
from prepare_builder02 import sha
from prepare_builder02_full90 import capsule
from prepare_builder02_full96 import OUTPUT as PARENT,ADDED,REQUESTS
HERE=Path(__file__).parent
OUTPUT=PARENT.parent/'full97-spectral-bridge-utf8-section-repair-resource02'
CANDIDATES=HERE/'full97-spectral-bridge-repair-candidates-v1'

def validate_language(data,name):
    text=data.decode('utf-8',errors='strict')
    assert chr(0xfffd) not in text and not re.search(r'\?(?!_)',text),'Corrupted source token'
    assert text.count('noncomputable section')==1 and text.count('\nend\nend ')==1,'Unclosed unnamed section'
    assert any(ord(c)>127 for c in text),'Expected mathematical Unicode tokens missing'
    assert not re.search(r'\b(sorry|admit|axiom)\b',text)
    if name=='BinaryMatrixSameRangeOrbit.lean':
        assert text.count(chr(0x2192)+chr(0x2097))==3 and chr(0x2243)+chr(0x2097) in text
        assert chr(0x2203) in text and chr(0x2200) in text
        assert text.count('LinearMap.mem_range')==3
    else:
        assert text.count(chr(0x2194))==2 and text.count('Iff.rfl')==2
        assert chr(0x2192) in text
    return True

def parent_custody():
    marker=json.loads((PARENT/'launch-once.json').read_bytes());check=Path(marker['preflight'])
    receipt=json.loads((check/'terminal-custody.json').read_bytes());stop=json.loads((check/'vm-termination.json').read_bytes())
    custody=receipt['custody'];verify_local_custody(custody['short_path'],custody['repository_path'],custody['remote_sha256'],custody['bytes'])
    assert custody['remote_sha256']=='BFD42A52C5F8C63421A7A5FEBF7B52F3958762A6D93C328525913CC4702B5341'
    assert marker['run']==receipt['run']==stop['run']
    assert receipt['terminal']['native_terminal'] and not receipt['terminal']['compile_green']
    assert [x['native_exit'] for x in receipt['terminal']['stages']]==[0,0,0,0,1,125,125]
    assert stop['custody_verified_before_stop'] and stop['independent']['status']=='TERMINATED' and str(stop['independent']['id'])=='7237681467779354904'
    with tarfile.open(custody['repository_path']) as archive:
        text=archive.extractfile('stage-4.stdout').read().decode()
        assert text.count("unexpected token '?'")==3 and text.count('The current section is unnamed')==2
        before=json.loads(archive.extractfile('source-before.json').read());after=json.loads(archive.extractfile('source-after.json').read());assert before==after
    return marker,custody

def make_successor(old):
    new=dict(old);manifest=json.loads(old['capture-manifest.json'])
    deriv=json.loads((CANDIDATES/'derivation.json').read_bytes())
    for row,rel in zip(deriv['sources'],ADDED):
        assert row['name']==rel.rsplit('/',1)[-1] and sha(old[rel])==row['old_sha256']
        data=(CANDIDATES/row['name']).read_bytes();assert sha(data)==row['new_sha256'] and len(data)==row['new_bytes']
        validate_language(data,row['name']);new[rel]=data;manifest['project_sources'][rel]={'sha256':sha(data),'bytes':len(data)}
    new['capture-manifest.json']=(json.dumps(manifest,indent=2)+'\n').encode();validate_expansion(old,new);return new

def validate_expansion(old,new):
    assert set(old)==set(new)
    assert sorted(n for n in old if old[n]!=new[n])==sorted(ADDED+['capture-manifest.json'])
    a=json.loads(old['capture-manifest.json']);b=json.loads(new['capture-manifest.json'])
    assert len(a['project_sources'])==len(b['project_sources'])==325
    assert a['requested_axioms']==b['requested_axioms'] and len(set(b['requested_axioms']))==184
    deriv=json.loads((CANDIDATES/'derivation.json').read_bytes());normalized=copy.deepcopy(b)
    for row,rel in zip(deriv['sources'],ADDED):
        assert sha(old[rel])==row['old_sha256']
        data=(CANDIDATES/row['name']).read_bytes();assert new[rel]==data and sha(data)==row['new_sha256']
        validate_language(data,row['name']);assert b['project_sources'][rel]=={'sha256':sha(data),'bytes':len(data)}
        normalized['project_sources'][rel]=a['project_sources'][rel]
    assert normalized==a,'Stage/profile/config/compiler/cache/hypothesis scope changed'
    return True

def main():
    from full96_capture_gates import validate_successor
    validate_successor();marker,custody=parent_custody()
    binding=json.loads((PARENT/'resource-binding.json').read_bytes())
    for name,pin in binding['files'].items():assert digest(PARENT/name)==pin
    old=capsule(PARENT/'input-archive.tar.gz');new=make_successor(old)
    OUTPUT.mkdir()
    with tarfile.open(OUTPUT/'input-archive.tar.gz','x:gz') as archive:
        for name,data in sorted(new.items()):
            member=tarfile.TarInfo(name);member.size=len(data);member.mode=0o644;archive.addfile(member,io.BytesIO(data))
    (OUTPUT/'capture-manifest.json').write_bytes(new['capture-manifest.json'])
    expansion=dict(schema='full97-exact-two-source-utf8-section-repair-v1',parent_run=marker['run'],parent_custody=custody,
        repaired_sources=ADDED,added_sources=[],additional_profiles=REQUESTS,all323_other_source_bytes_preserved=True,
        all184_requests_and_seven_stage_commands_preserved=True,compiler_packages_core_cache_configs_and_harnesses_preserved=True,
        candidate_derivation_sha256=digest(CANDIDATES/'derivation.json'),ASCII_only_generation_with_explicit_UTF8_codepoints=True,
        explicit_mem_range_conversion_and_section_closure=True,original_statement_intent_and_hypotheses_preserved=True,
        Spectral47_inhabitant_constructed=False,local_compilation=False,native_verification_pending=True,launch_clearance=False,accepted=False)
    (OUTPUT/'source-expansion.json').write_text(json.dumps(expansion,indent=2)+'\n',encoding='utf-8')
    successor=copy.deepcopy(binding)
    successor.update(parent_resource_binding_sha256=digest(PARENT/'resource-binding.json'),parent_run=marker['run'],source_expansion_sha256=digest(OUTPUT/'source-expansion.json'),
        changed_files=ADDED+['capture-manifest.json'],added_files=[],project_sources_preserved=323,additional_profiles=REQUESTS,
        auxiliary_inputs={n:sha(new[n]) for n in binding['auxiliary_inputs']},files={n:digest(OUTPUT/n) for n in ['input-archive.tar.gz','capture-manifest.json']})
    (OUTPUT/'resource-binding.json').write_text(json.dumps(successor,indent=2)+'\n',encoding='utf-8');assert capsule(OUTPUT/'input-archive.tar.gz')==new
    print(json.dumps({'root':str(OUTPUT),'sources':325,'profiles':184,'input_sha256':digest(OUTPUT/'input-archive.tar.gz'),'launch_clearance':False,'accepted':False}))
if __name__=='__main__':main()
