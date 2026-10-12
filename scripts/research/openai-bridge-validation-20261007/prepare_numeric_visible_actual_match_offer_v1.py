from pathlib import Path
import hashlib,json,re,subprocess,tarfile

S=Path(__file__).resolve().parent
OUT=S/'numeric-visible-actual-matching-offer-20261011-v1'
P=Path(r'C:\Users\dfred\Desktop\Projects\IGH\Quantyra-AI-Planning')
ARCHIVE=Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PIN='70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
assert not (OUT/'manifest.json').exists()
with ARCHIVE.open('rb') as f:
    assert hashlib.file_digest(f,'sha256').hexdigest().upper()==PIN
parents=[]
with tarfile.open(ARCHIVE,'r:gz') as a:
    for name in ['SubmoduleFunctionalGluing','ActualStarAffineFunctionalSelection','ActualFiniteLaw','ActualMaximalPairLadder']:
        member='lean/PvNP/RealizableHardness/'+name+'.lean'
        raw=a.extractfile(member).read()
        assert raw==(S/'full107-trace-qualified-source-record-v1/review-sources'/member).read_bytes()
        parents.append(dict(member=member,bytes=len(raw),sha256=sha(raw)))
    toolchain=a.extractfile('lean-toolchain').read()
    assert toolchain.decode().strip()=='leanprover/lean4:v4.34.0-rc2'
specs=[
('numeric-visible-ambient-ladder-offer-20261011-v1/ActualVisibleAmbientLadder.reconstruction-v2.lean',
 'numeric-visible-ambient-ladder-capture-v1','A31EFC136E87632DB17042109B5F1EDBBF08C1AB975F54E85E73297A640C558B','ActualVisibleAmbientLadder'),
('numeric-visible-list-strategy-offer-20261011-v1/ActualVisibleListStrategy.lean',
 'numeric-visible-list-strategy-capture-v1','1E7176008530D5D0BB0DEE16C428A295FFD08E6CB7BFEC34F0BAFEE46DC85D77','ActualVisibleListStrategy'),
('numeric-visible-output-transport-offer-20261011-v1/ActualVisibleOutputTransport.lean',
 'numeric-visible-output-transport-capture-v1','9D06450EE26E1BC5D7213FBE273765433C2880A0BCD3B894BDADBFF277FFE914','ActualVisibleOutputTransport'),
('numeric-restricted-visible-pair-offer-20261011-v2/ActualRestrictedVisiblePair.lean',
 'numeric-restricted-visible-pair-capture-v2','D8B69152D0DEC8E5BED9157B86AEABBFA20F809CF3D97357DEB0BBCCF0E1B14D','ActualRestrictedVisiblePair'),
('numeric-functional-assignment-acceptance-offer-20261011-v2/ActualFunctionalAssignmentAcceptance.lean',
 'numeric-functional-assignment-acceptance-capture-v2','DD587A2CEA6758DCF09AE378B506B9E48B2F8AFFF6EBB378A480442FFF883E31','ActualFunctionalAssignmentAcceptance'),
('numeric-random-extension-offer-20261011-v1/ActualRandomExtensionSuccess.lean',
 'numeric-random-extension-capture-v1','6FCB5FC2C7A00F24555287CCFCEAC98B754F277A8C4E3FE1FE830CD78FDB6D5B','ActualRandomExtensionSuccess'),
('numeric-original-decoder-selection-offer-20261011-v1/ActualOriginalDecoderSelection.lean',
 'numeric-original-decoder-selection-capture-v1','EFB5C764DA0A15E9DBFFACF5E366A8D5F20B18F9A687293629F40CED77AD3137','ActualOriginalDecoderSelection')]
candidates=[]
for relative,capture,pin,module in specs:
    raw=(S/relative).read_bytes()
    assert sha(raw)==pin,relative
    index=(S/capture/'index.json').read_bytes()
    assert pin in index.decode(),capture
    identical=[p for p in (S/capture).glob('*.lean') if p.read_bytes()==raw]
    assert len(identical)==1,(capture,identical)
    candidates.append(dict(module='PvNP.RealizableHardness.'+module,path=relative,
        bytes=len(raw),sha256=pin,capture_index=capture+'/index.json',
        capture_sha256=sha(index),captured_source=str(identical[0]),accepted=False))
source=(OUT/'ActualVisibleActualMatch.lean').read_bytes()
code=source.decode('utf-8')
assert not source.startswith(b'\xef\xbb\xbf')
assert all(x not in code for x in ['\ufffd','\u00e2\u02c6','\u00e2\u2020','\\sum'])
assert not re.search(r'\b(?:sorry|admit|axiom)\b',code)
# Balanced nested Lean comments, strings, and all ordinary bracket kinds.
stack=[]; depth=0; quoted=False; i=0
while i<len(code):
    if depth:
        if code[i:i+2]=='/-':depth+=1;i+=2;continue
        if code[i:i+2]=='-/':depth-=1;i+=2;continue
        i+=1;continue
    if quoted:
        if code[i]=='\\':i+=2;continue
        if code[i]=='"':quoted=False
        i+=1;continue
    if code[i:i+2]=='/-':depth=1;i+=2;continue
    if code[i:i+2]=='--':
        i=code.find('\n',i)
        if i<0:i=len(code)
        continue
    if code[i]=='"':quoted=True;i+=1;continue
    if code[i] in '([{':stack.append((code[i],i))
    if code[i] in ')]}':
        assert stack and stack[-1][0]=={')':'(',']':'[','}':'{'}[code[i]],i
        stack.pop()
    i+=1
assert not stack and not depth and not quoted
exports=re.findall(r'(?m)^theorem (\w+)',code)
definitions=re.findall(r'(?m)^abbrev (\w+)',code)
assert len(exports)==9 and definitions==['OriginalCoord']
checks='import PvNP.RealizableHardness.ActualVisibleActualMatch\n\n'
for name in definitions+exports:
    checks+='#check PvNP.RealizableHardness.ActualVisibleActualMatch.'+name+'\n'
for name in exports:
    checks+='#print axioms PvNP.RealizableHardness.ActualVisibleActualMatch.'+name+'\n'
diagnostics=OUT/'diagnostics'
for name in ['Checks.lean','CHECKS.md']:
    if (OUT/name).exists():
        old=(OUT/name).read_bytes()
        dest=diagnostics/(Path(name).stem+'.before-root-refresh.'+sha(old)+Path(name).suffix)
        if dest.exists():assert dest.read_bytes()==old
        else:dest.write_bytes(old)
(OUT/'Checks.lean').write_text(checks,encoding='utf-8',newline='\n')
(OUT/'CHECKS.md').write_text(
    '# Source-only checks\n\nThe Checks module requests all nine public theorem axiom profiles and all ten public declarations. '
    'UTF-8, glyph, delimiter and exact dependency preflight passed locally. No local Lean was invoked. '
    'Independent static review of the generic fiber/cardinality/codimension and actual direct-visible matching portions found no concrete defect; '
    'the subsequently added selected-pair and original-assignment endpoints remain subject to further review and GCP checks. '
    'This is not kernel acceptance, a full game-law identification, or source NO.\n',encoding='utf-8',newline='\n')
(OUT/'.gitattributes').write_text('* -text\n',encoding='utf-8',newline='\n')
plan_relative='docs/research/pvnp/full90-actual-rhs-numeric-no-obligations-2026-10-08.md'
plan_raw=subprocess.run(['git','-C',str(P),'show','bf968d0:'+plan_relative],check=True,stdout=subprocess.PIPE).stdout
plan=plan_raw.decode()
heading='## 2026-10-11 Restriction codimension without a rank-stability assumption'
assert plan.count(heading)==1
section=plan[plan.index(heading):].split('\n## ',1)[0]
files=[]
for p in sorted(OUT.rglob('*')):
    if not p.is_file():continue
    raw=p.read_bytes()
    raw.decode('utf-8')
    assert not raw.startswith(b'\xef\xbb\xbf')
    files.append(dict(path=p.relative_to(OUT).as_posix(),bytes=len(raw),sha256=sha(raw),
                      candidate_scope='diagnostics' not in p.parts))
manifest=dict(schema=OUT.name,author='/root',initial_author='/root/full_decoder_recovery',
    story='E002/S3137',accepted=False,compiler_invoked=False,
    full114_archive=dict(path=str(ARCHIVE),sha256=PIN,accepted=False),
    parent_dependencies=parents,candidate_dependencies=candidates,
    direct_imports=re.findall(r'(?m)^import (\S+)',code),
    functional_dependency_rebind=dict(historical_geometry_capture_unchanged=True,
        historical_functional_source='52106CF7B184E2A25F2729D840758CC42C3D148B9C4BA44005D45AB536C65340',
        successor_functional_source=specs[4][2],candidate_recompile_required=True),
    planning_argument=dict(repository=str(P),relative_path=plan_relative,committed_head='bf968d0',
        committed_blob_sha256=sha(plan_raw),heading=heading,section_sha256=sha(section.encode())),
    toolchain=dict(value=toolchain.decode().strip(),sha256=sha(toolchain)),
    mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2',
    public_axiom_requests=exports,checked_definitions=definitions,
    original_rank_stability_required=False,original_window_supported_required=False,
    direct_visible_event_start=True,second_side_loss_charged=False,
    same_selected_pair_equation_endpoint=True,assignment_agreement_both_directions=True,
    game_law_identified=False,source_no_proved=False,
    failed_author_turns=['stream-disconnected','remote-compaction-disconnected'],
    predecessor_snapshot_sha256='3DC8196425B65E396AB17563BDD9683D543E3C38AC895B4F8BD352BBC4489F56',
    files=files)
(OUT/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(dict(source_sha256=sha(source),checks_sha256=sha(checks.encode()),
    manifest_sha256=sha((OUT/'manifest.json').read_bytes()),exports=exports,files=len(files))))
