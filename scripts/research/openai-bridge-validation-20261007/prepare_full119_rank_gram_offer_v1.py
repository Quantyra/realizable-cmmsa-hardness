"""One proof-line repair from exact failed Full118 bytes. Never runs Lean."""
from pathlib import Path
import difflib, hashlib, json, re, tarfile

S = Path(__file__).resolve().parent
OUT = S / 'full119-rank-gram-repair-v1'
PACKET = S / 'full118-rank-gram-diagnostic-packet-v1'
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full118-exact-real-complex-operators-repair8-resource02\input-archive.tar.gz')
PIN = '097DB8FD8BA4922D0BB9698D67CF383D43B4AFBE509EF89E0738A87B82B82C62'
sha = lambda raw: hashlib.sha256(raw).hexdigest().upper()
assert not OUT.exists()
with ARCHIVE.open('rb') as stream:
    assert hashlib.file_digest(stream, 'sha256').hexdigest().upper() == PIN
assert sha((PACKET/'index.json').read_bytes()) == 'D3CA7B240129E13CDD653C8404B82C721A627E3954D46D23EC9CCE4920A6C323'
member = 'lean/PvNP/RealizableHardness/ExactRealRankGram.lean'
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    old = archive.extractfile(member).read()
    assert old == (PACKET/'ExactRealRankGram.lean').read_bytes()
    assert sha(old) == 'FF8981B60487A904F74F58903636FC7501E804247D5FDF45A8B9737F9246E06D'
    checks = archive.extractfile(member.replace('.lean', 'Checks.lean')).read()
    assert checks == (PACKET/'ExactRealRankGramChecks.lean').read_bytes()
    toolchain = archive.extractfile('lean-toolchain').read()
    assert toolchain.decode().strip() == 'leanprover/lean4:v4.34.0-rc2'
    parent = json.load(archive.extractfile('capture-manifest.json'))
    dependencies = []
    for module in re.findall(r'(?m)^import (\S+)', old.decode()):
        name = 'lean/' + module.replace('.', '/') + '.lean'
        raw = archive.extractfile(name).read()
        dependencies.append(dict(module=module, member=name, bytes=len(raw), sha256=sha(raw)))
before = b'    simp [hi, hj]'
after = b'    simp only [if_pos hi, if_neg hj, mul_zero]'
assert old.count(before) == 1
new = old.replace(before, after)
assert new.replace(after, before) == old
text = new.decode('utf-8')
assert not new.startswith(b'\xef\xbb\xbf') and '\ufffd' not in text
assert not re.search(r'\b(?:sorry|admit|axiom)\b', text)
headers = lambda t: [re.sub(r'\s+', ' ', x) for x in re.findall(r'(?ms)^(?:theorem|def)\s+\w+.*?(?=\s*:=)', t)]
assert headers(text) == headers(old.decode()) and len(headers(text)) == 11
assert len(re.findall(r'(?m)^theorem ', text)) == 10
scope = dict(sources=len(parent['project_sources']), requests=len(parent['requested_axioms']), stages=len(parent['stages']))
assert scope == dict(sources=369, requests=347, stages=7)
planpath = Path(r'C:\Users\dfred\Desktop\Projects\IGH\Quantyra-AI-Planning\docs\research\pvnp\full90-actual-rhs-numeric-no-obligations-2026-10-08.md')
plan = planpath.read_bytes()
heading = '## 2026-10-11 Full118 rank-Gram branch diagnosis and exact repair argument'
section = plan.decode('utf-8').split(heading, 1)[1].split('\n## ', 1)[0]
OUT.mkdir()
(OUT/'ExactRealRankGram.lean').write_bytes(new)
(OUT/'ExactRealRankGramChecks.lean').write_bytes(checks)
(OUT/'.gitattributes').write_text('* -text\n', encoding='utf-8', newline='\n')
(OUT/'ARGUMENT.md').write_text('# Full119 exact rank-Gram proof repair\n\nUNCOMPILED and UNACCEPTED.\n\n'+heading+section, encoding='utf-8', newline='\n')
(OUT/'source.diff').write_text(''.join(difflib.unified_diff(old.decode().splitlines(True), text.splitlines(True), fromfile='Full118', tofile='Full119')), encoding='utf-8', newline='\n')
files = [dict(path=p.name, bytes=p.stat().st_size, sha256=sha(p.read_bytes())) for p in sorted(OUT.iterdir())]
manifest = dict(schema=OUT.name, accepted=False, compiler_invoked=False,
    full118_input=dict(path=str(ARCHIVE), sha256=PIN), diagnostic_packet=str(PACKET),
    diagnostic_index_sha256=sha((PACKET/'index.json').read_bytes()),
    old_source_sha256=sha(old), new_source_sha256=sha(new), exact_inverse_reconstruction_passed=True,
    public_header_count=11, public_theorem_count=10, checks_unchanged=True,
    dependencies=dependencies, parent_scope=scope,
    planning_argument=dict(path=str(planpath), working_file_sha256=sha(plan), heading=heading,
        section_sha256=sha((heading+section).encode()), custody_copy='ARGUMENT.md'),
    toolchain=dict(value=toolchain.decode().strip(), sha256=sha(toolchain)),
    mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2',
    source_line_endings_preserved=True, warning_suppression_added=False, files=files)
(OUT/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(new), checks_sha256=sha(checks), manifest_sha256=sha((OUT/'manifest.json').read_bytes()), parent_scope=scope)))
