from pathlib import Path
import hashlib
import json
import tarfile

S = Path(__file__).resolve().parent
OUT = S / 'numeric-rational-decoder-offer-20261011-v1'
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PIN = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
REF = S / 'full107-trace-qualified-source-record-v1/review-sources/lean/PvNP/RealizableHardness'

def digest(data):
    return hashlib.sha256(data).hexdigest().upper()

assert not (OUT / 'manifest.json').exists(), 'Refuse to rewrite a stable offer'
with ARCHIVE.open('rb') as stream:
    assert hashlib.file_digest(stream, 'sha256').hexdigest().upper() == PIN
deps = []
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    for name in ['ZoomOutJoint.lean', 'ZoomOutPosterior.lean', 'ZoomOutTransfer.lean', 'GoodAdvice.lean', 'SamplerParameters.lean']:
        member = 'lean/PvNP/RealizableHardness/' + name
        raw = archive.extractfile(member).read()
        assert raw == (REF / name).read_bytes()
        deps.append({'member': member, 'bytes': len(raw), 'sha256': digest(raw)})
exports = ['exists_uniform_rational_threshold', 'agreement_after_exception', 'ready_joint_success_from_real_threshold']
checks = 'import PvNP.RealizableHardness.ActualRationalDecoderThreshold\n\n'
checks += ''.join('#print axioms PvNP.RealizableHardness.ActualRationalDecoderThreshold.' + n + '\n' for n in exports)
(OUT / 'Checks.lean').write_text(checks, encoding='utf-8', newline='\n')
argument = '''# One global rational decoder threshold

E002/S3137. Complete scalar/typed-interface argument; uncompiled source candidate.

The complete critical argument was recorded before translation in the planning note full90-actual-rhs-numeric-no-obligations-2026-10-08.md, section dated 2026-10-11 Decoder threshold and common-leaf coherence argument.

The inverse threshold e is a Real power. Its transverse original-table agreement is greater than e/2. Under the existing dimension guard the full-zoom exceptional mass (even with the manuscript's extra factor two) is at most 2^(-2h-3), which is at most e/8. Thus the full agreement exceeds 3e/8, and in particular e/3. This dimension/probability bound is an integration obligation, not a premise silently discharged by the present scalar module.

For 0<e<=1, rational density supplies C with e/5<C<e/3. It follows that 0<C<=1. This existential is outside every table, U, Q, and decoded-function choice, so one C can be fixed from the selected m,h. It preserves the rho-squared exponent margin; replacing e by only 2^(-2h) would not justify the later maximal-pair ladder threshold.

For the typed joint-law interface, retain the exact F,W,f and the same ambient, marginal, conditional and joint laws in ZoomOutJoint.ready_joint_success. If each favorable Q has Real ambient score at least e/3, then its rational score is at least C. If both native error guards are at most e/5, they are at most C. The original theorem therefore gives (ambient favorable mass minus its native bad-advice and TV charges)*(C/8) <= jointSuccess. Given a nonnegative lower bound p for that same mass difference, monotonicity gives p*(e/40) <= p*(C/8) <= jointSuccess. Nonnegativity of p is explicit: blindly replacing C in a product with a possibly negative mass difference would be invalid.

The three public statements are scalar rational choice, scalar exceptional-loss preservation, and the actual typed joint-law wrapper. The last still requires actual decoder F,W,f and its agreement/codimension bounds; this source does not construct those witnesses, discharge numerical source guards, prove source-NO, or replace the full decoder theorem. It does not change the frozen parent or choose a new threshold after a sample.

No Lean/Lake was invoked locally. Native GCP verification, axiom profiles and warning checks remain outstanding. Parent evidence is the preserved Full114 input, currently unaccepted; an execution package must rebind to the accepted operator successor.

Remaining to-do list: native verification; bind actual many-Q/H-extension output, numerical guards and same-joint-law decoder; complete source, runtime and certification obligations.
'''
(OUT / 'ARGUMENT.md').write_text(argument, encoding='utf-8', newline='\n')
(OUT / '.gitattributes').write_text('* -text\n', encoding='utf-8', newline='\n')
files = []
for path in sorted(OUT.iterdir()):
    raw = path.read_bytes()
    raw.decode('utf-8')
    assert not raw.startswith(b'\xef\xbb\xbf')
    files.append({'path': path.name, 'bytes': len(raw), 'sha256': digest(raw)})
source = (OUT / 'ActualRationalDecoderThreshold.lean').read_text(encoding='utf-8')
assert all(('theorem ' + name) in source for name in exports)
assert 'sorry' not in source and 'admit' not in source
manifest = {
    'schema': 'numeric-rational-decoder-offer-v1', 'status': 'uncompiled',
    'story': 'E002/S3137', 'author': '/root',
    'full114_archive': {'path': str(ARCHIVE), 'sha256': PIN},
    'mathlib_revision': 'e06eff5f95374108acfaf19f1ff7473aa7771df2',
    'dependencies': deps, 'public_axiom_requests': exports, 'files': files,
    'claims': 'Uniform scalar rational threshold and exact existing-joint-law interface; actual decoder witnesses remain explicit unfinished work.'
}
(OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8', newline='\n')
print(json.dumps({'source_sha256': digest(source.encode()), 'checks_sha256': digest(checks.encode()), 'manifest_sha256': digest((OUT/'manifest.json').read_bytes()), 'verified_dependencies': len(deps)}, indent=2))
