from pathlib import Path
import hashlib
import json
import re
import tarfile

S = Path(__file__).resolve().parent
OUT = S / 'numeric-complement-mass-offer-20261011-v1'
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PIN = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
REF = S / 'full107-trace-qualified-source-record-v1/review-sources'
sha = lambda raw: hashlib.sha256(raw).hexdigest().upper()
assert not (OUT/'manifest.json').exists()
assert sha(ARCHIVE.read_bytes()) == PIN
deps = []
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    for name in ['ActualFiniteLaw', 'ActualChangedAmbient8SBoundary', 'ActualTaggedConcreteStarLaw',
                 'ActualTaggedComplementIncidence', 'ActualTaggedComplementStarDensityBridge',
                 'ActualTaggedOrderedSampleNonempty', 'ActualSourceStarLaw']:
        member = 'lean/PvNP/RealizableHardness/' + name + '.lean'
        raw = archive.extractfile(member).read()
        assert raw == (REF/member).read_bytes()
        deps.append(dict(member=member, sha256=sha(raw), bytes=len(raw)))
candidate = S/'actual-global-density-bridge-offer-v2/ActualGlobalDensityBridge.lean'
candidate_pin = '642C3CA24DB6247C7797444BD02951173F43BA3249968EC40BFD8987A2898C7E'
assert sha(candidate.read_bytes()) == candidate_pin
argument = S/'numeric-refresh-argument-offer-20261011-v1/ARGUMENT.md'
argument_pin = '6C05AEBB2FCFE008EA6C7458367CDE24CA08C032A121A63AA7958589850B5DC7'
assert sha(argument.read_bytes()) == argument_pin
assert 'complements' in argument.read_text(encoding='utf-8')
source = (OUT/'ActualComplementDensityMass.lean').read_bytes()
code = source.decode('utf-8')
assert not re.search(r'\b(?:sorry|admit|axiom)\b', code)
exports = re.findall(r'(?m)^theorem (\w+)', code)
definitions = re.findall(r'(?m)^def (\w+)', code)
assert len(exports) == 7
assert len(definitions) == 2
checks = 'import PvNP.RealizableHardness.ActualComplementDensityMass\n\n'
checks += ''.join('#check PvNP.RealizableHardness.ActualComplementDensityMass.'+n+'\n' for n in definitions)
checks += ''.join('#print axioms PvNP.RealizableHardness.ActualComplementDensityMass.'+n+'\n' for n in exports)
(OUT/'Checks.lean').write_text(checks, encoding='utf-8', newline='\n')
explanation = '''# Actual unconditioned complement-density mass

E002/S3137. This translates the complete complement-averaging step in the already captured refresh argument, SHA 6C05AEBB2FCFE008EA6C7458367CDE24CA08C032A121A63AA7958589850B5DC7, paragraph beginning If the mean initial ordinary density over complements is at least 8S. The exact distinct-advice incidence and original-law averaging argument is recorded at planning 50e29d8. This candidate is uncompiled.

The actual StarDensity is an expectation of a zero-one indicator under a uniform center followed by a full ordered tuple of uniform extensions. Explicit nonempty hypotheses make both laws normalized; their product kernel sums to one. Pointwise nonnegative indicator bounds imply 0<=density<=1, including the zero-occurrence case. No conditional leaf law is substituted.

For the actual good U, at least one side complement exists by constructing a zero-dimensional side center and using the actual positive SideComplementOver count. originalComplementLaw is the uniform law on ALL these complements. Its mass is exactly reciprocal total cardinality and its definition contains no success predicate.

The pinned sideConditionalDensity_eq_ordinaryComplementStarDensity identifies the original side law with the actual complement-first experiment. Expanding its finite sums gives the original-law expectation of complementFullAcceptMass. The global-density bridge's public pointwise acceptance-inclusion theorem bounds each such mass by the transported ordinary StarDensity for the SAME source and globally predrawn center/leaf tables. Hence side density is at most the original complement expectation of those ordinary densities.

Define G by ordinary density >=4S. For S>=0 and each actual complement A, density(A)<=4S+1_G(A): good fibers have density<=1 and bad fibers have density<4S. Multiplying by the original nonnegative weights and summing gives meanDensity<=4S+mass(G). Under the original side-density premise >=8S, therefore mass(G)>=4S. All complements remain in the original denominator. This is a positive-mass result; it does not merely select one favorable complement, and it never conditions the law on G.

Seven actual Full114 dependency sources and the uncompiled global-density-v2 source are hash-pinned. The source has seven public axiom requests and two definition checks. No Lean/Lake ran locally. Full114 is an unaccepted parent; future native execution must rebind to the accepted operator successor with full retained scope.

This supplies the complement mass to combine with local distinct-Q fractions and finite dimension averaging. It does not discharge the local Gaussian/preservation/inverse proofs, identify the final all-Q source law, build the legitimate decoder or prove the source NO promise. Random-history, runtime and final certification remain explicit.

Remaining to-do list: combine same-table coordinate transport, local robust counting and original-law averaging; GCP kernel/axiom/warning verification; actual source decoder/NO, random-history, runtime and all certification gates.
'''
(OUT/'ARGUMENT.md').write_text(explanation, encoding='utf-8', newline='\n')
(OUT/'.gitattributes').write_text('* -text\n', encoding='utf-8', newline='\n')
files = []
for path in sorted(OUT.iterdir()):
    raw = path.read_bytes()
    assert not raw.startswith(b'\xef\xbb\xbf') and '\ufffd' not in raw.decode('utf-8')
    files.append(dict(path=path.name, sha256=sha(raw), bytes=len(raw)))
manifest = dict(schema='numeric-complement-mass-offer-v1', author='/root', story='E002/S3137',
    accepted=False, compiler_invoked=False, full114_archive=dict(path=str(ARCHIVE), sha256=PIN),
    dependencies=deps, candidate_dependencies=[dict(path=str(candidate), sha256=candidate_pin,
        module='ActualGlobalDensityBridge', status='uncompiled')],
    complete_argument=dict(path=str(argument), sha256=argument_pin),
    mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2', public_axiom_requests=exports,
    checked_definitions=definitions, files=files)
(OUT/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(source), checks_sha256=sha(checks.encode()),
    manifest_sha256=sha((OUT/'manifest.json').read_bytes()), exports=exports), indent=2))
