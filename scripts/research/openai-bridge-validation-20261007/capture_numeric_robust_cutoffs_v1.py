"""Pin the exact selected-floor arithmetic translation; no Lean invocation."""
import hashlib
import json
from pathlib import Path
import re
import prepare_complete_numeric_scope_v2 as scope
from lean_source_static_preflight_v2 import inspect_bytes
from prepare_complete_operator_scope_v2 import imports, declarations

HERE = Path(__file__).resolve().parent


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    offer = HERE / 'numeric-robust-cutoffs-offer-v1'
    source_name = 'ActualNumericRobustCutoffs.lean'
    checks_name = 'ActualNumericRobustCutoffsChecks.lean'
    assert {p.name for p in offer.iterdir()} == {source_name, checks_name}
    source = (offer / source_name).read_bytes()
    checks = (offer / checks_name).read_bytes()
    old = scope.parent()
    added, _, _ = scope.additions()
    all_sources = old | added
    dependencies = []
    for module in imports(source):
        if module.startswith('PvNP.'):
            path = 'lean/' + module.replace('.', '/') + '.lean'
            raw = all_sources[path]
            dependencies.append(dict(module=module, path=path, bytes=len(raw), sha256=sha(raw)))
    indices = []
    for folder, pin in scope.CAPTURES:
        assert sha((HERE / folder / 'index.json').read_bytes()) == pin
        indices.append(dict(capture=folder, index_sha256=pin))
    requests = re.findall(r'(?m)^#print axioms\s+(\S+)', checks.decode())
    assert declarations(source) == requests and len(requests) == 2
    lexical = [inspect_bytes(source, source_name), inspect_bytes(checks, checks_name)]
    argument = '''# Existing numeric floor supplies robust-local arithmetic

Root recorded the complete argument in the planning numeric obligations note before this source was written. This module exports the seven exact natural-number guards for m>=256, h>=numericHnum(m), A>=1, then derives them for the same numericSourceFloor selector output. It introduces no new source floor or independently chosen height.

Hfinal=2*b*(N+2) dominates 2*b*m*(r+1). With b=4000*m^2 and r=10*m*b, this gives h>=b^2 and h>=8*(r+1). The elementary induction 2^q>=q+2 for q>=2 and the exact double exponential block formula give n=2*blocks(A,h)>=8*h^2. The remaining two ambient inequalities follow. Doubling the final guard avoids any integer division: 8*m*h<=h^2 and 2*(m+3*(r+1)+1)<=h, with h<=h^2, imply 4*m*h+m+3*(r+1)+1<=h^2. The selected wrapper uses the existing selected_numeric_height result and numericSourceBase_eq.

These guards imply the manuscript's extra arithmetic cutoffs by the argument in planning. This source does NOT yet formalize the Real inequality for B_n*F_n, the reciprocal-square threshold comparison, or the rational/Real probability subtraction. It does NOT construct a refresh product law, a successful adaptive history, distinct advice subspaces, a decoder or a source NO contradiction. Those exact consumers remain open. The source has not been parsed or compiled by Lean, and no kernel or independent-review acceptance is claimed.

The original operator-author follow-up failed before delivering a stable offer (request 7cef28cf-c1d6-496c-b448-953cbb7bb659; stream disconnected). Root then authored these disjoint source files. No interrupted author file was overwritten. Root is the sole compiler/Git owner; no local or GCP compiler was invoked here.
'''
    (offer / 'ARGUMENT-AND-API-MAP.md').open('xb').write(argument.encode())
    files = {p.name: p.read_bytes() for p in offer.iterdir()}
    manifest = dict(offer=offer.name, status='uncompiled root-authored candidate',
        parent_input_sha256=scope.INPUT_SHA, parent_manifest_sha256=scope.MANIFEST_SHA,
        direct_project_dependencies=dependencies, numeric_capture_indices=indices,
        public_declarations=requests, lexical_preflight=lexical,
        original_numeric_floor_unchanged=True, same_selector_output=True,
        seven_arithmetic_guards=True, refresh_history_or_decoder_proved=False,
        Real_Bn_Fn_bound_formalized=False,
        prior_author_failure=dict(request_id='7cef28cf-c1d6-496c-b448-953cbb7bb659',
            message='stream disconnected before completion: An error occurred while processing your request.',
            stable_offer_delivered=False),
        offered_files={n: dict(bytes=len(raw), sha256=sha(raw)) for n, raw in files.items()},
        control_sha256=sha(Path(__file__).read_bytes()), compiler_invoked=False, accepted=False)
    (offer / 'manifest.json').open('xb').write((json.dumps(manifest, indent=2) + '\n').encode())
    target = HERE / 'numeric-robust-cutoffs-capture-v1'
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_bytes(b'* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    rows = []
    for p in sorted(offer.iterdir()):
        raw = p.read_bytes()
        (target / p.name).open('xb').write(raw)
        assert (target / p.name).read_bytes() == p.read_bytes() == raw
        rows.append(dict(original=str(p), copy=p.name, bytes=len(raw), sha256=sha(raw)))
    report = dict(files=rows, requested_axioms=requests, lexical_preflight=lexical,
        actual_dependencies_reverified=True, complete_argument_recorded_before_translation=True,
        root_read_complete_source_and_selector_definitions=True,
        static_review_concerns=[], compiler_invoked=False, accepted=False,
        control_sha256=sha(Path(__file__).read_bytes()))
    data = (json.dumps(report, indent=2) + '\n').encode()
    (target / 'index.json').open('xb').write(data)
    print(json.dumps(dict(capture=target.name, source_sha256=sha(source), index_sha256=sha(data),
                         requests=len(requests), compiler_invoked=False)))


if __name__ == '__main__':
    main()
