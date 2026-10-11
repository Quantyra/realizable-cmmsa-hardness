"""Derive complete scope preparation from the preserved real-scope control; no cloud/Lean."""
import ast
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE_PIN = '95E2A38E99B665EDFD2F1F7063288DF7ACB91D5BA7AA32739A2B640DED9C06E3'
CAPTURES = [
    ('operator-complete-offer-capture-v3', 'path', '3D892EAA6A8BF5103F4C697FCB862287A69D51BD32301575B0B37E2013E38173'),
    ('phi-eigenrelation-offer-capture-v4', 'copy', '3423358517781BCA5AD6220B131216293B9D3E19DC61A84F2D67D21AB09EB056'),
    ('real-gram-offer-capture-v1', 'path', '169D5BF3439215ACFA83B24D7A42DF0E398C53A5AF352B88FB0EC3202B49AA65'),
    ('complex-operator-complete-offer-capture-v4', 'path', 'DB7B77C3618AB6E94ECD761FAA7117810B7B56EB454B552DD4B74FA966AF3683'),
    ('complex-gram-offer-capture-v2', 'path', '81DE316ECEFC4DBD34744933566FFB93221857A7AF2128D92842A2BC805EEE24'),
]


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    old = (HERE / 'prepare_exact_real_operator_scope_v1.py').read_bytes()
    assert sha(old) == BASE_PIN
    for directory, _, pin in CAPTURES:
        assert sha((HERE / directory / 'index.json').read_bytes()) == pin
    source = old.decode('utf-8')
    old_loop = """    for directory, field in [('operator-complete-offer-capture-v3', 'path'),
                             ('phi-eigenrelation-offer-capture-v4', 'copy')]:
        index = json.loads((HERE / directory / 'index.json').read_bytes())"""
    new_loop = "    for directory, field, pin in " + repr(CAPTURES) + ":\n"
    new_loop += "        index_bytes = (HERE / directory / 'index.json').read_bytes()\n"
    new_loop += "        assert sha(index_bytes) == pin, 'Immutable capture index changed: ' + directory\n"
    new_loop += "        index = json.loads(index_bytes)"
    edits = [
        ('full-scope real operator successor', 'full-scope real/complex operator and Gram successor', 1),
        (old_loop, new_loop, 1),
        ('assert len(sources) == 13', 'assert len(sources) == 21', 1),
        ("assert len(b['project_sources']) == 361", "assert len(b['project_sources']) == 369", 1),
        ('exact-real-operator-full-scope-proposal-v1', 'complete-real-complex-operator-full-scope-proposal-v2', 2),
        ('complex_continuation_excluded_pending_source_repairs=True,',
         'exact_real_complex_operator_and_two_function_gram_source_offers=True,\n'
         '                  whole_complex_hypercontractivity_appendix_not_certified=True,', 1),
    ]
    for before, after, count in edits:
        assert source.count(before) == count
        source = source.replace(before, after)
    ast.parse(source)
    new = source.encode('utf-8')
    path = HERE / 'prepare_complete_operator_scope_v2.py'
    path.open('xb').write(new)
    record = dict(original='prepare_exact_real_operator_scope_v1.py', original_sha256=BASE_PIN,
                  successor=path.name, successor_sha256=sha(new),
                  replacements=[dict(before=a, after=b, count=c) for a, b, c in edits],
                  capture_index_pins={d: p for d, _, p in CAPTURES},
                  original_full109_parent348_261_configuration_and_native_gates_unchanged=True,
                  only_offered_scope_and_capture_index_pin_admission_expanded=True,
                  expected_project_sources=369, expected_added_sources=21,
                  scope_validation_not_yet_executed=True, cloud_operation=False, lean_executed=False,
                  accepted=False)
    (HERE / 'complete-operator-scope-control-derivation-v2.json').open('x', encoding='utf-8').write(json.dumps(record, indent=2) + '\n')
    print(json.dumps(dict(successor=path.name, sha256=sha(new), preparation_only=True)))


if __name__ == '__main__':
    main()
