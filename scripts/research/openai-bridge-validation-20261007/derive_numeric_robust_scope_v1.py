"""Extend the exact static numeric proposal by the two robust arithmetic profiles."""
import ast
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    raw = (HERE / 'prepare_complete_numeric_scope_v4.py').read_bytes()
    assert sha(raw) == 'EF9816582792D298EF2459E753CA2ACEC7C12F6C412B0DF509774C22DFB121F0'
    changes = [
        ('nine captured numeric, density, composition and fixed-coordinate offers', 'ten captured numeric, density, inverse and robust arithmetic offers', 1),
        ("    ('numeric-fixed-coordinate-inverse-capture-v3', 'EB080E7153B58F1E286358C7B46257C0BE85C1722E2C094939585287ACA7B17C'),",
         "    ('numeric-fixed-coordinate-inverse-capture-v3', 'EB080E7153B58F1E286358C7B46257C0BE85C1722E2C094939585287ACA7B17C'),\n    ('numeric-robust-cutoffs-capture-v1', 'E1211C7F55353E7627026CB21A63E234971E724D07461EA5153066AFC3345139'),", 1),
        ('len(sources) == 18', 'len(sources) == 20', 1),
        ('len(requests) == 36', 'len(requests) == 38', 1),
        ("len(b['project_sources']) == 387", "len(b['project_sources']) == 389", 1),
        ("len(b['requested_axioms']) == 383", "len(b['requested_axioms']) == 385", 1),
        ('project_sources=387', 'project_sources=389', 1),
        ('requested_profiles=383', 'requested_profiles=385', 1),
        ('dict(sources=387', 'dict(sources=389', 1),
        (', profiles=383', ', profiles=385', 1),
        ('complete-numeric-additive-scope-proposal-v4', 'complete-numeric-additive-scope-proposal-v5', 2),
    ]
    text = raw.decode()
    for old, new, count in changes:
        assert text.count(old) == count, old
        text = text.replace(old, new)
    inverse = text
    for old, new, count in reversed(changes):
        assert inverse.count(new) == count, new
        inverse = inverse.replace(new, old)
    assert inverse.encode() == raw
    ast.parse(text)
    out = text.encode()
    (HERE / 'prepare_complete_numeric_scope_v5.py').open('xb').write(out)
    report = dict(parent_control_sha256=sha(raw), successor_control_sha256=sha(out),
        inverse_exact=True, changes=[dict(before=a, after=b, occurrences=c) for a,b,c in changes],
        parent_Full114_still_failed_unaccepted=True, no_execution_archive=True,
        robust_arithmetic_is_not_refresh_history_or_BnFn_Lean_proof=True,
        compiler_invoked=False)
    data = (json.dumps(report, indent=2) + '\n').encode()
    (HERE / 'numeric-robust-scope-derivation-v1.json').open('xb').write(data)
    print(json.dumps(dict(control_sha256=sha(out), derivation_sha256=sha(data))))


if __name__ == '__main__':
    main()
