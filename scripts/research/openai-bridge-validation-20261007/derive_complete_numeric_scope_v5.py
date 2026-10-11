"""Derive the nine-candidate static proposal, retaining all failed Full114 inputs."""
import ast
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    raw = (HERE / 'prepare_complete_numeric_scope_v3.py').read_bytes()
    assert sha(raw) == '274DBCDB511AD5772EE8746D773140DB863C91558EE54830F61B7F83D6165C7A'
    changes = [
        ('eight captured numeric, density and composition offers', 'nine captured numeric, density, composition and fixed-coordinate offers', 1),
        ('numeric-same-instance-composition-capture-v2', 'numeric-same-instance-composition-capture-v3', 1),
        ('48672D236093387B5D9E8C8AFF076F490EB9783A740B63761E804323974CA46D', '7499538C6B2BE856EB26C4D4F2B8B2F48844FFB26E64ED93089D1E0F518C19F1', 1),
        ("    ('numeric-physical-density-capture-v2', '6D95E2F441AB49926E359E8C444245915B738DAAB77FB1C2ABBBB1469B50C087'),",
         "    ('numeric-physical-density-capture-v4', 'E010176FB8A1353D70923DA51198ED457FE3DF51B3909B8A6E260CF713076B91'),\n    ('numeric-fixed-coordinate-inverse-capture-v3', 'EB080E7153B58F1E286358C7B46257C0BE85C1722E2C094939585287ACA7B17C'),", 1),
        ('len(sources) == 16', 'len(sources) == 18', 1),
        ('len(requests) == 34', 'len(requests) == 36', 1),
        ("len(b['project_sources']) == 385", "len(b['project_sources']) == 387", 1),
        ("len(b['requested_axioms']) == 381", "len(b['requested_axioms']) == 383", 1),
        ('project_sources=385', 'project_sources=387', 1),
        ('requested_profiles=381', 'requested_profiles=383', 1),
        ('dict(sources=385', 'dict(sources=387', 1),
        ('profiles=381', 'profiles=383', 1),
        ('complete-numeric-additive-scope-proposal-v3', 'complete-numeric-additive-scope-proposal-v4', 2),
        ('GCP-verify the complete same-instance Real inverse composition and physical-density consequence',
         'GCP-verify same-instance and fixed-coordinate Real inverse candidates and the physical same-witness row-validity consequence', 1),
        ('Manuscript-to-physical score transport, positive-mass robust-source overlap and SAT-derived source NO promise; no favorable table witness required',
         'Fixed-frame transport, robust refresh preservation and many-Q amplification with explicit cutoffs; same-law decoder and SAT-derived source NO promise; retain eligible-U mass', 1),
    ]
    text = raw.decode()
    for old, new, count in changes:
        assert text.count(old) == count, (old, text.count(old), count)
        text = text.replace(old, new)
    inverse = text
    for old, new, count in reversed(changes):
        assert inverse.count(new) == count
        inverse = inverse.replace(new, old)
    assert inverse.encode() == raw
    ast.parse(text)
    out = text.encode()
    (HERE / 'prepare_complete_numeric_scope_v4.py').open('xb').write(out)
    report = dict(parent_control_sha256=sha(raw), successor_control_sha256=sha(out),
        inverse_exact=True, changes=[dict(before=a, after=b, occurrences=c) for a,b,c in changes],
        parent_stays_Full114_failed_and_unaccepted=True,
        future_native_scope_must_rebind_to_actual_green_operator_package=True,
        no_execution_archive_or_compiler_or_cloud=True)
    data = (json.dumps(report, indent=2) + '\n').encode()
    (HERE / 'complete-numeric-scope-derivation-v4.json').open('xb').write(data)
    print(json.dumps(dict(control_sha256=sha(out), derivation_sha256=sha(data))))


if __name__ == '__main__':
    main()
