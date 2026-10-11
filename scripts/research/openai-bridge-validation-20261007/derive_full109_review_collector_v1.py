"""Rebind the unchanged native review collector to the actual Full109 packets."""
import ast
import json
from pathlib import Path
from custody_checks import digest

HERE = Path(__file__).resolve().parent


def main():
    parent = HERE/'preserve_full107_material_integration_v4.py'
    original = parent.read_text(encoding='utf-8')
    changes = [
        ('Full107 v4', 'Full109 v1'),
        ('audit_full107_prior_review_reuse', 'audit_full109_prior_review_reuse_v1'),
        ("BASE/'material-integration-v4'", "BASE/'material-integration-v1'"),
        ('full107-material-integration-reports-v4', 'full109-material-integration-reports-v1'),
        ('full107-independent-material-integration-terminal-v4', 'full109-independent-material-integration-terminal-v1'),
    ]
    successor = original
    for old, new in changes:
        assert successor.count(old) == 1
        successor = successor.replace(old, new)
    restored = successor
    for old, new in reversed(changes):
        assert restored.count(new) == 1
        restored = restored.replace(new, old)
    assert restored == original
    ast.parse(successor)
    target = HERE/'preserve_full109_material_integration_v1.py'
    target.open('x', encoding='utf-8', newline='\n').write(successor)
    record = dict(parent_sha256=digest(parent), successor_sha256=digest(target),
                  shared_collector_sha256=digest(HERE/'preserve_full90_material_review_terminal.py'),
                  replacements=changes, exact_inverse_verified=True,
                  native_prompt_model_context_and_output_checks_unchanged=True,
                  actual_reviews_executed=False, accepted=False)
    (HERE/'full109-review-collector-derivation-v1.json').open('x', encoding='utf-8', newline='\n').write(json.dumps(record, indent=2)+'\n')
    print(json.dumps(record))


if __name__ == '__main__':
    main()
