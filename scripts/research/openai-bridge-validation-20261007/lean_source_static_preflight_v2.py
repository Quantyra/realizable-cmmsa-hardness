"""Extend the preserved lexical preflight with a bare-question-mark glyph-loss guard."""
import re
from lean_source_static_preflight_v1 import code_only, inspect_bytes as inspect_v1


def inspect_bytes(data, label):
    result = inspect_v1(data, label)
    code = code_only(data.decode('utf-8'))
    # Named metavariables (?h) and tactic holes (?_) remain valid Lean tokens.
    # A standalone '?' is neither and caught an actual Windows encoding failure.
    match = re.search(r'(?<![\w?])\?(?![\w?])', code)
    if match:
        line = code.count('\n', 0, match.start()) + 1
        raise ValueError(f'{label}: bare question mark / possible lost glyph at line {line}')
    result['bare_question_mark_guard_passed'] = True
    return result
