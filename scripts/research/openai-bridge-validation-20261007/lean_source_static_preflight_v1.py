"""Small lexical preflight for offered bytes. This is NOT a Lean parser/compiler."""
import hashlib
import json
from pathlib import Path
import re
import sys


def code_only(text):
    """Blank strings/quoted identifiers and nested comments; preserve positions."""
    out = list(text)
    pos = 0
    while pos < len(text):
        start = pos
        if text.startswith('--', pos):
            end = text.find('\n', pos)
            pos = len(text) if end < 0 else end
        elif text.startswith('/-', pos):
            depth = 1
            pos += 2
            while depth:
                if pos >= len(text):
                    raise ValueError('Unterminated block comment')
                if text.startswith('/-', pos):
                    depth += 1
                    pos += 2
                elif text.startswith('-/', pos):
                    depth -= 1
                    pos += 2
                else:
                    pos += 1
        elif text[pos] in ('"', '«'):
            closing = '"' if text[pos] == '"' else '»'
            pos += 1
            while pos < len(text) and text[pos] != closing:
                pos += 2 if closing == '"' and text[pos] == '\\' else 1
            if pos >= len(text):
                raise ValueError('Unterminated string or quoted identifier')
            pos += 1
        else:
            pos += 1
            continue
        for j in range(start, pos):
            if out[j] != '\n':
                out[j] = ' '
    return ''.join(out)


def inspect_bytes(data, label):
    if data.startswith(b'\xef\xbb\xbf'):
        raise ValueError(f'{label}: UTF-8 BOM')
    text = data.decode('utf-8')
    if any(bad in text for bad in ('\ufffd', '\u00e2\u2020', '\u00c3\u00a2')):
        raise ValueError(f'{label}: known glyph corruption')
    code = code_only(text)
    forbidden = re.search(r'\b(?:sorry|admit)\b|(?m:^\s*(?:private\s+|protected\s+)?axiom\s)', code)
    if forbidden:
        raise ValueError(f'{label}: forbidden proof token at offset {forbidden.start()}')
    if re.search(r'(?m)^\s*set_option\s+linter\.', code):
        raise ValueError(f'{label}: owned linter option requires explicit review')
    pairs = {'(': ')', '[': ']', '{': '}', '⟨': '⟩'}
    stack = []
    for pos, char in enumerate(code):
        if char in pairs:
            stack.append((char, pos))
        elif char in pairs.values():
            if not stack or pairs[stack[-1][0]] != char:
                raise ValueError(f'{label}: unmatched {char} at line {code.count(chr(10), 0, pos) + 1}')
            stack.pop()
    if stack:
        char, pos = stack[-1]
        raise ValueError(f'{label}: unclosed {char} at line {code.count(chr(10), 0, pos) + 1}')
    return dict(path=label, bytes=len(data), sha256=hashlib.sha256(data).hexdigest().upper(),
                lexical_preflight_passed=True, lean_parse_or_compile_performed=False)


def main():
    files = []
    for arg in sys.argv[1:]:
        p = Path(arg)
        files.extend(sorted(p.glob('*.lean')) if p.is_dir() else [p])
    assert files, 'At least one offered Lean source is required'
    results, errors = [], []
    for p in files:
        try:
            results.append(inspect_bytes(p.read_bytes(), str(p)))
        except (ValueError, UnicodeError) as error:
            errors.append(str(error))
    print(json.dumps(dict(files=results, errors=errors, lean_executed=False), ensure_ascii=True))
    raise SystemExit(bool(errors))


if __name__ == '__main__':
    main()
