"""Author only the warning repairs observed in additive Full92 modules."""
import hashlib
import json
from pathlib import Path
import re
from prepare_builder02_full90 import capsule

ROOT = Path('C:/Users/dfred/.quantyra/builder02/full92-source-size-profile-resource02')
DEST = Path(__file__).parent / 'full93-warning-candidate-v1'
PREFIX = 'lean/PvNP/RealizableHardness/'
EDITS = {
    'ActualSelectedComplementSourceSizeAppendMoment.lean': {
        143: [('have hsum :=', 'have _hsum :=')],
        144: [('have hbudget :=', 'have _hbudget :=')],
        243: [('have hsum :=', 'have _hsum :=')],
        244: [('have hbudget :=', 'have _hbudget :=')],
    },
    'ActualSelectedComplementSourceSizeAnalyticMoment.lean': {
        36: [('(hEven :', '(_hEven :')],
        47: [('(basisInv :', '(_basisInv :')],
        49: [('(hEven :', '(_hEven :'), ('(hi :', '(_hi :')],
        50: [('(hRho :', '(_hRho :')],
        51: [('(hc :', '(_hc :')],
        52: [('(hs :', '(_hs :')],
        53: [('(hHeight :', '(_hHeight :')],
        166: [('simp [hrank]', 'simp')],
        241: [('(hC :', '(_hC :')],
        512: [('field_simp [hden.ne\'] <;> ring', 'field_simp [hden.ne\']')],
        582: [('letI : Nonempty', 'let : Nonempty')],
        598: [('[ActualFixedFunctionalBinaryMatrixMoment.CoordinateAmbient,', '[ActualFixedFunctionalBinaryMatrixMoment.CoordinateAmbient]')],
        599: [('      Module.finrank_pi]', '')],
        906: [('by congr 1 <;> omega', 'by congr 1; omega')],
        1116: [('[ActualOrdinaryStarMatchingFiber.MatchesStar, T0,', '[ActualOrdinaryStarMatchingFiber.MatchesStar, T0]')],
        1117: [('      centerMatchBit, leafMatchBit]', '')],
    },
}


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def theorem_statements(text):
    pattern = r'(?m)^(?:(?:private|protected) )?(?:theorem|lemma) (\w+)\b'
    statements = {}
    for match in re.finditer(pattern, text):
        end = text.index(' := by', match.start())
        statements[match.group(1)] = text[match.start():end]
    return statements


def main():
    binding = json.loads((ROOT / 'resource-binding.json').read_bytes())
    assert sha((ROOT / 'input-archive.tar.gz').read_bytes()) == binding['files']['input-archive.tar.gz']
    files = capsule(ROOT / 'input-archive.tar.gz')
    manifest = json.loads(files['capture-manifest.json'])
    records = []
    candidates = []
    for name, edits in EDITS.items():
        rel = PREFIX + name
        old = files[rel]
        assert sha(old) == manifest['project_sources'][rel]['sha256']
        lines = old.decode().splitlines(keepends=True)
        replacements = []
        for line_no, pairs in edits.items():
            before = lines[line_no - 1]
            after = before
            for a, b in pairs:
                assert after.count(a) == 1, (name, line_no, a, after)
                after = after.replace(a, b, 1)
            lines[line_no - 1] = after
            replacements.append({'line': line_no, 'before': before, 'after': after})
        new = ''.join(lines).encode()
        inverse = new.decode().splitlines(keepends=True)
        for row in replacements:
            assert inverse[row['line'] - 1] == row['after']
            inverse[row['line'] - 1] = row['before']
        assert ''.join(inverse).encode() == old
        old_statements = theorem_statements(old.decode())
        new_statements = theorem_statements(new.decode())
        # hC is the only theorem-statement binder renamed; its premise stays.
        new_statements = {key: value.replace('(_hC :', '(hC :') for key, value in new_statements.items()}
        assert old_statements == new_statements, 'Theorem premise/conclusion drift'
        for contract in ['HC46ExactContract', 'Spectral47ExactContract']:
            if 'def ' + contract not in old.decode():
                continue
            start = old.decode().index('def ' + contract)
            end = old.decode().index('\ndef ', start + 4)
            before = old.decode()[start:end]
            start2 = new.decode().index('def ' + contract)
            end2 = new.decode().index('\ndef ', start2 + 4)
            after = new.decode()[start2:end2]
            for token in ['hEven', 'basisInv', 'hi', 'hRho', 'hc', 'hs', 'hHeight']:
                after = after.replace('(_' + token + ' :', '(' + token + ' :')
            assert before == after, 'Contract guard drift'
        candidates.append((name, new))
        records.append({'path': rel, 'old_sha256': sha(old), 'new_sha256': sha(new),
                        'bytes': len(new), 'edits': replacements,
                        'exact_inverse_byte_parity': True, 'theorem_statements_retained_modulo_hC_binder_name': True})
    DEST.mkdir()
    for name, data in candidates:
        (DEST / name).write_bytes(data)
    receipt = {'schema': 'full93-owned-warning-source-candidate-v1', 'parent_resource': str(ROOT),
               'parent_archive_sha256': binding['files']['input-archive.tar.gz'], 'sources': records,
               'observed_owned_warning_headers': 21, 'all_contract_guards_retained': True,
               'source_row_and_arity_roles_unchanged': True, 'new_linter_options_added': False,
               'native_warning_clearance_unverified': True, 'local_compilation': False,
               'accepted': False, 'launch_clearance': False}
    (DEST / 'derivation.json').write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'candidate': str(DEST), 'sources': 2, 'warnings_targeted': 21,
                      'mathematical_guards_retained': True, 'accepted': False}))


if __name__ == '__main__':
    main()
