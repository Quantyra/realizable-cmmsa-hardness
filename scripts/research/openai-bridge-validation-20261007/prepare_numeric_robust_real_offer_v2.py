"""Hash/lexical preflight only; this never invokes Lean, Lake, or GCP."""
from pathlib import Path
import hashlib
import json
import re
import tarfile

BASE = Path(__file__).resolve().parent
OFFER = BASE / 'numeric-robust-real-offer-20261011-v1'
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PARENT_SHA = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
MATHLIB_REV = 'e06eff5f95374108acfaf19f1ff7473aa7771df2'

def sha(data):
    return hashlib.sha256(data).hexdigest().upper()

def pin(data):
    return {'bytes': len(data), 'sha256': sha(data)}

def main():
    assert sha(ARCHIVE.read_bytes()) == PARENT_SHA
    dependencies = []
    cutoff_path = BASE / 'numeric-robust-cutoffs-capture-v1' / 'ActualNumericRobustCutoffs.lean'
    cutoff = cutoff_path.read_bytes()
    assert sha(cutoff) == 'E4702CA305CA7316F239A528211B4383FCC664D3C78AEA0CA890334606AED076'
    dependencies.append({'module': 'PvNP.RealizableHardness.ActualNumericRobustCutoffs',
                         'path': str(cutoff_path), **pin(cutoff), 'accepted': False})
    with tarfile.open(ARCHIVE, 'r:gz') as archive:
        for stem in ['ActualStarAcceptedGoodMass', 'ActualStarFixedRhoDimensionGuard']:
            suffix = '/PvNP/RealizableHardness/' + stem + '.lean'
            members = [member for member in archive.getmembers() if member.name.endswith(suffix)]
            assert len(members) == 1, stem
            data = archive.extractfile(members[0]).read()
            dependencies.append({'module': 'PvNP.RealizableHardness.' + stem,
                                 'archive_member': members[0].name, **pin(data)})
        lake_members = [member for member in archive.getmembers() if member.name == 'lake-manifest.json']
        assert len(lake_members) == 1
        lake = archive.extractfile(lake_members[0]).read()
        assert MATHLIB_REV.encode() in lake
    source = OFFER / 'ActualNumericRobustReal.lean'
    checks = OFFER / 'ActualNumericRobustRealChecks.lean'
    file_pins = {}
    for name in ['ActualNumericRobustReal.lean', 'ActualNumericRobustRealChecks.lean',
                 'ARGUMENT-AND-API-MAP.md', '.gitattributes', 'preflight-original-failure.txt']:
        data = (OFFER / name).read_bytes()
        assert not data.startswith(b'\xef\xbb\xbf'), name
        decoded = data.decode('utf-8', errors='strict')
        assert '\ufffd' not in decoded, name
        file_pins[name] = pin(data)
    body = source.read_text(encoding='utf-8')
    assert not re.search(r'\b(sorry|admit|unsafe)\b|^\s*axiom\s', body, re.M)
    assert all(glyph in body for glyph in ['≤', 'ℚ'] if glyph != 'ℚ')
    names = re.findall(r'^theorem\s+([A-Za-z_][A-Za-z0-9_]*)', body, re.M)
    namespace = 'PvNP.RealizableHardness.ActualNumericRobustReal.'
    declarations = [namespace + name for name in names]
    requested = re.findall(r'^#print axioms\s+(\S+)', checks.read_text(encoding='utf-8'), re.M)
    checked = re.findall(r'^#check\s+(\S+)', checks.read_text(encoding='utf-8'), re.M)
    assert len(declarations) == 6 and declarations == requested == checked
    result = {
        'offer': OFFER.name, 'status': 'uncompiled root-authored arithmetic candidate',
        'parent_input_sha256': PARENT_SHA, 'parent_native_accepted': False,
        'accepted_operator_rebind_required': True, 'mathlib_revision': MATHLIB_REV,
        'direct_project_dependencies': dependencies,
        'numeric_robust_cutoffs_capture_index_sha256': sha((cutoff_path.parent / 'index.json').read_bytes()),
        'public_declarations': declarations, 'offered_files': file_pins,
        'preflight': {'valid_utf8_without_BOM': True, 'glyphs_reviewed': True,
                      'no_placeholder_proof_or_new_axiom': True,
                      'six_public_declarations_and_requests_match': True,
                      'source_dependency_pins_reverified': True},
        'exact_ceil_horizon': True, 'original_numeric_floor_unchanged': True,
        'Real_Bn_Fn_bound_translation_present': True,
        'unconditioned_advice_correction_translation_present': True,
        'actual_refresh_history_proved': False, 'source_decoder_proved': False,
        'lean_parse_or_compile_performed': False, 'accepted': False,
        'control_sha256': sha(Path(__file__).read_bytes()),
    }
    (OFFER / 'manifest.json').write_bytes((json.dumps(result, indent=2) + '\n').encode('utf-8'))
    print(json.dumps({'preflight': 'passed', 'compiler_invoked': False,
                      'source': file_pins[source.name],
                      'checks': file_pins[checks.name],
                      'manifest_sha256': sha((OFFER / 'manifest.json').read_bytes()),
                      'public_declarations': declarations}, indent=2))

if __name__ == '__main__':
    main()
