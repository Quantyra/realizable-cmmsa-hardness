"""Separate warning-only proof successor from actual frozen native diagnostics."""
import json
import re
import tarfile
from pathlib import Path
from prepare_sourcesize_spectral_application import HERE, sha

PARENT = Path('C:/Users/dfred/.quantyra/builder02/full101-spectral-original-application-resource02')
ROOT = HERE / 'full101-owned-warning-repair-candidate-v1'
EDITS = {
 'ActualFiniteBinarySurjectionCounting': {80: [('letI', 'let')], 115: [('letI', 'let')]},
 'ActualFiniteBinaryImageOrbit': {49: [(', smul_add', '')], 59: [('[hr_app]', '')]},
 'ActualFiniteAppendSpectral47': {210: [(', baseFrequencyPart', '')], 353: [(", Finset.sum_ite_eq'", '')]},
 'ActualFiniteBinaryImageFibres': {74: None, 78: None, 102: [(', LinearMap.codRestrict_apply', '')],
   212: [(', LinearMap.comp_apply', '')], 224: [('<;>', ';')], 225: [('<;>', ';')],
   240: [(', LinearMap.comp_apply', '')]},
 'ActualFiniteAppendImageWeighted': {111: [(', Nat.mul_comm', '')], 136: [('letI', 'let')]},
 'ActualFiniteAppendImageTailBridge': {48: [('[hk, ', '['), (', Pi.single_apply', '')],
   52: [('[hk, ', '[')], 62: [("[Pi.single_apply, eq_comm, Finset.sum_ite_eq']", '[Pi.single_apply]')],
   106: [('simpa', 'simp')], 139: [('simpa using congrArg Prod.snd', 'simp')], 140: None},
 'ActualFiniteAppendImagePerImageEnergy': {68: [('  have hconst', '  have _ := hE\n  have hconst')]},
 'ActualFiniteAppendGlobalImageEnergy': {68: [('letI', 'let')],
   241: [('  classical', '  classical\n  have _ := basisInv')], 242: [('letI', 'let')]},
}


def main():
    manifest = json.loads((PARENT / 'capture-manifest.json').read_bytes())
    marker = json.loads((PARENT / 'launch-once.json').read_bytes())
    qualified = Path(marker['preflight'])/'qualified-native'/marker['run']/'material-expanded-native-report.json'
    report = json.loads(qualified.read_bytes())
    assert report['owned_warning_headers'] == [0,0,0,0,26,26,0]
    assert not report['full101_expanded_native_gates_green']
    ROOT.mkdir(exist_ok=True)
    records = []
    with tarfile.open(PARENT / 'input-archive.tar.gz') as archive:
        for module, changes in EDITS.items():
            rel='lean/PvNP/RealizableHardness/'+module+'.lean'
            data=archive.extractfile(rel).read()
            assert sha(data)==manifest['project_sources'][rel]['sha256']
            lines=data.decode().splitlines(keepends=True)
            edits=[]
            for number, replacements in changes.items():
                old=lines[number-1]
                if replacements is None:
                    # Retain the constructor bullet when removing a redundant change.
                    lines[number-1]=old[:old.index('·')+1]+'\n' if '·' in old else ''
                else:
                    new=old
                    for a,b in replacements:
                        assert new.count(a)==1,(module,number,a)
                        new=new.replace(a,b)
                    lines[number-1]=new.rstrip()+'\n'
                edits.append(dict(original_line=number,before=old,after=lines[number-1]))
            result=''.join(lines).encode()
            def declared_headers(source):
                text=source.decode()
                starts=list(re.finditer(r'(?m)^(?:(?:private|noncomputable|protected) )?(?:theorem|def|instance|abbrev)\b',text))
                return [text[m.start():text.index(':=',m.start())] for m in starts]
            assert declared_headers(data)==declared_headers(result),module
            assert not re.search(r'(?m)^\s*set_option linter\.',result.decode())
            path=ROOT/(module+'.lean')
            if path.exists():assert path.read_bytes()==result
            else:path.write_bytes(result)
            records.append(dict(path=rel,original_sha256=sha(data),sha256=sha(result),bytes=len(result),edits=edits,
                                all_declaration_headers_preserved=True,no_linter_disable_added=True))
    value=dict(schema='full101-owned-warning-repair-candidate-v1', parent_run=marker['run'],
               parent_qualification_sha256=sha(qualified.read_bytes()), files=records,
               remaining_repairs=[], all26_native_warning_headers_addressed=True,
               complete_warning_repair_unproven_until_native_run=True, compiler_invoked=False, native_verified=False,
               frozen_full101_modified=False, accepted=False)
    b=(json.dumps(value,indent=2)+'\n').encode()
    (ROOT/'derivation.json').write_bytes(b)
    print(json.dumps(dict(files=len(records),remaining_repairs=value['remaining_repairs'],native_verified=False)))


if __name__=='__main__':main()
