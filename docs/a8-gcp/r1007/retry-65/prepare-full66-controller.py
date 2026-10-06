from pathlib import Path
import json,ast
R=Path.cwd();P=R/'docs/a8-gcp/r1007';A=P/'retry-65';B=P/'retry-66'
s=(A/'controller.py').read_text(encoding='utf-8')
s=s.replace("['RealQNorm','RealQTransport','A22OperatorLq']","['RealQNorm','RealQTransport','A22OperatorLq','A22ParentFactorization','A22OriginalInduction','OriginalExactInhabitant']")
s=s.replace("CRITICAL=[", "OWNED+=['lean/PvNP/RealizableHardness/ActualSelectedComplementHC46OriginalApplication'+z+'.lean' for z in ['', 'Checks']]\nCRITICAL=[",1)
a=s.index('CANDIDATE_DIRS=');b=s.index('\ndef module(',a)
s=s[:a]+'''CANDIDATE_DIR=PACKAGE/'retry-65/coherent-full-a22-hc46-offer'
def candidate_bytes(rel):
    if rel not in OWNED[-14:]: return (REPO/rel).read_bytes()
    return (CANDIDATE_DIR/Path(rel).name).read_bytes()
'''+s[b:]
s=s.replace('retry-65','retry-66').replace('development65_import','full66_import').replace('capture-development-65c','capture-full-a22-hc46-66')
s=s.replace("CANDIDATE_DIR=PACKAGE/'retry-66/coherent-full-a22-hc46-offer'","CANDIDATE_DIR=PACKAGE/'retry-65/coherent-full-a22-hc46-offer'")
s=s.replace("PRIOR='cmmsa_a8_output_20261006T113644Z_145e9858'","PRIOR='cmmsa_a8_output_20261006T123622Z_1dfa244e'")
s=s.replace('OWNED[-6:]', 'OWNED[-14:]').replace('OWNED[-6::2]','OWNED[-14::2]').replace('OWNED[-5::2]','OWNED[-13::2]')
s=s.replace("priorcap=PACKAGE/'captures/capture-integrated-64'","priorcap=PACKAGE/'captures/capture-development-65c'")
s=s.replace("==221","==304")
s=s.replace("previous/'full-original-a20-a21-native-gates.json'","previous/'qualified-prior85-native-evidence.json'").replace("['full_original_A20_A21_native_gates_green']","['prior85_profiles_standard']")
s=s.replace('len(records) - 13, "check_modules": 13','len(records) - 17, "check_modules": 17')
s=s.replace("common.CLAIM='Development only: stable RealQNorm/RealQTransport/A22OperatorLq plus exact prior85 accepted graph; incomplete Parent and A22/HC46 consumers excluded. Full original A22/HC46 remains required; no helper or milestone acceptance.'","common.CLAIM='Full original A22, unchanged unrestricted-eta HC46ExactContract inhabitant and actual selected consumer without hHC; prior85 refreshed. Native development evidence only until full gates and mathematical reviews.'")
s=s.replace("'development-realq-core-source'","'full-original-A22-HC46-selected-source'").replace("'development-realq-core-checks'","'full-original-A22-HC46-selected-checks'")
ast.parse(s);(B/'controller.py').write_text(s,encoding='utf-8')
for name in ['current-warning-baseline.json','current-dependency-pins.json','accepted-a9-source.lean.snapshot','supplemental-inherited-coverage-baseline.json']:(B/name).write_bytes((A/name).read_bytes())
objects=json.loads((P/'runs/cmmsa_a8_output_20261006T123622Z_1dfa244e/remote-evidence/object-after.json').read_bytes());manifest=json.loads((P/'captures/capture-development-65c/manifest.json').read_bytes())
owned=json.loads((A/'coherent-full-a22-hc46-offer/custody.json').read_bytes())['files'];priorowned=[r['owner_file'] for r in json.loads((A/'axiom-declaration-owner-map.json').read_bytes())['requests'] if r['basis']=='accepted-frozen64-original85'];excluded=set(owned)|set(priorowned)|{n.replace('.lean','Checks.lean') for n in priorowned}|{'lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A9AmbientReindex.lean'}
sources={n:r for n,r in manifest['project_sources'].items() if n not in excluded};stems={'.lake/build/lib/lean/'+n.removeprefix('lean/').removesuffix('.lean')+'.olean' for n in sources};cache={n:h for n,h in objects.items() if any(n==t or n.startswith(t+'.') for t in stems)}
(B/'cache-scope-preview.json').write_text(json.dumps({'sources':len(sources),'objects':len(cache),'source_pins':sources,'object_pins':cache,'accepted':False},indent=2)+'\n',encoding='utf-8')
print('Full66 controller AST valid; cache preview',len(sources),len(cache))
