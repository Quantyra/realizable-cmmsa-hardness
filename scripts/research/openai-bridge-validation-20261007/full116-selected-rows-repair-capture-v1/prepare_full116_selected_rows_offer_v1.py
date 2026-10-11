"""Prepare a disjoint source-only repair from exact Full115 input; no Lean."""
from pathlib import Path
import difflib
import hashlib
import json
import re
import tarfile

S = Path(__file__).resolve().parent
OUT = S / 'full116-selected-rows-repair-v1'
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full115-exact-real-complex-operators-repair5-resource02\input-archive.tar.gz')
PIN = 'BE4A4F7223E09B0E05EFC62D4AB242F686C9E4BB6F265F5AB95F0F984E856A5E'
SOURCE = 'lean/PvNP/RealizableHardness/RectangularGLSelectedRows.lean'
PACKET = S / 'full115-native-diagnostic-packet-v1'

def sha(raw):
    return hashlib.sha256(raw).hexdigest().upper()

assert not OUT.exists(), 'Never overwrite an offer'
assert sha(ARCHIVE.read_bytes()) == PIN
assert sha((PACKET / 'index.json').read_bytes()) == '67A53045B3990D3B8304B7B574192E43292909D0C55ED26C100A63E676C7811A'
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    old = archive.extractfile(SOURCE).read()
    assert old == (PACKET / 'RectangularGLSelectedRows.lean').read_bytes()
    checks = archive.extractfile(SOURCE.replace('.lean', 'Checks.lean')).read()
    prefix = archive.extractfile('lean/PvNP/RealizableHardness/RectangularGLRowCompletion.lean').read().decode()
    dependencies = []
    for name in ['RectangularGLRowCompletion', 'RectangularFrameFiberAverage', 'BinaryMatrixRightOrbit']:
        member = 'lean/PvNP/RealizableHardness/' + name + '.lean'
        raw = archive.extractfile(member).read()
        dependencies.append(dict(member=member, bytes=len(raw), sha256=sha(raw)))
    parent_manifest = json.load(archive.extractfile('capture-manifest.json'))
new = old.decode()
bad_inverse = '''  · intro w
    apply Subtype.ext
    apply Subtype.ext
    ext <;> simp [Matrix.mul_assoc, hTS, hST]
  · intro w
    apply Subtype.ext
    apply Subtype.ext
    ext <;> simp [Matrix.mul_assoc, hTS, hST]
'''
good_inverse = prefix[prefix.index('  · intro w\n    apply Subtype.ext\n    apply Subtype.ext\n    apply Prod.ext'):prefix.index('\n/-- Chosen fibre equivalence')]
assert new.count(bad_inverse) == 1
new = new.replace(bad_inverse, good_inverse)
anchor = '/-- The normalized selected-row marginal'
helper = '''private noncomputable def selectedMap_fiber_equiv {k d : Nat}
    (P : BinaryMatrix k d) (hP : Function.Surjective (Matrix.toLin' P))
    (X Y : FullRowFrame k d) :
    RectangularFrameFiberAverage.Fiber (selectedRowsMap P hP) X ≃
      RectangularFrameFiberAverage.Fiber (selectedRowsMap P hP) Y := by
  let hX : RectangularFrameFiberAverage.Fiber (selectedRowsMap P hP) X ≃
      SelectedFiber P X.1 := selectedMapFiberEquiv P hP X
  let hXY : SelectedFiber P X.1 ≃ SelectedFiber P Y.1 :=
    selectedFiber_equiv P X.1 Y.1 X.2 Y.2
  let hY : RectangularFrameFiberAverage.Fiber (selectedRowsMap P hP) Y ≃
      SelectedFiber P Y.1 := selectedMapFiberEquiv P hP Y
  exact hX.trans (hXY.trans hY.symm)

private theorem selectedMap_fiber_card_eq {k d : Nat}
    (P : BinaryMatrix k d) (hP : Function.Surjective (Matrix.toLin' P))
    (X Y : FullRowFrame k d) :
    Fintype.card (RectangularFrameFiberAverage.Fiber (selectedRowsMap P hP) X) =
      Fintype.card (RectangularFrameFiberAverage.Fiber (selectedRowsMap P hP) Y) := by
  exact Fintype.card_congr (selectedMap_fiber_equiv P hP X Y)

'''
new = new.replace(anchor, helper + anchor, 1)
begin = new.index('  classical\n', new.index('theorem selected_rows_uniform_mean'))
end = new.index('\n/-- Direct bottom-s-row selector.', begin)
new = new[:begin] + '''  classical
  let f : InversePair d → FullRowFrame k d := selectedRowsMap P hP
  let X₀ : FullRowFrame k d := ⟨P, hP⟩
  let k₀ := Fintype.card (RectangularFrameFiberAverage.Fiber f X₀)
  have hf : Function.Surjective f := selectedRowsMap_surjective P hP
  have hbase : Nonempty (RectangularFrameFiberAverage.Fiber f X₀) := by
    obtain ⟨U, hU⟩ := hf X₀
    exact ⟨⟨U, hU⟩⟩
  have hk₀ : 0 < k₀ := by
    change 0 < Fintype.card (RectangularFrameFiberAverage.Fiber f X₀)
    exact Fintype.card_pos_iff.mpr hbase
  let hNonempty : Nonempty (FullRowFrame k d) := ⟨X₀⟩
  have hcard : ∀ X : FullRowFrame k d,
      Fintype.card (RectangularFrameFiberAverage.Fiber f X) = k₀ := by
    intro X
    change Fintype.card (RectangularFrameFiberAverage.Fiber (selectedRowsMap P hP) X) =
      Fintype.card (RectangularFrameFiberAverage.Fiber (selectedRowsMap P hP) X₀)
    exact selectedMap_fiber_card_eq P hP X X₀
  have hcardNat : ∀ X : FullRowFrame k d,
      Nat.card (RectangularFrameFiberAverage.Fiber f X) = k₀ := by
    intro X
    simpa only [← Nat.card_eq_fintype_card] using hcard X
  have hmap :
      (∑ U : InversePair d, g (f U)) / (Fintype.card (InversePair d) : Real) =
        (∑ X : FullRowFrame k d, g X) / (Fintype.card (FullRowFrame k d) : Real) :=
    @RectangularFrameFiberAverage.uniformMean_map_of_equipotent_fibers
      (InversePair d) (FullRowFrame k d)
      inferInstance inferInstance hNonempty f k₀ hk₀
      (by
        intro X
        simpa only [← Nat.card_eq_fintype_card] using hcardNat X)
      g
  exact hmap
''' + new[end:]
for pattern in [r'(?m)^import .+$', r'(?m)^set_option .+$']:
    assert re.findall(pattern, old.decode()) == re.findall(pattern, new)
assert 'sorry' not in new and 'admit' not in new
assert not new.encode().startswith(b'\xef\xbb\xbf') and '\ufffd' not in new
OUT.mkdir()
(OUT / 'RectangularGLSelectedRows.lean').write_bytes(new.encode())
(OUT / 'RectangularGLSelectedRowsChecks.lean').write_bytes(checks)
(OUT / '.gitattributes').write_text('* -text\n', encoding='utf-8', newline='\n')
argument = '''# Full116 selected-row repair

E002/S3137. Source-only routine repair, uncompiled. All original public statements, imports, Checks and options remain. No resource limit, warning policy or parent scope is relaxed.

Full115 stages 0-3 passed, then selected-row transporter inverse laws left the second matrix component unsolved and uniform marginal normalization timed out. The exact failed input and untruncated diagnostics remain in full115-native-diagnostic-packet-v1.

The inverse map is the same paired right/left multiplication. On the first component, associate (U*T)*S to U*(T*S); on the second, associate T*(S*V) to (T*S)*V. The reverse direction uses S*T=1. Explicit product extensionality and these four equalities replace the failed simplifier. The same proof was inspected in the exact Full115 RectangularGLRowCompletion dependency.

For uniform selected-row means, the map is onto and all fibers are equivalent by composition with the same transporter. Separate private definitions preserve this argument while reducing repeated elaboration. Remove shadow Fintype instances; pass the codomain Nonempty proof explicitly. Transport only fiber cardinalities through Nat.card to the consumer's exact Fintype instance, then apply the unchanged normalized finite-fiber averaging theorem. Zero row/dimension cases remain included. The theorem still assumes only surjectivity of P and concludes the original full normalized marginal.

This repairs elaboration and inverse algebra, not the mathematical target or theorem hypotheses. It is not native acceptance. Sol must preserve Full115 terminal/stop/audit and capture this offer before packaging unchanged 369-source/347-request/seven-stage Full116.

Remaining to-do list: GCP kernel/axiom/no-regression verification and the complete existing manuscript certification scope.
'''
(OUT / 'ARGUMENT.md').write_text(argument, encoding='utf-8', newline='\n')
(OUT / 'source.diff').write_text(''.join(difflib.unified_diff(old.decode().splitlines(True), new.splitlines(True), fromfile='Full115', tofile='Full116')), encoding='utf-8', newline='\n')
files = [dict(path=p.name, bytes=p.stat().st_size, sha256=sha(p.read_bytes())) for p in sorted(OUT.iterdir())]
manifest = dict(schema='full116-selected-rows-offer-v1', accepted=False, compiler_invoked=False,
    full115_input=dict(path=str(ARCHIVE), sha256=PIN), old_source_sha256=sha(old), new_source_sha256=sha(new.encode()),
    diagnostic_packet=str(PACKET), diagnostic_index_sha256=sha((PACKET/'index.json').read_bytes()),
    dependencies=dependencies, mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2',
    parent_scope=dict(sources=len(parent_manifest['project_sources']), requests=len(parent_manifest['requested_axioms']), stages=len(parent_manifest['stages'])),
    files=files)
(OUT/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(offer=str(OUT), source_sha256=sha(new.encode()), checks_sha256=sha(checks), manifest_sha256=sha((OUT/'manifest.json').read_bytes())), indent=2))
