from pathlib import Path
import hashlib
import json
import re
import tarfile

ROOT = Path(__file__).resolve().parents[3]
S = Path(__file__).resolve().parent
REF = S / 'full107-trace-qualified-source-record-v1/review-sources/lean/PvNP/RealizableHardness'
OUT = S / 'numeric-tagged-common-leaf-offer-20261011-v1'
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
EXPECTED_ARCHIVE = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
PINS = {
    'ActualLeafTransportCoherence.lean': '281144FB817D99845BE6BF399EEFCDB28B2300369CF1B715BBA580515377BAD5',
    'ActualLeafRelationLaws.lean': 'DF876D57B26C1D937FF588CC1EA48D8B4626BE2F4F9CF7DCC45DDDEA5A900003',
    'ActualTaggedPresentedSelection.lean': '838B2B75DD69C9706B6E924DF4D3AD3E0E661747F9F9BF486853CB55A593B793',
    'ActualTaggedSelectedDecoderBridge.lean': 'D428F9A1822A364C057A3209017B19916FF323F717590398A0F3CCC21898AB22',
}

def digest(raw):
    return hashlib.sha256(raw).hexdigest().upper()

with ARCHIVE.open('rb') as stream:
    assert hashlib.file_digest(stream, 'sha256').hexdigest().upper() == EXPECTED_ARCHIVE
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    for name, expected in PINS.items():
        raw = archive.extractfile('lean/PvNP/RealizableHardness/' + name).read()
        assert digest(raw) == expected
        assert (REF / name).read_bytes() == raw

assert not OUT.exists(), 'Refuse to overwrite an offered or captured directory'
original = (REF / 'ActualLeafTransportCoherence.lean').read_text(encoding='utf-8')
start = original.index('theorem actual_existsUnique_rhsFunctional_threeGoodQuestions')
end = original.index('theorem transportedLabel_coherence')
body = original[start:end]
body = body.replace('theorem actual_existsUnique_rhsFunctional_threeGoodQuestions', 'private theorem tagged_rhs_three_questions')
body = body.replace('theorem domain_inf_twoEquationSpans_le', 'private theorem tagged_domain_inf_two_equations')
body = body.replace('theorem actual_existsUnique_threeWayGluedLeafRhsFunctional', 'private theorem tagged_three_way_glue')
body = body.replace('actual_existsUnique_rhsFunctional_threeGoodQuestions I P Q R', 'tagged_rhs_three_questions I copies P Q R')
body = body.replace('domain_inf_twoEquationSpans_le P Q R', 'tagged_domain_inf_two_equations I copies P Q R')
body = body.replace('{I : ActualOccurrenceAllocation.Instance N m}', '(I : ActualOccurrenceAllocation.Instance N m)')
body = body.replace('(I : ActualOccurrenceAllocation.Instance N m)', '(I : ActualOccurrenceAllocation.Instance N m) (copies : Nat)')
body = body.replace('PresentedLeaf I J h', 'TaggedPresentedLeaf I copies J h')
body = body.replace('RawLeafLabel I P.domain', '(P.domain I copies) →ₗ[ZMod 2] ZMod 2')
body = body.replace('RespectsAt P rfl f', 'P.respectsRows I copies f')
body = body.replace('(I.GlobalVar → ZMod 2)', '(TaggedAmbient I copies)')
body = body.replace('Set I.RowId', 'Set (TaggedRow I copies)')
body = body.replace('actual_equationSpan_inf_sup_coordinateSpace_le I', 'equationSpan_inf_sup_coordinateSpace_le (taggedSource I copies).support\n      (taggedSource_support_card I copies) (tagged_pair_intersection I copies)')
body = body.replace('actual_existsUnique_rhsFunctional I', 'existsUnique_rhsFunctional (taggedSource I copies).support\n      (taggedSource I copies).rhs (taggedSource_support_card I copies)')
body = body.replace('I.support_card', '(taggedSource_support_card I copies)')
body = body.replace('I.pair_intersection', '(tagged_pair_intersection I copies)')
body = body.replace('I.support', '(taggedSource I copies).support')
body = body.replace('I.rowRhs', '(taggedSource I copies).rhs')
for letter in ('P', 'Q', 'R'):
    for field in ('domain_le_coordinateSpace', 'H_le_coordinateSpace', 'H_le_domain'):
        body = re.sub(r'\b' + letter + r'\.' + field + r'\b', '(' + letter + '.' + field + ' I copies)', body)
    for field in ('domain', 'H'):
        body = re.sub(r'\b' + letter + r'\.' + field + r'\b(?! I copies)', '(' + letter + '.' + field + ' I copies)', body)

header = '''import PvNP.RealizableHardness.ActualLeafTransportCoherence
import PvNP.RealizableHardness.ActualTaggedSelectedDecoderBridge

/-! Agreement of the one globally selected tagged table across related
presentations, including a common transverse leaf in different questions.
Uncompiled source candidate; it does not supply a decoder probability. -/
namespace PvNP.RealizableHardness.ActualTaggedCommonLeafCoherence
open PvNP.RealizableHardness
open ActualOccurrenceAllocation ActualStarQuestionSupport ActualStarSpanIntersection
open ActualRhsFunctionalConstruction ActualPresentedLeafGluing SubmoduleFunctionalGluing
open ActualTaggedFixedCenterGeometry ActualTaggedPresentedSelection
open ActualTaggedSelectedDecoderBridge

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
local instance rowIdDecidableEq {N m : Nat} (I : Instance N m) :
    DecidableEq I.RowId := Classical.decEq _

'''
tail = '''/-- Both transported labels are restrictions of one three-way glued
functional, so they agree on the full intersection of their domains. -/
theorem transported_labels_agree_on_intersection
    {N m J h : Nat} (I : Instance N m) (copies : Nat)
    (S P Q : TaggedPresentedLeaf I copies J h)
    (hSP : S.Rel I copies P) (hSQ : S.Rel I copies Q)
    (f : S.domain I copies →ₗ[ZMod 2] ZMod 2)
    (hf : S.respectsRows I copies f)
    (x : ↥(P.domain I copies ⊓ Q.domain I copies)) :
    taggedTransportedRawLabel I copies S P hSP f hf ⟨x.1, x.2.1⟩ =
      taggedTransportedRawLabel I copies S Q hSQ f hf ⟨x.1, x.2.2⟩ := by
  obtain ⟨F, hF, _⟩ := tagged_three_way_glue I copies S P Q f hf
  have hPcarrier : S.domain I copies ⊔ P.H I copies ≤
      S.domain I copies ⊔ (P.H I copies ⊔ Q.H I copies) :=
    sup_le le_sup_left (le_sup_of_le_right le_sup_left)
  have hQcarrier : S.domain I copies ⊔ Q.H I copies ≤
      S.domain I copies ⊔ (P.H I copies ⊔ Q.H I copies) :=
    sup_le le_sup_left (le_sup_of_le_right le_sup_right)
  let FP := F.comp (Submodule.inclusion hPcarrier)
  let FQ := F.comp (Submodule.inclusion hQcarrier)
  have hFP : FP = Classical.choose
      (tagged_existsUnique_gluedLeafRhsFunctional I copies S P.U P.goodU f hf) := by
    apply (Classical.choose_spec
      (tagged_existsUnique_gluedLeafRhsFunctional I copies S P.U P.goodU f hf)).2
    constructor
    · ext z
      exact LinearMap.congr_fun hF.1 z
    · intro e he
      exact hF.2.1 e he
  have hFQ : FQ = Classical.choose
      (tagged_existsUnique_gluedLeafRhsFunctional I copies S Q.U Q.goodU f hf) := by
    apply (Classical.choose_spec
      (tagged_existsUnique_gluedLeafRhsFunctional I copies S Q.U Q.goodU f hf)).2
    constructor
    · ext z
      exact LinearMap.congr_fun hF.1 z
    · intro e he
      exact hF.2.2 e he
  unfold taggedTransportedRawLabel
  rw [← hFP, ← hFQ]
  rfl

/-- The representative is fixed globally per class, before either question
is used. No domain equality is required for intersection agreement. -/
theorem selected_labels_agree_on_intersection
    {N m J h : Nat} (I : Instance N m) (copies : Nat)
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h)
    (P Q : TaggedPresentedLeaf I copies J h) (hPQ : P.Rel I copies Q)
    (x : ↥(P.domain I copies ⊓ Q.domain I copies)) :
    taggedSelectedLeafLabel I copies T s P ⟨x.1, x.2.1⟩ =
      taggedSelectedLeafLabel I copies T s Q ⟨x.1, x.2.2⟩ := by
  have hclass : taggedClassOf I copies P = taggedClassOf I copies Q :=
    (taggedClassOf_eq_iff I copies).mpr hPQ
  let S := (s (taggedClassOf I copies P)).1
  have hSP : S.Rel I copies P :=
    taggedRepresentativeRel I copies P (s (taggedClassOf I copies P))
  have hSQ : S.Rel I copies Q :=
    TaggedPresentedLeaf.Rel.trans I copies S P Q hSP hPQ
  have heq := transported_labels_agree_on_intersection I copies S P Q hSP hSQ
    (taggedValidifiedRawLabel I copies T S).1
    (taggedValidifiedRawLabel I copies T S).2 x
  simpa only [taggedSelectedLeafLabel, ← hclass, S] using heq

/-- Two actual presentations of the same transverse leaf have exactly the
same canonical table value on every vector of that leaf, even when their
outer questions and full domains differ. -/
theorem canonical_table_agrees_on_shared_leaf
    {N m J h : Nat} (I : Instance N m) (copies : Nat)
    (T : TaggedRawVertexTable I copies J h)
    (s : TaggedRepresentativeChoice I copies J h)
    (P Q : TaggedPresentedLeaf I copies J h) (hL : P.L = Q.L)
    (x : P.L) :
    taggedSelectedDomainTable I copies T s (P.domain I copies)
        ⟨x.1, le_sup_left x.2⟩ =
      taggedSelectedDomainTable I copies T s (Q.domain I copies)
        ⟨x.1, le_sup_left (hL ▸ x.2)⟩ := by
  have hPQ : P.Rel I copies Q := by
    change (P.L ⊔ P.H I copies) ⊔ Q.H I copies =
      (Q.L ⊔ Q.H I copies) ⊔ P.H I copies
    rw [hL]
    ac_rfl
  rw [taggedSelectedDomainTable_apply, taggedSelectedDomainTable_apply]
  exact selected_labels_agree_on_intersection I copies T s P Q hPQ
    ⟨x.1, le_sup_left x.2, le_sup_left (hL ▸ x.2)⟩

end
end PvNP.RealizableHardness.ActualTaggedCommonLeafCoherence
'''
source = header + body + tail
assert 'sorry' not in source and 'admit' not in source
assert 'actual_existsUnique' not in source and 'I.support' not in source
assert 'RawLeafLabel' not in source and 'RespectsAt' not in source
OUT.mkdir()
(OUT / 'ActualTaggedCommonLeafCoherence.lean').write_text(source, encoding='utf-8', newline='\n')
exports = ['transported_labels_agree_on_intersection', 'selected_labels_agree_on_intersection', 'canonical_table_agrees_on_shared_leaf']
checks = 'import PvNP.RealizableHardness.ActualTaggedCommonLeafCoherence\n\n'
checks += ''.join('#print axioms PvNP.RealizableHardness.ActualTaggedCommonLeafCoherence.' + n + '\n' for n in exports)
(OUT / 'Checks.lean').write_text(checks, encoding='utf-8', newline='\n')
argument = '''# Tagged common-leaf coherence

E002/S3137; source translation candidate, not kernel accepted.

The canonical manuscript's second-prover completion uses the same transverse leaf L in two different good questions. Its full domains L+H_P and L+H_Q can differ. The existing domain-equality coherence theorem alone does not establish equality of these two labels on L.

Fix the actual tagged occurrence source, arbitrary raw table T, and one representative choice s for each global leaf class. The same-leaf presentations P,Q are related since adding both equation spans produces the same subspace. Thus s selects the same source representative S for both.

For S,P,Q, actual tagged support cardinality is three and distinct supports intersect in at most one point. The pinned generic three-good-question independence theorem therefore makes their distinct equation vectors independent. Its basis construction supplies the RHS functional on the union of all three sets of equations; this does not assert the whole source is satisfiable. The pinned span-intersection geometry gives D_S intersect (H_P+H_Q) <= H_S. The validified representative label respects the RHS on H_S, and uniqueness on that span identifies it with the combined RHS functional there. They consequently agree on the intersection. The gluing theorem gives one functional F on D_S+H_P+H_Q extending the representative and the RHS of both questions.

Restrict F to D_S+H_P and D_S+H_Q. Each restriction meets the exact existing two-way gluing specification, so uniqueness identifies it with the function used by taggedTransportedRawLabel. Those labels agree at every vector in D_P intersect D_Q. Sharing the representative identifies the selected labels there. Finally taggedSelectedDomainTable_apply identifies the same canonical table at each actual full domain; on a common transverse leaf the table values coincide.

The first three private proof bodies are translated from the exact pinned untagged proof, replacing each source support/RHS/geometry occurrence explicitly with the actual tagged source. The generic three-question independence and intersection theorems are reused. All public conclusions use actual TaggedPresentedLeaf and the existing selected domain table. No common ambient functional, domain equality, new label consistency hypothesis, or decoder success is assumed.

Checks request the three public declarations. Native GCP compilation, exact axiom profiles and warning checks remain required. This module supplies only cross-question label coherence; it does not construct a legitimate completion U0(V), transport the triple-deletion law, bound exceptional entries, or prove the decoder/source-NO result.

Remaining to-do list: native verification; completion/coordinate-law/probability integration; refresh, side extension, decoder and remaining certification obligations.
'''
(OUT / 'ARGUMENT.md').write_text(argument, encoding='utf-8', newline='\n')
(OUT / '.gitattributes').write_text('* -text\n', encoding='utf-8', newline='\n')
files = []
for path in sorted(OUT.iterdir()):
    raw = path.read_bytes()
    raw.decode('utf-8')
    assert not raw.startswith(b'\xef\xbb\xbf')
    files.append({'path': path.name, 'bytes': len(raw), 'sha256': digest(raw)})
manifest = {
    'schema': 'numeric-tagged-common-leaf-offer-v1', 'status': 'uncompiled',
    'story': 'E002/S3137', 'author': '/root',
    'full114_archive': {'path': str(ARCHIVE), 'sha256': EXPECTED_ARCHIVE},
    'mathlib_revision': 'e06eff5f95374108acfaf19f1ff7473aa7771df2',
    'dependencies': PINS, 'public_axiom_requests': exports, 'files': files,
    'claims': 'Actual selected-table agreement across related presentations and a shared transverse leaf; no decoder probability or native acceptance.'
}
(OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8', newline='\n')
print(json.dumps({'directory': str(OUT), 'source_sha256': digest(source.encode()), 'files': files, 'manifest_sha256': digest((OUT/'manifest.json').read_bytes())}, indent=2))
