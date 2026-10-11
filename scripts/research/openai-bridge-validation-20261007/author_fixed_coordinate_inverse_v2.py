"""Translate the recorded fixed-coordinate argument without a Lean invocation."""
import hashlib
import json
from pathlib import Path
import re
from lean_source_static_preflight_v2 import inspect_bytes
from prepare_complete_operator_scope_v2 import imports, declarations
import prepare_complete_numeric_scope_v2 as scope

HERE = Path(__file__).resolve().parent


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    parent = HERE / 'numeric-same-instance-composition-capture-v3'
    assert sha((parent / 'index.json').read_bytes()) == '7499538C6B2BE856EB26C4D4F2B8B2F48844FFB26E64ED93089D1E0F518C19F1'
    raw = (parent / 'ExactNumericSameInstanceComposition.lean').read_bytes()
    assert sha(raw) == 'A171D0C93430164072950BEE4B06D15892576B4711ED6374AE5B40171770F23D'
    original = raw.decode('utf-8')
    old = scope.parent()
    added, _, provenance = scope.additions()
    all_sources = old | added
    rank_path = scope.PREFIX + 'ActualSelectedComplementSourceSizeAppendMoment.lean'
    rank_raw = old[rank_path]
    assert sha(rank_raw) == 'D4B86B565B267499622FE21E4D9E2F5D5E9261FB9A99711A105646F84DA75817'
    rank_source = rank_raw.decode('utf-8')
    start = rank_source.index('private theorem selected_rankloss_exponent')
    stop = rank_source.index('\ntheorem selected_actual_append_moment', start)
    arithmetic = rank_source[start:stop]
    # Any documentation before the following theorem belongs to that theorem.
    if '/--' in arithmetic:
        arithmetic = arithmetic[:arithmetic.index('/--')]
    assert 'private theorem rankloss_from_exponent' in arithmetic
    prefix = original[:original.index('open ActualGlobalDensityBridge\n')]
    prefix = re.sub(r'/\-! Exact same-instance composition.*?\-/',
        '/-! Fixed coordinate ambient inverse, universally quantified over ordinary tables.\nUncompiled translation of the recorded refresh-compatible argument. -/', prefix,
        count=1, flags=re.S)
    prefix = prefix.replace('ExactNumericSameInstanceComposition', 'ExactCoordinateNumericInverse')
    prefix = prefix.replace('import Mathlib.Tactic',
        'import PvNP.RealizableHardness.ActualFixedFunctionalAppendOperator\n'
        'import PvNP.RealizableHardness.ActualSelectedComplementSourceSizeAppendMoment\n'
        'import PvNP.RealizableHardness.ActualLeafLabelRankImageAlignment\n'
        'import PvNP.RealizableHardness.ActualSourceStarLaw\nimport Mathlib.Tactic')
    prefix += 'open ActualSourceStarLaw\nopen ActualSelectedComplementSourceSizeAnalyticMoment\n\n' + arithmetic + '\n'
    h = 'ActualCmmsaParameterReconciliation.hBlock L m'
    c = 'ActualStarFixedRhoDimensionGuard.leafT m (' + h + ')'
    s = 'ActualStarFixedRhoDimensionGuard.leafK m (' + h + ')'
    d = '(' + c + ' + ' + s + ')'
    v = 'ActualComplementCoordinateMassBridge.CoordAmbient (SamplerParameters.blocks samplerA (' + h + '))'
    statement = r'''/-- The same fixed coordinate ambient and arbitrary ordinary tables are retained
through the complete weighted, material and scalar inverse argument. -/
theorem fixed_coordinate_real_inverse_agreement
    {L m samplerA : Nat}
    (base : Nat -> Nat) (cutoff : Real -> Nat)
    (hA : 1 <= samplerA)
    (hsel : ActualCmmsaAdmissibilitySelector.selector
      (ActualNumericExplicitHeight.numericSourceFloor base cutoff) L = (m : WithBot Nat))
    (hcenter : Nonempty (Grass (V_AMBIENT) (C_DIM)))
    (hleaf : forall K : Grass (V_AMBIENT) (C_DIM),
      Nonempty (ActualChangedAmbient8SBoundary.LeafOver K D_DIM))
    (C : ActualSourceStarLaw.CenterTable (V := V_AMBIENT) (C_DIM))
    (T : ActualSourceStarLaw.LeafTable (V := V_AMBIENT) D_DIM)
    (hscore : ActualStarAcceptedGoodMass.successMargin
        (ActualStarFixedRhoDimensionGuard.badExponent m (H_DIM)) <=
      ActualChangedAmbient8SBoundary.StarDensity (k := m) hcenter hleaf C T) :
    exists q : Nat, exists Q : Grass (V_AMBIENT) q,
      exists P : ActualMaximalPairLadder.DecodedPair Q D_DIM,
        q + ActualMaximalPairLadder.codim P.W = ActualNumericSourceHeight.numericRankThreshold m /\
        Fintype.card (ActualMaximalPairLadder.Zoom Q P) != 0 /\
        Real.rpow 2
          (-2 * (1 - 1000 * ActualSelectedSpectralParameters.actualSelectedRho m
            (H_DIM) ^ 2) * (H_DIM : Real)) <
          (ActualMaximalPairLadder.agreement T Q P : Real) := by
'''
    for token, value in [('V_AMBIENT', v), ('C_DIM', c), ('D_DIM', d), ('H_DIM', h)]:
        statement = statement.replace(token, value)
    # Keep the original numeric setup and scalar argument; replace only the
    # source-instance selection and material wrapper with coordinate interfaces.
    start = original.index('  classical\n', original.index('theorem same_instance_real_inverse_agreement'))
    end = original.index('\nend\nend PvNP.', start)
    body = original[start:end]
    begin = body.index('  have hscore :')
    end_score = body.index('  have hdimBase :', begin)
    body = body[:begin] + body[end_score:]
    begin = body.index('  have hcomp :=')
    stop = body.index('  have hfixed :=', begin)
    replacement = '''  let CA := C
  let TA := T
  have hfinrank : Module.finrank (ZMod 2)
      (ActualComplementCoordinateMassBridge.CoordAmbient J) = 2 * J := by
    simp [ActualComplementCoordinateMassBridge.CoordAmbient]
  have hdim : d <= Module.finrank (ZMod 2)
      (ActualComplementCoordinateMassBridge.CoordAmbient J) := by
    rw [hfinrank, hsplitNat]
    omega
'''
    body = body[:begin] + replacement + body[stop:]
    begin = body.index('  have hstarScore :')
    stop = body.index('  obtain ', begin)
    body = body[:begin] + '''  have hstarScore : epsRat <= ActualChangedAmbient8SBoundary.StarDensity
      (k := m) hcenter hleaf CA TA := by
    simpa only [epsRat, E, h, CA, TA] using hscore
''' + body[stop:]
    body = body.replace('A.1', '(ActualComplementCoordinateMassBridge.CoordAmbient J)')
    begin = body.index('  let Tc :=')
    stop = body.index('  let etaRat', begin)
    body = body[:begin] + '  let Tc := T\n' + body[stop:]
    assert body.count('  refine ⟨A, ?_⟩\n') == 1
    body = body.replace('  refine ⟨A, ?_⟩\n', '')
    body = body.replace('_hcutHeight', 'hcutHeight')
    begin = body.index('  let fc :=')
    stop = body.index('  have hMaterial :', begin)
    material = r'''  let fc := f
  let Cc := C
  let k := ActualNumericExplicitHeight.numericK m
  have hPR := ActualLeafLabelRankImageAlignment.actual_leaf_failed_zoom_gives_nominal_pseudorandom
    (r := r) (d := d) hrd Tc fc etaRat eNonneg hfail'
  have hdimN : c + s <= 2 * J := by
    have hd := hdim
    rw [hfinrank] at hd
    exact hd
  have hMomentMatrix :=
    ActualSelectedComplementManuscriptDyadicMoment.selected_actual_HC_spectral_moment_bound_at_dyadic_exponent
      (n := 2 * J) (c := c) (s := s) (m := m) (r := r) (k := k)
      cutoff (C := Cc) (T := Tc) (f := fc)
      (Real.rpow 2 (-((2 : Real) / 3) * (r : Real) * rho * h))
      (by positivity) hmpos
      (ActualNumericExplicitHeight.numericK_rounding m hm).2.2.1
      hsplit hrhoPos hcParamReal hsParamReal hcutHeight hPR
      (ActualNumericExplicitHeight.numericK_rounding m hm).2.2.2
      ActualBinaryMatrixHC46OriginalExactInhabitant.original_HC46_exact
      (ActualSelectedComplementSourceSizeSpectralApplication.sourceSize_spectral47_inhabited cutoff)
      hdimN
  have hbudget : c + s = 2 * h /\ c + m * s + 2 * h <= 2 * J :=
    selected_rankloss_exponent hm hh hA rfl rfl rfl
  have hsmall := rankloss_from_exponent hhpos hbudget.1 hbudget.2
  have hsmall' : ((c + m * s : Nat) : Real) * (2 : Real) ^ (c + s - 1) /
      (2 : Real) ^ Module.finrank (ZMod 2)
        (ActualFixedFunctionalAppendOperator.CoordinateAmbient (2 * J)) <= 1 / 2 := by
    simpa only [show Module.finrank (ZMod 2)
      (ActualFixedFunctionalAppendOperator.CoordinateAmbient (2 * J)) = 2 * J by
        simp [ActualFixedFunctionalAppendOperator.CoordinateAmbient]] using hsmall
  have hAppend := ActualFixedFunctionalAppendOperator.matchingStarMass_cast_le_twice_actualAppendRankImageMoment
    (n := 2 * J) (c := c) (s := s) (k := m) hdim
    (by rw [hbudget.1]; omega) hsmall' Cc Tc fc
  have hMassMoment : X <= 2 * selectedActualMoment (m := m) (selectedG Cc fc) (selectedF Tc fc) := by
    simpa [X, Xq, CA, TA, Cc, Tc, fc,
      ActualFixedFunctionalAppendOperator.actualAppendRankImageMoment,
      selectedActualMoment, selectedG, selectedF,
      ActualFixedFunctionalAppendOperator.CoordinateAmbient,
      ActualComplementCoordinateMassBridge.CoordAmbient] using hAppend
  have hMomentRhs : selectedActualMoment (m := m) (selectedG Cc fc) (selectedF Tc fc) <=
      selected_actual_analytic_rhs (n := 2 * J) (c := c) (s := s) (m := m)
        Cc Tc fc r k (2 * (etaRat : Real))
        (Real.rpow 2 (-((2 : Real) / 3) * (r : Real) * rho * h)) := by
    simpa [selected_actual_analytic_rhs] using hMomentMatrix
  have hMoment := hMassMoment.trans
    (mul_le_mul_of_nonneg_left hMomentRhs (by norm_num : (0 : Real) <= 2))
  have hCenter := matching_center_mass_eq_grassmann_beta
    (V := ActualComplementCoordinateMassBridge.CoordAmbient J)
    (c := c) (s := s) (m := m) hdim Cc fc
'''
    body = body[:begin] + material + body[stop:]
    assert not any(token in body for token in ['I copies U', 'A.1', 'hside', 'hcomp', 'hstarDensity'])
    source = (prefix + statement + body + '\n\nend\nend PvNP.RealizableHardness.ExactCoordinateNumericInverse\n').encode('utf-8')
    check = b'import PvNP.RealizableHardness.ExactCoordinateNumericInverse\n\n#check PvNP.RealizableHardness.ExactCoordinateNumericInverse.fixed_coordinate_real_inverse_agreement\n#print axioms PvNP.RealizableHardness.ExactCoordinateNumericInverse.fixed_coordinate_real_inverse_agreement\n'
    files = {'ExactCoordinateNumericInverse.lean': source, 'ExactCoordinateNumericInverseChecks.lean': check}
    lexical = [inspect_bytes(data, name) for name, data in files.items()]
    dependencies = []
    for module in imports(source):
        if module.startswith('PvNP.'):
            path = 'lean/' + module.replace('.', '/') + '.lean'
            data = all_sources[path]
            dependencies.append(dict(module=module, path=path, bytes=len(data), sha256=sha(data)))
    map_text = '''# Fixed-coordinate inverse argument and API map

This uncompiled theorem fixes V=Fin(2J)->ZMod2 and quantifies over every ordinary center/leaf table on V. The same C,T,f and exact Real agreement threshold are used throughout. No occurrence instance or newly selected complement enters the proof. Nonempty center/extension proofs are universally quantified as in the original all-ambient interface; selected dimensions supply these carriers.

The exact parent numeric setup, threshold cast, weighted signal/beta bounds, finite rational maximum, scalar cutoffs, actual Boolean-energy B bound and scalar contradiction are retained from same-instance composition v3. Two private rank-loss arithmetic arguments are copied from the actual Full114 source-size append module. The table-general selected_actual_HC_spectral_moment_bound_at_dyadic_exponent replaces the source-instance material wrapper. The generic matching-star/actual-append comparison retains outer factor2, and the generic center-ratio identity supplies the same beta. All six numeric capture identities remain pinned.

The result is reusable for arbitrary refreshed tables after choosing one fixed coordinate ambient for an actual complement. It does not itself implement the refresh history, its probability bound, many-Q counting, H-extension, additional robust cutoffs, or the source NO decoder. These consumers and transports remain open. The manuscript target is not replaced by a rationally rounded agreement threshold. No external signal, material bound, HC/spectral contract, or failed-zoom premise is added.

This is a root-authored translation candidate. No Lean parser, Lean compiler, Lake, cloud run, or native certification was invoked. Every named dependency must pass native verification before acceptance.
'''
    files['ARGUMENT-AND-API-MAP.md'] = map_text.encode()
    manifest = dict(offer='numeric-fixed-coordinate-inverse-offer-v2', status='uncompiled source candidate',
        parent_composition_capture_sha256=sha((parent / 'index.json').read_bytes()),
        parent_input_sha256=scope.INPUT_SHA, parent_manifest_sha256=scope.MANIFEST_SHA,
        direct_project_dependencies=dependencies, numeric_captures=scope.CAPTURES,
        numeric_source_provenance=provenance, copied_rankloss_source=dict(path=rank_path, sha256=sha(rank_raw)),
        public_declarations=declarations(source), lexical_preflight=lexical,
        arbitrary_coordinate_tables=True, original_Real_threshold=True, outer_material_factor_two=True,
        offered_files={name:dict(bytes=len(data),sha256=sha(data)) for name,data in files.items()},
        control_sha256=sha(Path(__file__).read_bytes()), compiler_invoked=False, accepted=False)
    files['manifest.json'] = (json.dumps(manifest,indent=2)+'\n').encode()
    target = HERE / 'numeric-fixed-coordinate-inverse-offer-v2'
    target.mkdir(exist_ok=False)
    for name, data in files.items():
        (target / name).open('xb').write(data)
    print(json.dumps(dict(folder=target.name, source_bytes=len(source), source_sha256=sha(source),
                         public_declarations=manifest['public_declarations'], compiler_invoked=False)))


if __name__ == '__main__':
    main()
