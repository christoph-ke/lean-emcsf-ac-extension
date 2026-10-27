module

public import EmcsfAcExtension.Local.Defs.Envelope
public import EmcsfAcExtension.Infra.Triangle
import EmcsfAcExtension.Local.Api.Finite
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! # Geometric envelope transport through the diagonal

The incoming transport starts on the initial cone. The outgoing one
starts on the diagonal, where its trace is controlled by the first
envelope. Infinite source integrals are permitted until closure.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem norm_primitive_bound_aux {a b x : ℝ} {f H : ℝ → ℝ}
    (hax : a ≤ x) (hxb : x ≤ b) (hf : ContinuousOn f (Icc a b))
    (hH : AEStronglyMeasurable H (volume.restrict (Icc a b)))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (H t) t) :
    ‖f x‖ₑ ≤ ‖f a‖ₑ + ∫⁻ t in Icc a b, ‖H t‖ₑ := by
  by_cases htop : (∫⁻ t in Icc a b, ‖H t‖ₑ) = ⊤
  · simp only [htop, add_top, le_top]
  have hiH : Integrable H (volume.restrict (Icc a b)) :=
    ⟨hH, lt_top_iff_ne_top.mpr htop⟩
  have hsub : Icc a x ⊆ Icc a b := Icc_subset_Icc_right hxb
  have hiHx : IntervalIntegrable H volume a x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hax).2 (IntegrableOn.mono_set hiH hsub)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hax (hf.mono hsub)
    (fun t ht => hd t ⟨ht.1, ht.2.trans_le hxb⟩) hiHx
  have heq : f x = f a + ∫ t in a..x, H t := by rw [hi]; ring
  calc
    _ = ‖f a + ∫ t in a..x, H t‖ₑ := congrArg enorm heq
    _ ≤ ‖f a‖ₑ + ‖∫ t in a..x, H t‖ₑ := enorm_add_le _ _
    _ ≤ ‖f a‖ₑ + ∫⁻ t in Icc a x, ‖H t‖ₑ := by
      apply add_le_add le_rfl
      rw [intervalIntegral.integral_of_le hax, restrict_Ioc_eq_restrict_Icc]
      exact enorm_integral_le_lintegral_enorm _
    _ ≤ _ := add_le_add le_rfl (lintegral_mono_set hsub)

/-- A common geometric source controls the two labelwise envelopes.
The exact coefficients `2,2,1` are universal. Both source integration
orders are retained, so no area Fubini assumption is hidden. Continuity
and differentiability are hypotheses of this analytic `_of_` helper;
the field equations supply them for the geometric renormalizations.
-/
theorem stab_geometric_envelopes_of_transport_c1 {T : ℝ} (_hT : 0 ≤ T)
    {L N H : ℝ → ℝ → ℝ}
    (hL : ContinuousOn (Function.uncurry L) (triangle 0 T))
    (hN : ContinuousOn (Function.uncurry N) (triangle 0 T))
    (hHi : ∀ v ∈ Icc 0 T, AEStronglyMeasurable (fun u => H u v)
      (volume.restrict (Icc 0 v)))
    (hHo : ∀ u ∈ Icc 0 T, AEStronglyMeasurable (H u)
      (volume.restrict (Icc u T)))
    (hdL : ∀ v ∈ Icc 0 T, ∀ u ∈ Ioo 0 v,
      HasDerivAt (fun t => L t v) (H u v) u)
    (hdN : ∀ u ∈ Icc 0 T, ∀ v ∈ Ioo u T,
      HasDerivAt (N u) (H u v) v)
    (haxis : ∀ t ∈ Icc 0 T, N t t = L t t) :
    (∫⁻ v in Icc 0 T, outEnv 0 L v) + (∫⁻ u in Icc 0 T, inEnv T N u) ≤
      2 * (∫⁻ v in Icc 0 T, ‖L 0 v‖ₑ) +
      2 * (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, ‖H u v‖ₑ) +
      ∫⁻ u in Icc 0 T, ∫⁻ v in Icc u T, ‖H u v‖ₑ := by
  let I := ∫⁻ v in Icc 0 T, ‖L 0 v‖ₑ
  let F := ∫⁻ v in Icc 0 T, outEnv 0 L v
  let G := ∫⁻ u in Icc 0 T, inEnv T N u
  let Ai := ∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, ‖H u v‖ₑ
  let Ao := ∫⁻ u in Icc 0 T, ∫⁻ v in Icc u T, ‖H u v‖ₑ
  have hpointL v (hv : v ∈ Icc 0 T) :
      outEnv 0 L v ≤ ‖L 0 v‖ₑ + ∫⁻ u in Icc 0 v, ‖H u v‖ₑ := by
    apply iSup₂_le
    intro u hu
    exact norm_primitive_bound_aux hu.1 hu.2
      (hL.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun t ht => ⟨ht.1, ht.2, hv.2⟩)) (hHi v hv) (hdL v hv)
  have hpointN u (hu : u ∈ Icc 0 T) :
      inEnv T N u ≤ outEnv 0 L u + ∫⁻ v in Icc u T, ‖H u v‖ₑ := by
    apply iSup₂_le
    intro v hv
    apply (norm_primitive_bound_aux hv.1 hv.2
      (hN.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun t ht => ⟨hu.1, ht.1, ht.2⟩)) (hHo u hu) (hdN u hu)).trans
    dsimp only [Function.comp_def, Function.uncurry_def, id_eq]
    rw [haxis u hu]
    exact add_le_add (le_iSup₂_of_le u ⟨hu.1, le_rfl⟩ le_rfl) le_rfl
  have hLI : AEMeasurable (fun v => ‖L 0 v‖ₑ) (volume.restrict (Icc 0 T)) :=
    ((hL.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => ⟨le_rfl, hv.1, hv.2⟩)).enorm).aemeasurable measurableSet_Icc
  have hLE : AEMeasurable (outEnv 0 L) (volume.restrict (Icc 0 T)) :=
    (continuousOn_outEnv hL).aemeasurable measurableSet_Icc
  have hF : F ≤ I + Ai := by
    apply (setLIntegral_mono' measurableSet_Icc hpointL).trans_eq
    exact lintegral_add_left' hLI _
  have hG : G ≤ F + Ao := by
    apply (setLIntegral_mono' measurableSet_Icc hpointN).trans_eq
    exact lintegral_add_left' hLE _
  change F + G ≤ 2 * I + 2 * Ai + Ao
  calc
    _ ≤ F + (F + Ao) := add_le_add le_rfl hG
    _ ≤ (I + Ai) + ((I + Ai) + Ao) := add_le_add hF (add_le_add hF le_rfl)
    _ = _ := by ring

end EmcsfAcExtension.Local
