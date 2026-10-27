module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.AssemblyMoments
import EmcsfAcExtension.Local.Stability.MomentsSections
import EmcsfAcExtension.Infra.Triangle

/-! # Incoming scalar control on a potential differentiation triangle

The incoming Hardy estimate is applied on each incoming section before
integrating its label. This gives charged_SF_new_version.tex:L5455–5493 on every
smaller triangle, including its regular-axis endpoint.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- Classical helper for the potential incoming triangle bound.
Related node: `restart-sec-bv-stability-independent#potential-incoming-triangle-bound`.
Incoming Hardy controls the potential differentiation triangle, with
the universal coefficient `64/3`. The displayed factor `T` is the only
length dependence; the constant is independent of all field parameters,
the background and derivative suprema. This lemma has the classical
`StabSetting` scope and does not claim the broader characteristic-AC node. -/
theorem Stab.potential_incoming_triangle_bound
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) (hε : ε ^ 2 ≤ 1 / 4)
    {v : ℝ} (hv : v ∈ Icc 0 T) :
    (∫⁻ p in triangle 0 v, ENNReal.ofReal
      (‖S.xi p.1 p.2 / (S.nu p.1 p.2 : ℂ)‖ / (p.2 - p.1))) ≤
        ENNReal.ofReal ((64 / 3) * T) *
          ∫⁻ s in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S) s := by
  classical
  let Y := (triangle 0 v).indicator
    (fun p : ℝ × ℝ => S.xi p.1 p.2 / (S.nu p.1 p.2 : ℂ))
  let F := fun p : ℝ × ℝ => ENNReal.ofReal (‖Y p‖ / (p.2 - p.1))
  let K := ∫⁻ s in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S) s
  have hsub : triangle 0 v ⊆ triangle 0 T := by
    intro p hp
    exact ⟨hp.1, hp.2.1, hp.2.2.trans hv.2⟩
  have hY : Measurable Y := by
    dsimp only [Y]
    rw [← Set.piecewise_eq_indicator]
    exact ((stab_in_ratio_c1 hset.c1).continuousOn.mono hsub).measurable_piecewise
      continuousOn_const (measurableSet_triangle 0 v)
  have hF : Measurable F :=
    ENNReal.measurable_ofReal.comp (hY.norm.div (measurable_snd.sub measurable_fst))
  have hsection : ∀ w ∈ Icc 0 v,
      (∫⁻ u in Icc 0 w, F (u, w)) ≤ ENNReal.ofReal (64 / 3 : ℝ) * K := by
    intro w hw
    have hwT := hw.2.trans hv.2
    have hpoint : (∫⁻ u in Icc 0 w, F (u, w)) ≤ 4 *
        ∫⁻ u in Icc 0 w, ENNReal.ofReal
          (-S.nu u w / S.r u w * ‖S.xi u w / (S.nu u w : ℂ)‖) := by
      rw [← lintegral_const_mul' 4 _ (by norm_num)]
      apply setLIntegral_mono' measurableSet_Icc
      intro u hu
      have hpv : (u, w) ∈ triangle 0 v := ⟨hu.1, hu.2, hw.2⟩
      have hpT := hsub hpv
      dsimp only [F, Y]
      rw [indicator_of_mem hpv]
      rcases hu.2.eq_or_lt with rfl | huw
      · simp only [sub_self, div_zero, ENNReal.ofReal_zero]
        exact bot_le
      have hr := hset.c1.r_pos (u, w) hpT huw
      have hb := hset.box.2 (u, w) hpT
      have hrb := (stab_radius_bounds hset hu.1 huw.le hwT).2
      have hgap : 0 < w - u := sub_pos.mpr huw
      have hweight : 1 / (w - u) ≤ 4 * (-S.nu u w / S.r u w) := by
        rw [← mul_div_assoc, div_le_div_iff₀ hgap hr]
        have hn : 1 ≤ 4 * (-S.nu u w) := by linarith only [hb.2.2.1]
        have hmul := mul_le_mul_of_nonneg_right hn hgap.le
        linarith only [hrb, hmul]
      rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      apply ENNReal.ofReal_le_ofReal
      have hmul := mul_le_mul_of_nonneg_right hweight
        (norm_nonneg (S.xi u w / (S.nu u w : ℂ)))
      simpa only [one_div_mul_eq_div, mul_assoc] using hmul
    have hi := stab_in_hardy hset hε hw.1 hwT
    apply hpoint.trans
    apply (mul_le_mul' le_rfl hi).trans_eq
    calc
      _ = (ENNReal.ofReal (4 : ℝ) * ENNReal.ofReal (16 / 3 : ℝ)) * K := by
        norm_num only [ENNReal.ofReal_ofNat]
        dsimp only [K]
        ring
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
        congr 2
        norm_num
  calc
    _ = ∫⁻ p in triangle 0 v, F p := by
      apply setLIntegral_congr_fun (measurableSet_triangle 0 v)
      intro p hp
      dsimp only [F, Y]
      rw [indicator_of_mem hp]
    _ = ∫⁻ w in Icc 0 v, ∫⁻ u in Icc 0 w, F (u, w) :=
      by
        rw [Measure.volume_eq_prod]
        exact lintegral_triangle_eq_lintegral_lintegral_symm hF
    _ ≤ ∫⁻ w in Icc 0 v, ENNReal.ofReal (64 / 3 : ℝ) * K :=
      setLIntegral_mono' measurableSet_Icc hsection
    _ = ENNReal.ofReal ((64 / 3) * v) * K := by
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64 / 3)]
      ring
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left hv.2 (by norm_num : (0 : ℝ) ≤ 64 / 3))) le_rfl

end EmcsfAcExtension.Local
