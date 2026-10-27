module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.ChargePrimitive
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Apriori.AreaJAux
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Local.Calculus.Reconstruction
import EmcsfAcExtension.Local.Calculus.C1ToSolution2
import EmcsfAcExtension.Infra.AC.Variation

/-! # Characteristic variation of the charge

Integrating the Maxwell estimates in their own orientations proves
`charged_SF_new_version.tex:L4907–L4908`. No envelope closure is required.
-/

public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

variable {e s ε M : ℝ} {S : Fields} {h : ℝ → ℂ}

private theorem charge_out_variation (hset : AprioriSetting e s ε M S h)
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 s) :
    eVariationOn (S.Q u) (Icc u v) ≤
      ENNReal.ofReal (2 * |e| * M * ε * S.r u v ^ 2) := by
  have hs : MapsTo (fun x => (u, x)) (Icc u v) (triangle 0 s) :=
    fun x hx => ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩
  have cQ : ContDiffOn ℝ 1 (S.Q u) (Icc u v) :=
    hset.c1.c1_Q.comp ((contDiffOn_const (c := u)).prodMk contDiffOn_id) hs
  have ac : AbsolutelyContinuousOnInterval (S.Q u) u v := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rwa [uIcc_of_le hp.2.1]
  have cw : ContinuousOn (fun x => S.lam u x * S.r u x) (Icc u v) :=
    (hset.c1.c1_lam.continuousOn.mul hset.c1.c1_r.continuousOn).comp
    (continuous_const.prodMk continuous_id).continuousOn hs
  have hw := cw.intervalIntegrable_of_Icc (μ := volume) hp.2.1
  have hb := intervalIntegral.integral_mono_on_of_le_Ioo hp.2.1
    ac.intervalIntegrable_deriv_finiteDimensional.norm (hw.const_mul (4 * |e| * M * ε))
    (fun x hx => by
      have hxD := hs ⟨hx.1.le, hx.2.le⟩
      have hd := (hasDerivWithinAt_pdV hset.c1.c1_Q hxD hs).hasDerivAt
        (Icc_mem_nhds hx.1 hx.2)
      rw [hd.deriv, (hset.c1.eq_v (u, x) hxD hx.1).2.2.2.1, Real.norm_eq_abs]
      simpa only [mul_assoc] using hset.maxwell_v_le hxD)
  have hm := outgoing_radius_moment (hset.c1.toIsSolution hset.pos) hp.2.1
    (show outSeg u u v ⊆ triangle 0 s from fun p hq => by
      rcases hq with ⟨rfl, hq⟩
      exact hs hq) 1
  norm_num only [pow_one, Nat.reduceAdd, Nat.cast_one] at hm
  rw [intervalIntegral.integral_const_mul, hm] at hb
  exact (ac.eVariationOn_le_integral_norm_deriv hp.2.1).trans
    (ENNReal.ofReal_le_ofReal (hb.trans_eq (by ring)))

private theorem charge_in_variation (hset : AprioriSetting e s ε M S h)
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 s) :
    eVariationOn (fun x => S.Q x v) (Icc u v) ≤
      ENNReal.ofReal (2 * |e| * M * ε * S.r u v ^ 2) := by
  have hs : MapsTo (fun x => (x, v)) (Icc u v) (triangle 0 s) :=
    fun x hx => ⟨hp.1.trans hx.1, hx.2, hp.2.2⟩
  have cQ : ContDiffOn ℝ 1 (fun x => S.Q x v) (Icc u v) :=
    hset.c1.c1_Q.comp (contDiffOn_id.prodMk (contDiffOn_const (c := v))) hs
  have ac : AbsolutelyContinuousOnInterval (fun x => S.Q x v) u v := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rwa [uIcc_of_le hp.2.1]
  have cw : ContinuousOn (fun x => -S.nu x v * S.r x v) (Icc u v) :=
    (hset.c1.c1_nu.continuousOn.neg.mul hset.c1.c1_r.continuousOn).comp
    (continuous_id.prodMk continuous_const).continuousOn hs
  have hw := cw.intervalIntegrable_of_Icc (μ := volume) hp.2.1
  have hb := intervalIntegral.integral_mono_on_of_le_Ioo hp.2.1
    ac.intervalIntegrable_deriv_finiteDimensional.norm (hw.const_mul (4 * |e| * M * ε))
    (fun x hx => by
      have hxD := hs ⟨hx.1.le, hx.2.le⟩
      have hd := (hasDerivWithinAt_pdU hset.c1.c1_Q hxD hs).hasDerivAt
        (Icc_mem_nhds hx.1 hx.2)
      rw [hd.deriv, (hset.c1.eq_u (x, v) hxD hx.2).2.2.2.1, Real.norm_eq_abs]
      simpa only [mul_assoc] using hset.maxwell_u_le hxD)
  have hm := incoming_radius_moment hset hp.1 hp.2.1 hp.2.2 1
  norm_num only [pow_one, Nat.reduceAdd, Nat.cast_one] at hm
  rw [intervalIntegral.integral_const_mul, hm] at hb
  exact (ac.eVariationOn_le_integral_norm_deriv hp.2.1).trans
    (ENNReal.ofReal_le_ofReal (hb.trans_eq (by ring)))

/-- [node restart-sec-independent-area#charge-characteristic-variation]
Both characteristic variations of the charge, `charged_SF_new_version.tex:L4907–L4908`.
`C` is universal, independent of `e,s,ε,M,S,h` and higher data derivatives.
The sharper endpoint-radius bound is retained alongside the `R = s/2` bound.
No smallness is required. -/
theorem charge_characteristic_variation :
    ∃ C : ℝ, 0 < C ∧ ∀ (e s ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
      AprioriSetting e s ε M S h → ∀ u v, (u, v) ∈ triangle 0 s →
        eVariationOn (S.Q u) (Icc u v) ≤
          ENNReal.ofReal (2 * |e| * M * ε * S.r u v ^ 2) ∧
        eVariationOn (fun x => S.Q x v) (Icc u v) ≤
          ENNReal.ofReal (2 * |e| * M * ε * S.r u v ^ 2) ∧
        eVariationOn (S.Q u) (Icc u v) ≤ ENNReal.ofReal (C * |e| * M * ε * (s / 2) ^ 2) ∧
        eVariationOn (fun x => S.Q x v) (Icc u v) ≤
          ENNReal.ofReal (C * |e| * M * ε * (s / 2) ^ 2) := by
  refine ⟨8, by norm_num, ?_⟩
  intro e s ε M S h hset u v hp
  have hout := charge_out_variation hset hp
  have hin := charge_in_variation hset hp
  have hr : S.r u v ≤ s := (Area.radius_bounds hset hp.1 hp.2.1 hp.2.2).2.trans
    (by linarith only [hp.1, hp.2.2])
  have hsq := pow_le_pow_left₀ (hset.radius_nonneg hp) hr 2
  have hcoeff : 0 ≤ 2 * |e| * M * ε := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg e))
      (le_trans (by norm_num) hset.one_le_M)) hset.eps_nonneg
  have hb : ENNReal.ofReal (2 * |e| * M * ε * S.r u v ^ 2) ≤
      ENNReal.ofReal (8 * |e| * M * ε * (s / 2) ^ 2) := by
    apply ENNReal.ofReal_le_ofReal
    convert mul_le_mul_of_nonneg_left hsq hcoeff using 1
    ring
  exact ⟨hout, hin, hout.trans hb, hin.trans hb⟩

end EmcsfAcExtension.Local
