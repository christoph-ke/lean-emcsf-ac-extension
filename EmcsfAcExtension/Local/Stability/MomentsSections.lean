module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Infra.Calculus.PartialsC1
public import EmcsfAcExtension.Infra.AC.Quotient

/-! # Closed radial sections for the stability moments

Sectional regularity and radius primitives follow from the standing classical
setting. No differentiated renormalized transport equation is used here.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension.Local

variable {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}

/-- The outgoing normalized ratio is `C¹` on the full closed triangle. -/
theorem stab_out_ratio_c1 (hS : IsC1Solution e S (triangle 0 T)) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ))
      (triangle 0 T) := by
  have hc := hS.c1_theta.mul
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn hS.c1_lam).inv
      (fun p hp => Complex.ofReal_ne_zero.mpr (hS.lam_pos p hp).ne'))
  simpa only [Pi.mul_def, Pi.inv_def, div_eq_mul_inv, Function.comp_apply,
    Function.uncurry_apply_pair, Complex.ofRealCLM_apply] using! hc

/-- The incoming normalized ratio is `C¹` on the full closed triangle. -/
theorem stab_in_ratio_c1 (hS : IsC1Solution e S (triangle 0 T)) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.xi p.1 p.2 / (S.nu p.1 p.2 : ℂ))
      (triangle 0 T) := by
  have hc := hS.c1_xi.mul
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn hS.c1_nu).inv
      (fun p hp => Complex.ofReal_ne_zero.mpr (hS.nu_neg p hp).ne))
  simpa only [Pi.mul_def, Pi.inv_def, div_eq_mul_inv, Function.comp_apply,
    Function.uncurry_apply_pair, Complex.ofRealCLM_apply] using! hc

/-- The outgoing ratio is AC on each closed outgoing section, including the
axis. This is a regularity fact, with no estimate constant. -/
theorem stab_out_ratio_ac (hset : StabSetting e T ε M A S h) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    AbsolutelyContinuousOnInterval (fun s => S.theta u s / (S.lam u s : ℂ)) u v := by
  apply ContDiffOn.absolutelyContinuousOnInterval
  rw [uIcc_of_le huv]
  exact (stab_out_ratio_c1 hset.c1).comp
    (contDiffOn_const.prodMk contDiffOn_id)
    (fun s hs => ⟨hu, hs.1, hs.2.trans hvT⟩)

/-- The outgoing normalized scalar has continuous within-domain first partials. -/
theorem stab_normalized_out_c1 (hS : IsC1Solution e S (triangle 0 T)) :
    ContDiffOn ℝ 1 (Function.uncurry S.a) (triangle 0 T) := by
  simpa only [Pi.add_def, Function.uncurry_def, Fields.a] using!
    hS.c1_phi.add (stab_out_ratio_c1 hS)

/-- The incoming normalized scalar has continuous within-domain first partials. -/
theorem stab_normalized_in_c1 (hS : IsC1Solution e S (triangle 0 T)) :
    ContDiffOn ℝ 1 (Function.uncurry S.b) (triangle 0 T) := by
  simpa only [Pi.add_def, Function.uncurry_def, Fields.b] using!
    hS.c1_phi.add (stab_in_ratio_c1 hS)

/-- The outgoing ratio vanishes at the regular axis, exactly as required by
the radial integrating factor. No limiting representative is chosen. -/
theorem stab_out_ratio_axis (hset : StabSetting e T ε M A S h) {t : ℝ}
    (ht : t ∈ Icc 0 T) : S.theta t t / (S.lam t t : ℂ) = 0 := by
  have ha := (hset.c1.axis t ⟨ht.1, le_rfl, ht.2⟩).2.2.2.2.1
  simpa only [Fields.a, add_eq_left] using ha

/-- The incoming ratio vanishes at the regular axis. This is the terminal
condition when the incoming section is parametrized outwards from the axis. -/
theorem stab_in_ratio_axis (hset : StabSetting e T ε M A S h) {t : ℝ}
    (ht : t ∈ Icc 0 T) : S.xi t t / (S.nu t t : ℂ) = 0 := by
  have hb := (hset.c1.axis t ⟨ht.1, le_rfl, ht.2⟩).2.2.2.2.2
  simpa only [Fields.b, add_eq_left] using hb

/-- The radius is the primitive of `λ` on a closed outgoing section.
This uses the pointwise field equation only off the axis. -/
theorem stab_radius_out_integral (hset : StabSetting e T ε M A S h) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    (∫ s in u..v, S.lam u s) = S.r u v := by
  have hr : ContinuousOn (S.r u) (Icc u v) :=
    hset.c1.c1_r.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨hu, hs.1, hs.2.trans hvT⟩)
  have hl : ContinuousOn (S.lam u) (Icc u v) :=
    hset.c1.c1_lam.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨hu, hs.1, hs.2.trans hvT⟩)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv hr
    (fun s hs => by
      have hp : (u, s) ∈ triangle 0 T := ⟨hu, hs.1.le, hs.2.le.trans hvT⟩
      have hd := hasDerivWithinAt_uncurry_triangle_v hset.c1.c1_r hp
      change HasDerivWithinAt (S.r u) (pdV (triangle 0 T) S.r u s) (Icc u T) s at hd
      rw [(hset.c1.eq_v (u, s) hp hs.1).1] at hd
      exact hd.hasDerivAt (Icc_mem_nhds hs.1 (hs.2.trans_le hvT)))
    ((by simpa only [uIcc_of_le huv] using hl :
      ContinuousOn (S.lam u) (uIcc u v)).intervalIntegrable)
  rw [(hset.c1.axis u ⟨hu, le_rfl, huv.trans hvT⟩).1, sub_zero] at hi
  exact hi

/-- The radius is the positively oriented incoming primitive of `-ν` from
the axis. The displayed integral is written in increasing `u` coordinates. -/
theorem stab_radius_in_integral (hset : StabSetting e T ε M A S h) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    (∫ s in u..v, -S.nu s v) = S.r u v := by
  have hr : ContinuousOn (fun s => S.r s v) (Icc u v) :=
    hset.c1.c1_r.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hu.trans hs.1, hs.2, hvT⟩)
  have hn : ContinuousOn (fun s => S.nu s v) (Icc u v) :=
    hset.c1.c1_nu.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hu.trans hs.1, hs.2, hvT⟩)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv hr
    (fun s hs => by
      have hp : (s, v) ∈ triangle 0 T := ⟨hu.trans hs.1.le, hs.2.le, hvT⟩
      have hd := hasDerivWithinAt_uncurry_triangle_u hset.c1.c1_r hp
      change HasDerivWithinAt (fun s => S.r s v)
        (pdU (triangle 0 T) S.r s v) (Icc 0 v) s at hd
      rw [(hset.c1.eq_u (s, v) hp hs.2).1] at hd
      exact hd.hasDerivAt (Icc_mem_nhds (hu.trans_lt hs.1) hs.2))
    ((by simpa only [uIcc_of_le huv] using hn :
      ContinuousOn (fun s => S.nu s v) (uIcc u v)).intervalIntegrable)
  rw [(hset.c1.axis v ⟨hu.trans huv, le_rfl, hvT⟩).1, zero_sub] at hi
  rw [intervalIntegral.integral_neg, hi, neg_neg]

/-- The outgoing radius is comparable to coordinate separation with the exact
box constants `1/4` and `1`, independently of all solution parameters. -/
theorem stab_radius_bounds (hset : StabSetting e T ε M A S h) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    (v - u) / 4 ≤ S.r u v ∧ S.r u v ≤ v - u := by
  have hl : ContinuousOn (S.lam u) (uIcc u v) := by
    rw [uIcc_of_le huv]
    exact hset.c1.c1_lam.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨hu, hs.1, hs.2.trans hvT⟩)
  have hi := hl.intervalIntegrable (μ := volume)
  rw [← stab_radius_out_integral hset hu huv hvT]
  constructor
  · have hb := intervalIntegral.integral_mono_on huv intervalIntegrable_const hi
      (fun s hs => (hset.box.2 (u, s) ⟨hu, hs.1, hs.2.trans hvT⟩).1)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_one_div] using hb
  · have hb := intervalIntegral.integral_mono_on huv hi intervalIntegrable_const
      (fun s hs => (hset.box.2 (u, s) ⟨hu, hs.1, hs.2.trans hvT⟩).2.1)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_one] using hb

/-- Radius is monotone away from the axis in either radial direction.
These order bounds use the signs of `λ` and `-ν`, with no estimate constant. -/
theorem stab_radius_section_order (hset : StabSetting e T ε M A S h) {u s v : ℝ}
    (hu : 0 ≤ u) (hus : u ≤ s) (hsv : s ≤ v) (hvT : v ≤ T) :
    S.r u s ≤ S.r u v ∧ S.r s v ≤ S.r u v := by
  have huv := hus.trans hsv
  have hl : ContinuousOn (S.lam u) (uIcc u v) := by
    rw [uIcc_of_le huv]
    exact hset.c1.c1_lam.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨hu, ht.1, ht.2.trans hvT⟩)
  have hn : ContinuousOn (fun t => -S.nu t v) (uIcc u v) := by
    rw [uIcc_of_le huv]
    exact (hset.c1.c1_nu.continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => ⟨hu.trans ht.1, ht.2, hvT⟩)).neg
  constructor
  · rw [← stab_radius_out_integral hset hu hus (hsv.trans hvT),
      ← stab_radius_out_integral hset hu huv hvT]
    apply intervalIntegral.integral_mono_interval le_rfl hus hsv _ hl.intervalIntegrable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (hset.c1.lam_pos (u, t) ⟨hu, ht.1.le, ht.2.trans hvT⟩).le
  · rw [← stab_radius_in_integral hset (hu.trans hus) hsv hvT,
      ← stab_radius_in_integral hset hu huv hvT]
    apply intervalIntegral.integral_mono_interval hus hsv le_rfl _ hn.intervalIntegrable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (neg_pos.mpr (hset.c1.nu_neg (t, v) ⟨hu.trans ht.1.le, ht.2, hvT⟩)).le

end EmcsfAcExtension.Local
