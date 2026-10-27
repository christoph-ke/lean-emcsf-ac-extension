module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassODE
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassSign
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassRegularity
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassAlgebra
import EmcsfAcExtension.Local.Stability.MomentsReflection
import EmcsfAcExtension.Local.Calculus.Raychaudhuri
import EmcsfAcExtension.Local.Algebra.Radial
import EmcsfAcExtension.Local.Stability.FluxDifferenceRegularity
import EmcsfAcExtension.Local.Stability.GeometryDifferenceOptical
import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Incoming normalized mass in the outward parameter

The incoming mass constraint is used in its own orientation. The outward
parameter is `t = -u`, the radius derivative is `-ν`, and the regular
axis is its initial endpoint. No outgoing weighted estimate is used.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- Exact incoming mass-ratio constraint on the classical class.
There are no estimate constants or small-data assumptions. -/
theorem Stab.incoming_mu_derivative_identity_c1 {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    HasDerivWithinAt (fun s => S.mu s v)
      (S.nu u v / S.r u v * ((1 - S.mu u v) * ‖S.xi u v / S.nu u v‖ ^ 2 +
        S.Q u v ^ 2 / S.r u v ^ 2 - S.mu u v)) (Icc 0 v) u := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  apply (hasDerivWithinAt_mu_u_aux hS hu huv hvT).congr_deriv
  exact Stab.outgoing_mu_derivative_identity_algebra (hS.r_pos _ hp huv).ne'
    (hS.nu_neg _ hp).ne (hS.eq_u _ hp huv).2.2.1

private theorem mass_gap_solve_in_aux {n l γ I : ℝ}
    (hl : l ≠ 0) (hγ : γ ≠ 0) (hopt : n / γ = l * Real.exp I) :
    γ = n / l * Real.exp (-I) := by
  have heq := (div_eq_iff hγ).mp hopt
  rw [Real.exp_neg, ← div_eq_mul_inv, div_div]
  apply (eq_div_iff (mul_ne_zero hl (Real.exp_ne_zero I))).mpr
  calc
    γ * (l * Real.exp I) = l * Real.exp I * γ := by ring
    _ = n := heq.symm

/-- The reflected mass ratio is AC through its initial regular-axis
endpoint. The proof uses the exact incoming optical representation;
no mass-distance estimate or radius cutoff is an assumption. -/
theorem stab_mu_reflected_ac
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    AbsolutelyContinuousOnInterval (fun t => S.mu (-t) v) (-v) (-u) := by
  let F := fun s => -S.nu s v / S.r s v * ‖S.xi s v / (S.nu s v : ℂ)‖ ^ 2
  have hmap : MapsTo (fun t : ℝ => (-t, v)) (Icc (-v) (-u)) (triangle 0 T) := by
    intro t ht
    exact ⟨by linarith only [hu, ht.2], by linarith only [ht.1], hvT⟩
  have cF : ContinuousOn (fun t => F (-t)) (Icc (-v) (-u)) :=
    (stab_in_quadratic_flux_continuous hset).comp
      (continuous_neg.prodMk continuous_const).continuousOn hmap
  have hI := (ContinuousOn.intervalIntegrable_of_Icc (μ := volume)
    (neg_le_neg huv) cF).absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hL : AbsolutelyContinuousOnInterval (fun t => S.lam (-t) v / S.lam v v) (-v) (-u) := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le (neg_le_neg huv)]
    exact (hset.c1.c1_lam.comp (contDiffOn_id.neg.prodMk contDiffOn_const) hmap).div_const _
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) (-v) (-u) :=
    (LipschitzWith.const 1).lipschitzOnWith.absolutelyContinuousOnInterval
  apply (hconst.sub (hL.mul_normed_ring hI.neg.exp)).congr
  intro t ht
  have ht' : t ∈ Icc (-v) (-u) := by simpa only [uIcc_of_le (neg_le_neg huv)] using ht
  have hpt := hmap ht'
  have hg := mass_gap_solve_in_aux
    (hset.c1.lam_pos (v, v) ⟨hu.trans huv, le_rfl, hvT⟩).ne'
    (hset.c1.one_sub_mu_pos (-t, v) hpt).ne'
    (stab_in_optical_from_axis hset hpt.1 hpt.2.1 hvT)
  have hi : (∫ s in -v..t, F (-s)) = (∫ s in -t..v, F s) := by
    rw [intervalIntegral.integral_comp_neg, neg_neg]
  change 1 - (S.lam (-t) v / S.lam v v * Real.exp (-(∫ s in -v..t, F (-s)))) = S.mu (-t) v
  rw [hi]
  dsimp only [F] at hg ⊢
  linarith only [hg]

/-- Incoming difference forcing in the outward parameter. The remaining
positive damping is `(-ν₁/r₁)(1+|ξ₁/ν₁|²)`. -/
@[expose] noncomputable def massDifferenceForcingIn (S₁ S₂ : Fields) (u v : ℝ) : ℝ :=
  -S₁.nu u v / S₁.r u v *
    ((1 - S₂.mu u v) * (‖S₁.xi u v / (S₁.nu u v : ℂ)‖ ^ 2 -
      ‖S₂.xi u v / (S₂.nu u v : ℂ)‖ ^ 2) +
      (S₁.Q u v ^ 2 / S₁.r u v ^ 2 - S₂.Q u v ^ 2 / S₂.r u v ^ 2)) +
    (-S₁.nu u v / S₁.r u v - -S₂.nu u v / S₂.r u v) *
      ((1 - S₂.mu u v) * ‖S₂.xi u v / (S₂.nu u v : ℂ)‖ ^ 2 +
        S₂.Q u v ^ 2 / S₂.r u v ^ 2 - S₂.mu u v)

/-- The absolute incoming forcing retains the matching incoming Hardy
weight and the second solution's individual mass term. Coefficients `2`
and `20` are universal, uniformly in every field parameter. -/
theorem stab_in_mass_difference_forcing_le
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    |massDifferenceForcingIn S₁ S₂ u v| ≤
      (2 * ε) * (-S₁.nu u v / S₁.r u v *
        ‖S₁.xi u v / (S₁.nu u v : ℂ) - S₂.xi u v / (S₂.nu u v : ℂ)‖) +
      -S₁.nu u v / S₁.r u v *
        |S₁.Q u v ^ 2 / S₁.r u v ^ 2 - S₂.Q u v ^ 2 / S₂.r u v ^ 2| +
      (20 * (geomDist T S₁ S₂).toReal) * (-S₁.nu u v / S₁.r u v *
        (‖S₂.xi u v / (S₂.nu u v : ℂ)‖ ^ 2 + S₂.Q u v ^ 2 / S₂.r u v ^ 2 +
          |S₂.mu u v|)) := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hμ := stab_mu_nonneg h₂s hu huv.le hvT
  rw [abs_of_nonneg hμ]
  exact stab_mass_difference_forcing_le
    (div_nonneg (neg_pos.mpr (h₁s.c1.nu_neg (u, v) hp)).le
      (h₁s.c1.r_pos (u, v) hp huv).le)
    hμ (by linarith only [h₂s.c1.one_sub_mu_pos (u, v) hp]) (by positivity)
    ((le_add_of_nonneg_left (norm_nonneg _)).trans (h₁s.box.2 (u, v) hp).2.2.2.2.2.1)
    ((le_add_of_nonneg_left (norm_nonneg _)).trans (h₂s.box.2 (u, v) hp).2.2.2.2.2.1)
    (stab_in_weight_sub_le h₁s h₂s hu huv hvT)

/-- The incoming weighted mass difference is bounded by its exact absolute
forcing with coefficient one. This is the reversed incoming constraint,
with its own axis endpoint; no outgoing mass estimate is an input. -/
theorem stab_in_mass_difference_raw
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    (∫⁻ t in Icc u v, ENNReal.ofReal
      (-S₁.nu t v / S₁.r t v * |S₁.mu t v - S₂.mu t v|)) ≤
      ∫⁻ t in Icc u v, ENNReal.ofReal |massDifferenceForcingIn S₁ S₂ t v| := by
  let w := fun t => -S₁.nu (-t) v
  let d := fun t => -S₁.nu (-t) v / S₁.r (-t) v *
    (1 + ‖S₁.xi (-t) v / (S₁.nu (-t) v : ℂ)‖ ^ 2)
  let q := fun t => massDifferenceForcingIn S₁ S₂ (-t) v
  have hmap : MapsTo (fun t : ℝ => (-t, v)) (Ioc (-v) (-u)) (triangle 0 T) := by
    intro t ht
    exact ⟨by linarith only [hu, ht.2], by linarith only [ht.1], hvT⟩
  have cN₁ := h₁s.c1.c1_nu.continuousOn.comp
    (continuous_neg.prodMk continuous_const).continuousOn hmap
  have cN₂ := h₂s.c1.c1_nu.continuousOn.comp
    (continuous_neg.prodMk continuous_const).continuousOn hmap
  have cR₁ := h₁s.c1.c1_r.continuousOn.comp
    (continuous_neg.prodMk continuous_const).continuousOn hmap
  have cR₂ := h₂s.c1.c1_r.continuousOn.comp
    (continuous_neg.prodMk continuous_const).continuousOn hmap
  have cQ₁ := h₁s.c1.c1_Q.continuousOn.comp
    (continuous_neg.prodMk continuous_const).continuousOn hmap
  have cQ₂ := h₂s.c1.c1_Q.continuousOn.comp
    (continuous_neg.prodMk continuous_const).continuousOn hmap
  have cY₁ := (stab_in_ratio_c1 h₁s.c1).continuousOn.comp
    (continuous_neg.prodMk continuous_const).continuousOn hmap
  have cY₂ := (stab_in_ratio_c1 h₂s.c1).continuousOn.comp
    (continuous_neg.prodMk continuous_const).continuousOn hmap
  have cμ₂ := (continuousOn_mu_aux h₂s.pos h₂s.c1).comp
    (continuous_neg.prodMk continuous_const).continuousOn hmap
  have hr₁ : ∀ t ∈ Ioc (-v) (-u), S₁.r (-t) v ≠ 0 := by
    intro t ht
    exact (h₁s.c1.r_pos _ (hmap ht) (by linarith only [ht.1])).ne'
  have hr₂ : ∀ t ∈ Ioc (-v) (-u), S₂.r (-t) v ≠ 0 := by
    intro t ht
    exact (h₂s.c1.r_pos _ (hmap ht) (by linarith only [ht.1])).ne'
  have cw₁ := cN₁.neg.div cR₁ hr₁
  have cw₂ := cN₂.neg.div cR₂ hr₂
  have ce₁ := (cQ₁.pow 2).div (cR₁.pow 2) (fun t ht => pow_ne_zero 2 (hr₁ t ht))
  have ce₂ := (cQ₂.pow 2).div (cR₂.pow 2) (fun t ht => pow_ne_zero 2 (hr₂ t ht))
  have cq : ContinuousOn q (Ioc (-v) (-u)) :=
    (cw₁.mul ((continuousOn_const.sub cμ₂).mul
      ((cY₁.norm.pow 2).sub (cY₂.norm.pow 2)) |>.add (ce₁.sub ce₂))).add
        ((cw₁.sub cw₂).mul (((continuousOn_const.sub cμ₂).mul (cY₂.norm.pow 2)).add ce₂
          |>.sub cμ₂))
  have hmapcc : MapsTo (fun t : ℝ => (-t, v)) (Icc (-v) (-u)) (triangle 0 T) := by
    intro t ht
    exact ⟨by linarith only [hu, ht.2], by linarith only [ht.1], hvT⟩
  have hw : IntervalIntegrable w volume (-v) (-u) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (neg_le_neg huv.le)
    exact (h₁s.c1.c1_nu.continuousOn.comp
      (continuous_neg.prodMk continuous_const).continuousOn hmapcc).neg
  have hw0 : ∀ t ∈ Icc (-v) (-u), 0 ≤ w t :=
    fun t ht => (neg_pos.mpr (h₁s.c1.nu_neg _ (hmapcc ht))).le
  have haxis : S₁.mu (-(-v)) v - S₂.mu (-(-v)) v = 0 := by
    simp only [neg_neg, Fields.mu,
      (h₁s.c1.axis v ⟨hu.trans huv.le, le_rfl, hvT⟩).1,
      (h₂s.c1.axis v ⟨hu.trans huv.le, le_rfl, hvT⟩).1, div_zero, sub_self]
  have hrad : ∀ t ∈ Icc (-v) (-u), (∫ s in -v..t, w s) = S₁.r (-t) v :=
    fun _ ht => stab_radius_reflected_integral h₁s hu huv.le hvT ht
  have hd : ∀ t ∈ Ioo (-v) (-u), w t / (∫ s in -v..t, w s) ≤ d t := by
    intro t ht
    rw [hrad t ⟨ht.1.le, ht.2.le⟩]
    have hb : 0 ≤ w t / S₁.r (-t) v := div_nonneg (hw0 t ⟨ht.1.le, ht.2.le⟩)
      (h₁s.c1.r_pos _ (hmap ⟨ht.1, ht.2.le⟩) (by linarith only [ht.1])).le
    dsimp only [d, w] at hb ⊢
    nlinarith only [mul_nonneg hb (sq_nonneg ‖S₁.xi (-t) v / (S₁.nu (-t) v : ℂ)‖)]
  have hid : ∀ t ∈ Ioo (-v) (-u),
      HasDerivWithinAt (fun s => S₁.mu (-s) v - S₂.mu (-s) v)
        (q t - d t * (S₁.mu (-t) v - S₂.mu (-t) v)) (Icc (-v) (-u)) t := by
    intro t ht
    have hut : 0 < -t := by linarith only [hu, ht.2]
    have htv : -t < v := by linarith only [ht.1]
    have hh := ((Stab.incoming_mu_derivative_identity_c1 h₁s.c1 hut.le htv hvT).sub
      (Stab.incoming_mu_derivative_identity_c1 h₂s.c1 hut.le htv hvT)).hasDerivAt
        (Icc_mem_nhds hut htv)
    have hh' := (by simpa only [zero_sub] using! hh :
      HasDerivAt (fun s => S₁.mu s v - S₂.mu s v) _ (0 - t)).comp_const_sub 0 t
    have hh'' := hh'.hasDerivWithinAt (s := Icc (-v) (-u))
    simp only [zero_sub] at hh''
    apply hh''.congr_deriv
    dsimp only [q, d, massDifferenceForcingIn]
    simp only [neg_div]
    ring
  have hf := (stab_mu_reflected_ac h₁s hu huv.le hvT).sub
    (stab_mu_reflected_ac h₂s hu huv.le hvT)
  have hh := stab_mass_hardy_of_identity (neg_le_neg huv.le) hw hw0 hf haxis
    (cq.abs.aestronglyMeasurable measurableSet_Ioc) hd hid
  rw [restrict_Ioc_eq_restrict_Icc] at hh
  have hleft : (∫⁻ t in Icc (-v) (-u), ENNReal.ofReal
      (w t / (∫ s in -v..t, w s) * |S₁.mu (-t) v - S₂.mu (-t) v|)) =
      ∫⁻ t in Icc u v, ENNReal.ofReal
        (-S₁.nu t v / S₁.r t v * |S₁.mu t v - S₂.mu t v|) := by
    calc
      _ = ∫⁻ t in Icc (-v) (-u), ENNReal.ofReal
          (-S₁.nu (-t) v / S₁.r (-t) v * |S₁.mu (-t) v - S₂.mu (-t) v|) := by
        apply setLIntegral_congr_fun measurableSet_Icc
        intro t ht
        dsimp only
        rw [hrad t ht]
      _ = _ := stab_lintegral_neg_Icc
        (fun s => ENNReal.ofReal (-S₁.nu s v / S₁.r s v * |S₁.mu s v - S₂.mu s v|)) u v
  simp only [Pi.sub_apply] at hh
  rw [hleft] at hh
  exact hh.trans_eq (stab_lintegral_neg_Icc
    (fun s => ENNReal.ofReal |massDifferenceForcingIn S₁ S₂ s v|) u v)

/-- The undifferenced incoming mass Hardy integral is bounded by its
scalar and electromagnetic source. The coefficient one is universal,
uniformly in every parameter and the axis-to-point interval. -/
theorem stab_in_mass_source_comparison
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    (∫⁻ t in Icc u v, ENNReal.ofReal (-S.nu t v / S.r t v * |S.mu t v|)) ≤
      ∫⁻ t in Icc u v, ENNReal.ofReal (-S.nu t v / S.r t v *
        (‖S.xi t v / (S.nu t v : ℂ)‖ ^ 2 + S.Q t v ^ 2 / S.r t v ^ 2)) := by
  let w := fun t => -S.nu (-t) v
  let d := fun t => -S.nu (-t) v / S.r (-t) v *
    (1 + ‖S.xi (-t) v / (S.nu (-t) v : ℂ)‖ ^ 2)
  let q := fun t => -S.nu (-t) v / S.r (-t) v *
    (‖S.xi (-t) v / (S.nu (-t) v : ℂ)‖ ^ 2 + S.Q (-t) v ^ 2 / S.r (-t) v ^ 2)
  have hmap : MapsTo (fun t : ℝ => (-t, v)) (Icc (-v) (-u)) (triangle 0 T) := by
    intro t ht
    exact ⟨by linarith only [hu, ht.2], by linarith only [ht.1], hvT⟩
  have hmapoc : MapsTo (fun t : ℝ => (-t, v)) (Ioc (-v) (-u)) (triangle 0 T) :=
    fun t ht => hmap ⟨ht.1.le, ht.2⟩
  have cN := hset.c1.c1_nu.continuousOn.comp
    (continuous_neg.prodMk continuous_const).continuousOn hmapoc
  have cR := hset.c1.c1_r.continuousOn.comp
    (continuous_neg.prodMk continuous_const).continuousOn hmapoc
  have cQ := hset.c1.c1_Q.continuousOn.comp
    (continuous_neg.prodMk continuous_const).continuousOn hmapoc
  have cY := (stab_in_ratio_c1 hset.c1).continuousOn.comp
    (continuous_neg.prodMk continuous_const).continuousOn hmapoc
  have hr : ∀ t ∈ Ioc (-v) (-u), S.r (-t) v ≠ 0 := by
    intro t ht
    exact (hset.c1.r_pos _ (hmapoc ht) (by linarith only [ht.1])).ne'
  have cq : ContinuousOn q (Ioc (-v) (-u)) :=
    (cN.neg.div cR hr).mul ((cY.norm.pow 2).add
      ((cQ.pow 2).div (cR.pow 2) (fun t ht => pow_ne_zero 2 (hr t ht))))
  have hw : IntervalIntegrable w volume (-v) (-u) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (neg_le_neg huv.le)
    exact (hset.c1.c1_nu.continuousOn.comp
      (continuous_neg.prodMk continuous_const).continuousOn hmap).neg
  have hw0 : ∀ t ∈ Icc (-v) (-u), 0 ≤ w t :=
    fun t ht => (neg_pos.mpr (hset.c1.nu_neg _ (hmap ht))).le
  have haxis : S.mu (-(-v)) v = 0 := by
    simp only [neg_neg, Fields.mu,
      (hset.c1.axis v ⟨hu.trans huv.le, le_rfl, hvT⟩).1, div_zero]
  have hrad : ∀ t ∈ Icc (-v) (-u), (∫ s in -v..t, w s) = S.r (-t) v :=
    fun _ ht => stab_radius_reflected_integral hset hu huv.le hvT ht
  have hd : ∀ t ∈ Ioo (-v) (-u), w t / (∫ s in -v..t, w s) ≤ d t := by
    intro t ht
    rw [hrad t ⟨ht.1.le, ht.2.le⟩]
    have hb : 0 ≤ w t / S.r (-t) v := div_nonneg (hw0 t ⟨ht.1.le, ht.2.le⟩)
      (hset.c1.r_pos _ (hmapoc ⟨ht.1, ht.2.le⟩) (by linarith only [ht.1])).le
    dsimp only [d, w] at hb ⊢
    nlinarith only [mul_nonneg hb (sq_nonneg ‖S.xi (-t) v / (S.nu (-t) v : ℂ)‖)]
  have hid : ∀ t ∈ Ioo (-v) (-u),
      HasDerivWithinAt (fun s => S.mu (-s) v)
        (q t - d t * S.mu (-t) v) (Icc (-v) (-u)) t := by
    intro t ht
    have hut : 0 < -t := by linarith only [hu, ht.2]
    have htv : -t < v := by linarith only [ht.1]
    have hh := (Stab.incoming_mu_derivative_identity_c1 hset.c1 hut.le htv hvT).hasDerivAt
      (Icc_mem_nhds hut htv)
    have hh' := (by simpa only [zero_sub] using! hh :
      HasDerivAt (fun s => S.mu s v) _ (0 - t)).comp_const_sub 0 t
    have hh'' := hh'.hasDerivWithinAt (s := Icc (-v) (-u))
    simp only [zero_sub] at hh''
    apply hh''.congr_deriv
    dsimp only [q, d]
    simp only [neg_div]
    ring
  have hh := stab_mass_hardy_of_identity (neg_le_neg huv.le) hw hw0
    (stab_mu_reflected_ac hset hu huv.le hvT) haxis
    (cq.abs.aestronglyMeasurable measurableSet_Ioc) hd hid
  rw [restrict_Ioc_eq_restrict_Icc] at hh
  have hleft : (∫⁻ t in Icc (-v) (-u), ENNReal.ofReal
      (w t / (∫ s in -v..t, w s) * |S.mu (-t) v|)) =
      ∫⁻ t in Icc u v, ENNReal.ofReal (-S.nu t v / S.r t v * |S.mu t v|) := by
    calc
      _ = ∫⁻ t in Icc (-v) (-u), ENNReal.ofReal
          (-S.nu (-t) v / S.r (-t) v * |S.mu (-t) v|) := by
        apply setLIntegral_congr_fun measurableSet_Icc
        intro t ht
        dsimp only
        rw [hrad t ht]
      _ = _ := stab_lintegral_neg_Icc
        (fun s => ENNReal.ofReal (-S.nu s v / S.r s v * |S.mu s v|)) u v
  rw [hleft] at hh
  apply hh.trans_eq
  calc
    _ = ∫⁻ t in Icc (-v) (-u), ENNReal.ofReal (q t) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro t ht
      dsimp only
      rw [abs_of_nonneg (show 0 ≤ q t from by
        dsimp only [q]
        have hn := hw0 t ht
        have hr0 : 0 ≤ S.r (-t) v :=
          (div_nonneg (sub_nonneg.mpr (hmap ht).2.1) (by norm_num : (0 : ℝ) ≤ 4)).trans
            (stab_radius_bounds hset (hmap ht).1 (hmap ht).2.1 hvT).1
        dsimp only [w] at hn
        positivity)]
    _ = _ := stab_lintegral_neg_Icc
      (fun s => ENNReal.ofReal (-S.nu s v / S.r s v *
        (‖S.xi s v / (S.nu s v : ℂ)‖ ^ 2 + S.Q s v ^ 2 / S.r s v ^ 2))) u v

end EmcsfAcExtension.Local
