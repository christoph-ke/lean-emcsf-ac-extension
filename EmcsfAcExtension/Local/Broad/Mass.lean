module

public import EmcsfAcExtension.Local.Broad.BVHardy
public import EmcsfAcExtension.Infra.PowerKernel
public import EmcsfAcExtension.Infra.Triangle
import EmcsfAcExtension.Local.Calculus.RelativeCharge
import EmcsfAcExtension.Local.Broad.Charge

/-! # The matching radial Hardy kernel for mass averages

The nonnegative form of charged_SF_new_version.tex:L5761–5772 proves the kernel estimate
before any finiteness assumption. The radius variable belongs to the same
characteristic section in both integrations.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension.Local.Broad

/-- [node restart-stab-broad-uniqueness#mass-average-Hardy-kernel]
Tonelli's radial mass-average kernel, charged_SF_new_version.tex:L5761–5772 and internal project
record (K).
The exact universal coefficient is one. The estimate is in extended
nonnegative integrals and does not presuppose a finite Hardy norm. -/
theorem mass_average_hardy_kernel {H : ℝ} {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ ρ in Icc 0 H, ∫⁻ x in Icc 0 ρ, F x * ENNReal.ofReal (1 / ρ ^ 2)) ≤
      ∫⁻ x in Icc 0 H, F x * ENNReal.ofReal (1 / x) := by
  have hmeas : Measurable (fun p : ℝ × ℝ => F p.1 * ENNReal.ofReal (1 / p.2 ^ 2)) :=
    (hF.comp measurable_fst).mul (by fun_prop)
  rw [← lintegral_lintegral_swap_triangle hmeas]
  apply lintegral_mono_ae
  have hzero : ∀ᵐ x : ℝ, x ≠ 0 := by simp [ae_iff]
  filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hzero] with x hx hx0
  have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
  calc
    (∫⁻ ρ in Icc x H, F x * ENNReal.ofReal (1 / ρ ^ 2)) =
        ∫⁻ ρ in Icc x H, (F x * ENNReal.ofReal (1 / x)) *
          ENNReal.ofReal (orderedPowerKernel 1 0 x ρ) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro ρ hρ
      have hρpos : 0 < ρ := hxpos.trans_le hρ.1
      change F x * ENNReal.ofReal (1 / ρ ^ 2) =
        (F x * ENNReal.ofReal (1 / x)) * ENNReal.ofReal (orderedPowerKernel 1 0 x ρ)
      rw [mul_assoc, ← ENNReal.ofReal_mul (one_div_nonneg.mpr hxpos.le)]
      congr 2
      simp only [orderedPowerKernel, sub_zero, Real.rpow_one]
      norm_num only [show (1 : ℝ) + 1 = 2 by norm_num, Real.rpow_two]
      field_simp [hx0, hρpos.ne']
    _ = (F x * ENNReal.ofReal (1 / x)) *
        ∫⁻ ρ in Icc x H, ENNReal.ofReal (orderedPowerKernel 1 0 x ρ) :=
      lintegral_const_mul _ (by unfold orderedPowerKernel; fun_prop)
    _ ≤ (F x * ENNReal.ofReal (1 / x)) * ENNReal.ofReal (1 / 1) := by
      gcongr
      exact lintegral_orderedPowerKernel_le (by norm_num) hxpos.le hx.2
    _ = F x * ENNReal.ofReal (1 / x) := by simp

/-- The outgoing mass constraint reconstructed from the same-axis endpoint.
This is an exact identity in the broad frozen class, with no estimate constants
or derivative envelopes. -/
theorem outgoing_mass_reconstruction {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u ≤ v)
    (hseg : outSeg u u v ⊆ D) :
    2 * S.m u v = ∫ x in u..v, S.lam u x *
      ((1 - S.mu u x) * ‖S.theta u x / S.lam u x‖ ^ 2 + S.Q u x ^ 2 / S.r u x ^ 2) := by
  have hm := (hS.ac_out u u v huv hseg).2.1
  have heq := integralForm_of_ac_of_interior_deriv huv hm
    (fun x hx => IsSolution.hasDerivAt_mass_out hS hseg hx)
  have halg x (hx : x ∈ uIcc u v) :
      S.lam u x * ((1 - S.mu u x) * ‖S.theta u x / S.lam u x‖ ^ 2 +
        S.Q u x ^ 2 / S.r u x ^ 2) = 2 * S.mV u x := by
    have hx' : x ∈ Icc u v := by simpa only [uIcc_of_le huv] using hx
    have hl := (hS.lam_pos (u, x) (hseg ⟨rfl, hx'⟩)).ne'
    have h := RelCharge.radial_mass_equation hS (hseg ⟨rfl, hx'⟩)
    simpa only [mul_comm] using ((div_eq_iff hl).mp h).symm
  rw [intervalIntegral.integral_congr halg, intervalIntegral.integral_const_mul, ← heq.2]
  simp [(hS.axis u (hseg ⟨rfl, le_rfl, huv⟩)).2.1]

/-- The outgoing mass density is integrable up to its regular axis endpoint.
This follows directly from the AC mass equation and has no envelope or box
premise. -/
theorem outgoing_mass_density_integrable {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u ≤ v)
    (hseg : outSeg u u v ⊆ D) :
    IntervalIntegrable (fun x => S.lam u x *
      ((1 - S.mu u x) * ‖S.theta u x / S.lam u x‖ ^ 2 +
        S.Q u x ^ 2 / S.r u x ^ 2)) volume u v := by
  have heq := integralForm_of_ac_of_interior_deriv huv
    (hS.ac_out u u v huv hseg).2.1
    (fun x hx => IsSolution.hasDerivAt_mass_out hS hseg hx)
  apply (heq.1.const_mul 2).congr
  intro x hx
  have hx' : x ∈ Icc u v := by
    simpa only [uIcc_of_le huv] using uIoc_subset_uIcc hx
  have hl := (hS.lam_pos (u, x) (hseg ⟨rfl, hx'⟩)).ne'
  exact ((div_eq_iff hl).mp (RelCharge.radial_mass_equation hS (hseg ⟨rfl, hx'⟩))).trans
    (by ring)

/-- The outgoing mass ratio is the positive radial average of its constraint
density. This exact identity also holds at the axis with total division. -/
theorem outgoing_mass_ratio_reconstruction {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u ≤ v)
    (hseg : outSeg u u v ⊆ D) :
    S.mu u v = (S.r u v)⁻¹ * ∫ x in u..v, S.lam u x *
      ((1 - S.mu u x) * ‖S.theta u x / S.lam u x‖ ^ 2 + S.Q u x ^ 2 / S.r u x ^ 2) := by
  rw [Fields.mu, outgoing_mass_reconstruction hS huv hseg]
  ring

/-- The incoming mass density is integrable through its regular axis
endpoint, directly from the AC mass equation. No derivative envelope or box
constant is used. -/
theorem incoming_mass_density_integrable {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u ≤ v)
    (hseg : inSeg u v v ⊆ D) :
    IntervalIntegrable (fun x => (-S.nu x v) *
      ((1 - S.mu x v) * ‖S.xi x v / S.nu x v‖ ^ 2 +
        S.Q x v ^ 2 / S.r x v ^ 2)) volume u v := by
  have heq := integralForm_of_ac_of_interior_deriv huv (hS.ac_in u v v huv hseg).2.1
    (fun x hx => IsSolution.hasDerivAt_mass_in hS hseg hx)
  apply (heq.1.const_mul (-2)).congr
  intro x hx
  have hx' : x ∈ Icc u v := by
    simpa only [uIcc_of_le huv] using uIoc_subset_uIcc hx
  have hn := (hS.nu_neg (x, v) (hseg ⟨hx'.1, hx'.2, rfl⟩)).ne
  simp only [Fields.mU, norm_div, Complex.norm_real, Real.norm_eq_abs,
    div_pow, sq_abs]
  field_simp [hn]

/-- The incoming mass ratio uses the density in the same incoming orientation,
with its zero-axis endpoint. The identity has no estimate constants. -/
theorem incoming_mass_ratio_reconstruction {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u ≤ v)
    (hseg : inSeg u v v ⊆ D) :
    S.mu u v = (S.r u v)⁻¹ * ∫ x in u..v, (-S.nu x v) *
      ((1 - S.mu x v) * ‖S.xi x v / S.nu x v‖ ^ 2 + S.Q x v ^ 2 / S.r x v ^ 2) := by
  rw [Fields.mu, stab_incoming_mass hS huv hseg]
  ring

/-- Ordinary mass is nonnegative on a complete outgoing section. This is a
consequence of the positive mass flux and zero central mass, without an upper
gap assumption or any smallness requirement. -/
theorem mass_nonneg {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u ≤ v)
    (hseg : outSeg u u v ⊆ D) : 0 ≤ S.m u v := by
  have h : 0 ≤ 2 * S.m u v := by
    rw [outgoing_mass_reconstruction hS huv hseg]
    apply intervalIntegral.integral_nonneg huv
    intro x hx
    exact mul_nonneg (hS.lam_pos (u, x) (hseg ⟨rfl, hx⟩)).le
      (add_nonneg (mul_nonneg (hS.one_sub_mu_pos (u, x) (hseg ⟨rfl, hx⟩)).le
        (sq_nonneg _)) (div_nonneg (sq_nonneg _) (sq_nonneg _)))
  linarith

/-- The broad mass ratio is in `[0,1)` everywhere on a complete triangle,
including its zero-valued axis quotient. The endpoints are numerical and
uniform in all parameters and solutions. -/
theorem mu_mem_Ico {s t e u v : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle s t)) (hp : (u, v) ∈ triangle s t) :
    S.mu u v ∈ Ico 0 1 := by
  refine ⟨?_, by linarith [hS.one_sub_mu_pos (u, v) hp]⟩
  rcases eq_or_lt_of_le (show u ≤ v from hp.2.1) with huv | huv
  · subst v
    simp [Fields.mu, (hS.axis u hp).1]
  · have hs : outSeg u u v ⊆ triangle s t := by
      rintro p ⟨rfl, hx⟩
      exact ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩
    exact div_nonneg (mul_nonneg (by norm_num) (mass_nonneg hS huv.le hs))
      (hS.r_pos (u, v) hp huv).le

/-- The uniform broad mass-ratio distance. No constant or finiteness choice is
part of its definition; the bound one is proved from the mass constraints. -/
@[expose] noncomputable def mass_ratio_distance (s t : ℝ) (S₁ S₂ : Fields) : ℝ≥0∞ :=
  ⨆ p ∈ triangle s t, ENNReal.ofReal |S₁.mu p.1 p.2 - S₂.mu p.1 p.2|

/-- The mass-ratio distance is at most the universal numerical constant one,
independently of the competing solutions, triangle and coupling. -/
theorem mass_ratio_distance_le_one {s t e : ℝ} {S₁ S₂ : Fields}
    (hS₁ : IsSolution e S₁ (triangle s t)) (hS₂ : IsSolution e S₂ (triangle s t)) :
    mass_ratio_distance s t S₁ S₂ ≤ 1 := by
  apply iSup₂_le
  rintro ⟨u, v⟩ hp
  have h₁ := mu_mem_Ico hS₁ hp
  have h₂ := mu_mem_Ico hS₂ hp
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  exact abs_le.mpr ⟨by linarith [h₁.1, h₂.2], by linarith [h₁.2, h₂.1]⟩

/-- Each mass-ratio difference is bounded by its finite real uniform distance.
The coefficient one is universal. -/
theorem abs_mu_sub_le_mass_ratio_distance {s t e u v : ℝ} {S₁ S₂ : Fields}
    (hS₁ : IsSolution e S₁ (triangle s t)) (hS₂ : IsSolution e S₂ (triangle s t))
    (hp : (u, v) ∈ triangle s t) :
    |S₁.mu u v - S₂.mu u v| ≤ (mass_ratio_distance s t S₁ S₂).toReal := by
  apply (ENNReal.ofReal_le_iff_le_toReal (ne_top_of_le_ne_top (by norm_num)
    (mass_ratio_distance_le_one hS₁ hS₂))).mp
  exact le_iSup₂_of_le (u, v) hp le_rfl

/-- Polynomial electric domination controls both an outgoing radial mass
average and its subsequent weighted integral. The exact coefficients `1/3`
and `1/6` are universal, independently of the solution, interval, nonnegative
density and its bound. Integrability is a conclusion, including at the axis. -/
theorem outgoing_electric_averages_of_bound {e B : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u ≤ v)
    (hseg : outSeg u u v ⊆ D) (_hB : 0 ≤ B) {q : ℝ → ℝ}
    (hqmeas : AEStronglyMeasurable q (volume.restrict (Icc u v)))
    (hq : ∀ x ∈ Icc u v, 0 ≤ q x ∧ q x ≤ B * S.r u x ^ 2) :
    let A := fun x => (S.r u x)⁻¹ * ∫ y in u..x, S.lam u y * q y
    (∀ x ∈ Icc u v, 0 ≤ A x ∧ A x ≤ B * S.r u x ^ 2 / 3) ∧
      IntervalIntegrable (fun x => S.lam u x / S.r u x * A x) volume u v ∧
      (∫ x in u..v, S.lam u x / S.r u x * A x) ≤ B * S.r u v ^ 2 / 6 := by
  intro A
  have cl := continuousOn_out_section hS.cont_lam hseg
  have cr := continuousOn_out_section hS.cont_r hseg
  have hl x (hx : x ∈ Icc u v) : 0 ≤ S.lam u x :=
    (hS.lam_pos (u, x) (hseg ⟨rfl, hx⟩)).le
  have hr x (hx : x ∈ Icc u v) : 0 ≤ S.r u x := by
    rcases eq_or_lt_of_le hx.1 with hx0 | hx0
    · subst x; rw [(hS.axis u (hseg ⟨rfl, le_rfl, huv⟩)).1]
    · exact (hS.r_pos (u, x) (hseg ⟨rfl, hx⟩) hx0).le
  have ib : IntervalIntegrable (fun x => B * (S.lam u x * S.r u x ^ 2)) volume u v :=
    (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv (cl.mul (cr.pow 2))).const_mul B
  have iq : IntervalIntegrable (fun x => S.lam u x * q x) volume u v := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le huv] at ib ⊢
    apply ib.mono' (cl.aestronglyMeasurable (μ := volume) measurableSet_Icc |>.mul hqmeas)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    change ‖S.lam u x * q x‖ ≤ B * (S.lam u x * S.r u x ^ 2)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hl x hx) (hq x hx).1)]
    calc
      _ ≤ S.lam u x * (B * S.r u x ^ 2) :=
        mul_le_mul_of_nonneg_left (hq x hx).2 (hl x hx)
      _ = _ := by ring
  have hA x (hx : x ∈ Icc u v) : 0 ≤ A x ∧ A x ≤ B * S.r u x ^ 2 / 3 := by
    have hxsub : uIcc u x ⊆ uIcc u v := uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc hx)
    have hInt := intervalIntegral.integral_nonneg (μ := volume) hx.1 (fun y hy =>
      mul_nonneg (hl y ⟨hy.1, hy.2.trans hx.2⟩) (hq y ⟨hy.1, hy.2.trans hx.2⟩).1)
    refine ⟨mul_nonneg (inv_nonneg.mpr (hr x hx)) hInt, ?_⟩
    by_cases hr0 : S.r u x = 0
    · simp [A, hr0]
    · have hmono := intervalIntegral.integral_mono_on hx.1 (iq.mono_set hxsub)
        (ib.mono_set hxsub) (fun y hy => by
          have hy' : y ∈ Icc u v := ⟨hy.1, hy.2.trans hx.2⟩
          calc
            _ ≤ S.lam u y * (B * S.r u y ^ 2) :=
              mul_le_mul_of_nonneg_left (hq y hy').2 (hl y hy')
            _ = _ := by ring)
      have hs : outSeg u u x ⊆ D := by
        rintro p ⟨rfl, hp⟩
        exact hseg ⟨rfl, hp.1, hp.2.trans hx.2⟩
      have hm := outgoing_radius_moment hS hx.1 hs 2
      simp only [Nat.reduceAdd] at hm
      rw [intervalIntegral.integral_const_mul, hm] at hmono
      apply (mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr (hr x hx))).trans_eq
      field_simp [hr0]
      ring
  have hpoint x (hx : x ∈ Icc u v) :
      S.lam u x / S.r u x * A x ≤ (B / 3) * (S.lam u x * S.r u x) := by
    apply (mul_le_mul_of_nonneg_left (hA x hx).2 (div_nonneg (hl x hx) (hr x hx))).trans_eq
    by_cases hr0 : S.r u x = 0
    · simp [hr0]
    · field_simp [hr0]
  have ip := iq.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc |>.continuousOn
  rw [uIcc_of_le huv] at ip
  have hAmeas : AEStronglyMeasurable A (volume.restrict (Icc u v)) :=
    (cr.aestronglyMeasurable (μ := volume) measurableSet_Icc).inv₀.mul
      (ip.aestronglyMeasurable (μ := volume) measurableSet_Icc)
  have ic : IntervalIntegrable (fun x => (B / 3) * (S.lam u x * S.r u x)) volume u v :=
    (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv (cl.mul cr)).const_mul _
  have iA : IntervalIntegrable (fun x => S.lam u x / S.r u x * A x) volume u v := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le huv] at ic ⊢
    apply ic.mono' (((cl.aestronglyMeasurable (μ := volume) measurableSet_Icc).div₀
      (cr.aestronglyMeasurable (μ := volume) measurableSet_Icc)).mul hAmeas)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    change ‖S.lam u x / S.r u x * A x‖ ≤ B / 3 * (S.lam u x * S.r u x)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (div_nonneg (hl x hx) (hr x hx)) (hA x hx).1)]
    exact hpoint x hx
  refine ⟨hA, iA, ?_⟩
  have hb := intervalIntegral.integral_mono_on huv iA ic hpoint
  have hm : (∫ x in u..v, S.lam u x * S.r u x) = S.r u v ^ 2 / 2 := by
    simpa only [pow_one, Nat.reduceAdd, Nat.cast_one, one_add_one_eq_two] using
      outgoing_radius_moment hS huv hseg 1
  rw [intervalIntegral.integral_const_mul, hm] at hb
  exact hb.trans_eq (by ring)

/-- Polynomial electric domination in the incoming orientation, using the same
axis endpoint as the subsequent integration. The exact coefficients `1/3`
and `1/6` are universal, and finiteness at the singular endpoint is proved. -/
theorem incoming_electric_averages_of_bound {e B : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u ≤ v)
    (hseg : inSeg u v v ⊆ D) (_hB : 0 ≤ B) {q : ℝ → ℝ}
    (hqmeas : AEStronglyMeasurable q (volume.restrict (Icc u v)))
    (hq : ∀ x ∈ Icc u v, 0 ≤ q x ∧ q x ≤ B * S.r x v ^ 2) :
    let A := fun x => (S.r x v)⁻¹ * ∫ y in x..v, (-S.nu y v) * q y
    (∀ x ∈ Icc u v, 0 ≤ A x ∧ A x ≤ B * S.r x v ^ 2 / 3) ∧
      IntervalIntegrable (fun x => (-S.nu x v) / S.r x v * A x) volume u v ∧
      (∫ x in u..v, (-S.nu x v) / S.r x v * A x) ≤ B * S.r u v ^ 2 / 6 := by
  intro A
  have cl := (continuousOn_in_section hS.cont_nu hseg).neg
  have cr := continuousOn_in_section hS.cont_r hseg
  have hl x (hx : x ∈ Icc u v) : 0 ≤ -S.nu x v :=
    (neg_pos.mpr (hS.nu_neg (x, v) (hseg ⟨hx.1, hx.2, rfl⟩))).le
  have hr x (hx : x ∈ Icc u v) : 0 ≤ S.r x v := by
    rcases eq_or_lt_of_le hx.2 with hx0 | hx0
    · subst x; rw [(hS.axis v (hseg ⟨huv, le_rfl, rfl⟩)).1]
    · exact (hS.r_pos (x, v) (hseg ⟨hx.1, hx.2, rfl⟩) hx0).le
  have ib : IntervalIntegrable (fun x => B * ((-S.nu x v) * S.r x v ^ 2)) volume u v :=
    (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv (cl.mul (cr.pow 2))).const_mul B
  have iq : IntervalIntegrable (fun x => (-S.nu x v) * q x) volume u v := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le huv] at ib ⊢
    apply ib.mono' (cl.aestronglyMeasurable (μ := volume) measurableSet_Icc |>.mul hqmeas)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    change ‖(-S.nu x v) * q x‖ ≤ B * ((-S.nu x v) * S.r x v ^ 2)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hl x hx) (hq x hx).1)]
    calc
      _ ≤ (-S.nu x v) * (B * S.r x v ^ 2) :=
        mul_le_mul_of_nonneg_left (hq x hx).2 (hl x hx)
      _ = _ := by ring
  have hA x (hx : x ∈ Icc u v) : 0 ≤ A x ∧ A x ≤ B * S.r x v ^ 2 / 3 := by
    have hxsub : uIcc x v ⊆ uIcc u v :=
      uIcc_subset_uIcc (Icc_subset_uIcc hx) right_mem_uIcc
    have hInt := intervalIntegral.integral_nonneg (μ := volume) hx.2 (fun y hy =>
      mul_nonneg (hl y ⟨hx.1.trans hy.1, hy.2⟩) (hq y ⟨hx.1.trans hy.1, hy.2⟩).1)
    refine ⟨mul_nonneg (inv_nonneg.mpr (hr x hx)) hInt, ?_⟩
    by_cases hr0 : S.r x v = 0
    · simp [A, hr0]
    · have hmono := intervalIntegral.integral_mono_on hx.2 (iq.mono_set hxsub)
        (ib.mono_set hxsub) (fun y hy => by
          have hy' : y ∈ Icc u v := ⟨hx.1.trans hy.1, hy.2⟩
          calc
            _ ≤ (-S.nu y v) * (B * S.r y v ^ 2) :=
              mul_le_mul_of_nonneg_left (hq y hy').2 (hl y hy')
            _ = _ := by ring)
      have hs : inSeg x v v ⊆ D := by
        rintro p ⟨hp₁, hp₂, rfl⟩
        exact hseg ⟨hx.1.trans hp₁, hp₂, rfl⟩
      have hm := incoming_radius_moment hS hx.2 hs 2
      simp only [Nat.reduceAdd] at hm
      rw [intervalIntegral.integral_const_mul, hm] at hmono
      apply (mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr (hr x hx))).trans_eq
      field_simp [hr0]
      ring
  have hpoint x (hx : x ∈ Icc u v) :
      (-S.nu x v) / S.r x v * A x ≤ (B / 3) * ((-S.nu x v) * S.r x v) := by
    apply (mul_le_mul_of_nonneg_left (hA x hx).2 (div_nonneg (hl x hx) (hr x hx))).trans_eq
    by_cases hr0 : S.r x v = 0
    · simp [hr0]
    · field_simp [hr0]
  have ip := iq.absolutelyContinuousOnInterval_intervalIntegral right_mem_uIcc |>.continuousOn
  rw [uIcc_of_le huv] at ip
  have ip' : ContinuousOn (fun x => ∫ y in x..v, (-S.nu y v) * q y) (Icc u v) := by
    apply ip.neg.congr
    intro x _
    exact intervalIntegral.integral_symm
      (f := fun y => (-S.nu y v) * q y) (μ := volume) v x
  have hAmeas : AEStronglyMeasurable A (volume.restrict (Icc u v)) :=
    (cr.aestronglyMeasurable (μ := volume) measurableSet_Icc).inv₀.mul
      (ip'.aestronglyMeasurable (μ := volume) measurableSet_Icc)
  have ic : IntervalIntegrable (fun x => (B / 3) * ((-S.nu x v) * S.r x v)) volume u v :=
    (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv (cl.mul cr)).const_mul _
  have iA : IntervalIntegrable (fun x => (-S.nu x v) / S.r x v * A x) volume u v := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le huv] at ic ⊢
    apply ic.mono' (((cl.aestronglyMeasurable (μ := volume) measurableSet_Icc).div₀
      (cr.aestronglyMeasurable (μ := volume) measurableSet_Icc)).mul hAmeas)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    change ‖(-S.nu x v) / S.r x v * A x‖ ≤ B / 3 * ((-S.nu x v) * S.r x v)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (div_nonneg (hl x hx) (hr x hx)) (hA x hx).1)]
    exact hpoint x hx
  refine ⟨hA, iA, ?_⟩
  have hb := intervalIntegral.integral_mono_on huv iA ic hpoint
  have hm : (∫ x in u..v, (-S.nu x v) * S.r x v) = S.r u v ^ 2 / 2 := by
    simpa only [pow_one, Nat.reduceAdd, Nat.cast_one, one_add_one_eq_two] using
      incoming_radius_moment hS huv hseg 1
  rw [intervalIntegral.integral_const_mul, hm] at hb
  exact hb.trans_eq (by ring)

/-- [node restart-stab-broad-uniqueness#charged-mass-average-difference]
Electric-square comparison and its mass averages in both matching
orientations, charged_SF_new_version.tex:L5718–5726. For a fixed box `c,C`, the positive
constant is independent of all triangle, coupling, scalar-size, ratio-size,
solution and section parameters. All singular weighted integrals are proved
integrable; no derivative envelope is assumed. -/
theorem charged_mass_average_difference (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s t e M ε : ℝ) (S₁ S₂ : Fields),
      IsSolution e S₁ (triangle s t) → IsSolution e S₂ (triangle s t) →
      1 ≤ M → 0 ≤ ε → ε ≤ 1 →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s t,
        c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C ∧
          ‖S.phi p.1 p.2‖ ≤ M ∧ ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ ε) →
      (∀ u v, (u, v) ∈ triangle s t → ∀ x ∈ Icc u v, ∀ y ∈ Icc u v,
        ‖S₂.a u x - S₂.a u y‖ ≤ ε) →
      let E := (normalized_field_distance s t S₁ S₂).toReal +
        ε * (geometry_distance s t S₁ S₂).toReal
      let σ := e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2
      let q := fun u v => |S₁.Q u v ^ 2 / S₁.r u v ^ 2 - S₂.Q u v ^ 2 / S₂.r u v ^ 2|
      ∀ u v, (u, v) ∈ triangle s t →
        q u v ≤ K * e ^ 2 * M ^ 2 * ε * S₁.r u v ^ 2 * E ∧
        let Ao := fun x => (S₁.r u x)⁻¹ * ∫ y in u..x, S₁.lam u y * q u y
        let Ai := fun x => (S₁.r x v)⁻¹ * ∫ y in x..v, (-S₁.nu y v) * q y v
        Ao v ≤ K * σ * ε * E ∧ Ai u ≤ K * σ * ε * E ∧
          IntervalIntegrable (fun x => S₁.lam u x / S₁.r u x * Ao x) volume u v ∧
          (∫ x in u..v, S₁.lam u x / S₁.r u x * Ao x) ≤ K * σ * ε * E ∧
          IntervalIntegrable (fun x => (-S₁.nu x v) / S₁.r x v * Ai x) volume u v ∧
          (∫ x in u..v, (-S₁.nu x v) / S₁.r x v * Ai x) ≤ K * σ * ε * E := by
  obtain ⟨Kq, hKq, hq⟩ := charged_square_difference c C hc hC
  let K := Kq + 4 * C ^ 2 * Kq
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro s t e M ε S₁ S₂ hS₁ hS₂ hM hε hε1 hbox hosc E σ q u v hp
  have hmem₁ : S₁ ∈ ({S₁, S₂} : Set Fields) := by simp
  have hqbound (x y : ℝ) (hxy : (x, y) ∈ triangle s t) :
      q x y ≤ Kq * e ^ 2 * M ^ 2 * ε * S₁.r x y ^ 2 * E :=
    hq s t e M ε S₁ S₂ hS₁ hS₂ hM hε hε1 hbox hosc x y hxy
  have hE : 0 ≤ E := by dsimp [E]; positivity
  let B := Kq * e ^ 2 * M ^ 2 * ε * E
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hK : Kq ≤ K := le_add_of_nonneg_right (by positivity)
  have hso : outSeg u u v ⊆ triangle s t := by
    rintro p ⟨rfl, hx⟩
    exact ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩
  have hsi : inSeg u v v ⊆ triangle s t := by
    rintro p ⟨hx, hy, rfl⟩
    exact ⟨hp.1.trans hx, hy, hp.2.2⟩
  have qmeas_out : AEStronglyMeasurable (fun x => q u x) (volume.restrict (Icc u v)) := by
    have cq₁ := (continuousOn_out_section hS₁.cont_Q hso).pow 2
    have cr₁ := (continuousOn_out_section hS₁.cont_r hso).pow 2
    have cq₂ := (continuousOn_out_section hS₂.cont_Q hso).pow 2
    have cr₂ := (continuousOn_out_section hS₂.cont_r hso).pow 2
    have h := ((cq₁.aestronglyMeasurable (μ := volume) measurableSet_Icc).div₀
      (cr₁.aestronglyMeasurable (μ := volume) measurableSet_Icc)).sub
        ((cq₂.aestronglyMeasurable (μ := volume) measurableSet_Icc).div₀
          (cr₂.aestronglyMeasurable (μ := volume) measurableSet_Icc)) |>.norm
    simpa only [q, Real.norm_eq_abs, Pi.sub_apply, Pi.div_apply, Pi.pow_apply] using! h
  have qmeas_in : AEStronglyMeasurable (fun x => q x v) (volume.restrict (Icc u v)) := by
    have cq₁ := (continuousOn_in_section hS₁.cont_Q hsi).pow 2
    have cr₁ := (continuousOn_in_section hS₁.cont_r hsi).pow 2
    have cq₂ := (continuousOn_in_section hS₂.cont_Q hsi).pow 2
    have cr₂ := (continuousOn_in_section hS₂.cont_r hsi).pow 2
    have h := ((cq₁.aestronglyMeasurable (μ := volume) measurableSet_Icc).div₀
      (cr₁.aestronglyMeasurable (μ := volume) measurableSet_Icc)).sub
        ((cq₂.aestronglyMeasurable (μ := volume) measurableSet_Icc).div₀
          (cr₂.aestronglyMeasurable (μ := volume) measurableSet_Icc)) |>.norm
    simpa only [q, Real.norm_eq_abs, Pi.sub_apply, Pi.div_apply, Pi.pow_apply] using! h
  have hO := outgoing_electric_averages_of_bound hS₁ hp.2.1 hso hB qmeas_out (fun x hx =>
    ⟨abs_nonneg _, (hqbound u x (hso ⟨rfl, hx⟩)).trans_eq (by dsimp [B]; ring)⟩)
  have hI := incoming_electric_averages_of_bound hS₁ hp.2.1 hsi hB qmeas_in (fun x hx =>
    ⟨abs_nonneg _, (hqbound x v (hsi ⟨hx.1, hx.2, rfl⟩)).trans_eq (by dsimp [B]; ring)⟩)
  have hst : 0 ≤ t - s := by linarith [hp.1, hp.2.1, hp.2.2]
  have hlo := outgoing_radius_lower hS₁ hp.2.1 hso
    (fun x hx => (hbox S₁ hmem₁ (u, x) (hso ⟨rfl, hx⟩)).1)
  have hr0 : 0 ≤ S₁.r u v :=
    (mul_nonneg hc.le (sub_nonneg.mpr hp.2.1)).trans hlo
  have hup := outgoing_radius_upper hS₁ hp.2.1 hso
    (fun x hx => (hbox S₁ hmem₁ (u, x) (hso ⟨rfl, hx⟩)).2.1)
  have hR : S₁.r u v ≤ C * (t - s) := hup.trans
    (mul_le_mul_of_nonneg_left (by linarith [hp.1, hp.2.2]) hC)
  have hcost : B * S₁.r u v ^ 2 ≤ K * σ * ε * E := by
    calc
      _ ≤ B * (C * (t - s)) ^ 2 := by gcongr
      _ = (4 * C ^ 2 * Kq) * σ * ε * E := by dsimp [B, σ]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hE
        apply mul_le_mul_of_nonneg_right _ hε
        apply mul_le_mul_of_nonneg_right _ (by dsimp [σ]; positivity)
        exact le_add_of_nonneg_left hKq.le
  have h3 : B * S₁.r u v ^ 2 / 3 ≤ K * σ * ε * E :=
    (by have h0 := mul_nonneg hB (sq_nonneg (S₁.r u v)); linarith [hcost])
  have h6 : B * S₁.r u v ^ 2 / 6 ≤ K * σ * ε * E :=
    (by have h0 := mul_nonneg hB (sq_nonneg (S₁.r u v)); linarith [hcost])
  refine ⟨(hqbound u v hp).trans ?_, ?_⟩
  · gcongr
  · intro Ao Ai
    exact ⟨((hO.1 v (right_mem_Icc.mpr hp.2.1)).2).trans h3,
      ((hI.1 u (left_mem_Icc.mpr hp.2.1)).2).trans h3,
      hO.2.1, hO.2.2.trans h6, hI.2.1, hI.2.2.trans h6⟩

end EmcsfAcExtension.Local.Broad
