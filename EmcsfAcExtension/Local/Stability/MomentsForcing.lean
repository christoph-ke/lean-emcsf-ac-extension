module

public import EmcsfAcExtension.Local.Stability.MomentsSections

/-! # Measurability of the radial stability forcing

Dividing `j` or `k` by `1 - μ` cancels the prefactor in its definition.
This proves sectional measurability without assuming continuity of `μ` at
the axis, or continuity of the characteristic envelopes.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension.Local

variable {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}

/-- The outgoing radial forcing has a measurable norm on every closed
section. No additional regularity of the label envelope is assumed. -/
theorem stab_out_forcing_measurable (hset : StabSetting e T ε M A S h) {u v : ℝ}
    (hu : 0 ≤ u) (_huv : u ≤ v) (hvT : v ≤ T) :
    AEStronglyMeasurable
      (fun s => ‖jC1 (triangle 0 T) S u s / ((1 - S.mu u s : ℝ) : ℂ)‖)
      (volume.restrict (Icc u v)) := by
  have hsec {E : Type} [NormedAddCommGroup E] {f : ℝ × ℝ → E}
      (hf : ContinuousOn f (triangle 0 T)) :
      AEStronglyMeasurable (fun s => f (u, s)) (volume.restrict (Icc u v)) :=
    (hf.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨hu, hs.1, hs.2.trans hvT⟩)).aestronglyMeasurable measurableSet_Icc
  have hpd := hsec (continuousOn_partial_v (stab_normalized_out_c1 hset.c1)
    (uniqueDiffOn_triangle hset.pos))
  have hl := hsec hset.c1.c1_lam.continuousOn
  have hr := hsec hset.c1.c1_r.continuousOn
  have hx := hsec (stab_out_ratio_c1 hset.c1).continuousOn
  have hcoeff := Complex.continuous_ofReal.comp_aestronglyMeasurable
    ((hl.div₀ hr).mul (hx.norm.pow 2))
  have hq := (hpd.sub (hcoeff.mul hx)).norm
  apply hq.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  have hγ : (1 - (S.mu u s : ℂ)) ≠ 0 := by
    exact_mod_cast (hset.c1.one_sub_mu_pos (u, s)
      ⟨hu, hs.1, hs.2.trans hvT⟩).ne'
  simp only [jC1, pdV, Function.uncurry_apply_pair, Pi.sub_apply, Pi.mul_apply,
    Pi.div_apply, Pi.pow_apply]
  push_cast
  rw [mul_div_cancel_left₀ _ hγ]

/-- The incoming covariant radial forcing has a measurable norm on every
closed section. The connection term is part of the measurable forcing. -/
theorem stab_in_forcing_measurable (hset : StabSetting e T ε M A S h) {u v : ℝ}
    (hu : 0 ≤ u) (_huv : u ≤ v) (hvT : v ≤ T) :
    AEStronglyMeasurable
      (fun s => ‖kC1 e (triangle 0 T) S s v / ((1 - S.mu s v : ℝ) : ℂ)‖)
      (volume.restrict (Icc u v)) := by
  have hsec {E : Type} [NormedAddCommGroup E] {f : ℝ × ℝ → E}
      (hf : ContinuousOn f (triangle 0 T)) :
      AEStronglyMeasurable (fun s => f (s, v)) (volume.restrict (Icc u v)) :=
    (hf.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hu.trans hs.1, hs.2, hvT⟩)).aestronglyMeasurable measurableSet_Icc
  have hpd := hsec (continuousOn_partial_u (stab_normalized_in_c1 hset.c1)
    (uniqueDiffOn_triangle hset.pos))
  have hn := hsec hset.c1.c1_nu.continuousOn
  have hr := hsec hset.c1.c1_r.continuousOn
  have hy := hsec (stab_in_ratio_c1 hset.c1).continuousOn
  have hA := hsec hset.c1.c1_A.continuousOn
  have hb := hsec (stab_normalized_in_c1 hset.c1).continuousOn
  have hcoeff := Complex.continuous_ofReal.comp_aestronglyMeasurable
    ((hn.div₀ hr).mul (hy.norm.pow 2))
  have hAc := Complex.continuous_ofReal.comp_aestronglyMeasurable hA
  have hq := ((hpd.add ((hAc.const_mul (Complex.I * e)).mul hb)).sub
    (hcoeff.mul hy)).norm
  apply hq.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  have hγ : (1 - (S.mu s v : ℂ)) ≠ 0 := by
    exact_mod_cast (hset.c1.one_sub_mu_pos (s, v)
      ⟨hu.trans hs.1, hs.2, hvT⟩).ne'
  simp only [kC1, pdU, Function.uncurry_apply_pair, Pi.sub_apply, Pi.mul_apply,
    Pi.div_apply, Pi.pow_apply, Pi.add_apply]
  push_cast
  rw [mul_div_cancel_left₀ _ hγ]

/-- In the fixed box, division by `1 - μ` costs at most the exact universal
factor `4`. The complex numerator is arbitrary. -/
theorem stab_forcing_norm_le (hset : StabSetting e T ε M A S h) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) (z : ℂ) :
    ‖z / ((1 - S.mu u v : ℝ) : ℂ)‖ ≤ 4 * ‖z‖ := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv, hvT⟩
  have hγ := (hset.box.2 (u, v) hp).2.2.2.2.1
  have hγ0 := hset.c1.one_sub_mu_pos (u, v) hp
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hγ0]
  apply (div_le_iff₀ hγ0).2
  have hm := mul_le_mul_of_nonneg_left hγ (norm_nonneg z)
  linarith only [hm]

end EmcsfAcExtension.Local
