module

public import EmcsfAcExtension.Local.Calculus.Reconstruction

/-! # Endpoint estimates from integrable broad scalar derivatives

Only continuity of the transported field and integrability of its
ordinary interior derivative are needed. No incoming AC trace is assumed.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local.Broad

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- An integrable interior derivative controls every prefix increment,
including the terminal endpoint, with the exact full norm integral. -/
theorem norm_increment_le_integral_norm {a b x : ℝ} {f g : ℝ → E}
    (_hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ y ∈ Ioo a b, HasDerivAt f (g y) y)
    (ig : IntervalIntegrable g volume a b) (hx : x ∈ Icc a b) :
    ‖f x - f a‖ ≤ ∫ y in a..b, ‖g y‖ := by
  have isub := ig.mono_set (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc hx))
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
    (hf.mono (Icc_subset_Icc le_rfl hx.2))
    (fun y hy => hd y ⟨hy.1, hy.2.trans_le hx.2⟩) isub
  rw [← heq]
  apply (intervalIntegral.norm_integral_le_integral_norm hx.1).trans
  exact intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2
    (Filter.Eventually.of_forall (fun y => norm_nonneg (g y))) ig.norm

/-- Three integrable sources bound a continuous transported field by the
sum of their full norm integrals. All comparison coefficients are one. -/
theorem norm_increment_le_three_integrals {a b x : ℝ} {f g h k : ℝ → E}
    (_hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ y ∈ Ioo a b, HasDerivAt f (g y + h y + k y) y)
    (ig : IntervalIntegrable g volume a b) (ih : IntervalIntegrable h volume a b)
    (ik : IntervalIntegrable k volume a b) (hx : x ∈ Icc a b) :
    ‖f x - f a‖ ≤ (∫ y in a..b, ‖g y‖) + (∫ y in a..b, ‖h y‖) +
      (∫ y in a..b, ‖k y‖) := by
  apply (norm_increment_le_integral_norm _hab hf hd ((ig.add ih).add ik) hx).trans
  have hh := intervalIntegral.integral_mono_on _hab ((ig.add ih).add ik).norm
    ((ig.norm.add ih.norm).add ik.norm) (fun y _ =>
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl))
  simpa only [intervalIntegral.integral_add, ig.norm, ih.norm, ik.norm,
    ig.norm.add ih.norm] using hh

end EmcsfAcExtension.Local.Broad
