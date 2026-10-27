module

public import EmcsfAcExtension.Global.Exterior.DerivativeSource
public import EmcsfAcExtension.Global.Exterior.DerivativeSourceTerminal

/-! # Neutral moments for the exterior derivative source

The neutral cubic and mass terms of the exact derivative source are bounded
using scalar energy and the reciprocal-radius moment. All constants are
numerical and uniform in the solution, coupling, row and endpoint.
Source: `charged_SF_new_version.tex:L1298–L1325`, approved internal project record (S3)–(S4).
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Exterior

variable {ui e : ℝ} {S : Fields}

/-- [internal]
The neutral cubic moment is at most `4 M SF / ell²`. The coefficient `4`
is universal; `SF` bounds only the undifferentiated normalized field. -/
theorem source_neutral_cubic_bound_of_profiles (h : OriginalData ui e S)
    {u a SF : ℝ} (hua : u < a) (ha : a ≤ 0)
    (hs : outSeg u a 0 ⊆ origDomain ui)
    (hg : ∀ v ∈ Icc a 0, 1 / 2 ≤ 1 - S.mu u v)
    (hF : ∀ v ∈ Icc a 0, ‖S.theta u v / (S.lam u v : ℂ)‖ ≤ SF) :
    (∫ v in a..0, ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 3 /
      S.r u v ^ 2 * S.lam u v) ≤ 4 * terminalMass S u * SF / S.r u a ^ 2 := by
  have hr (v : ℝ) (hv : v ∈ Icc a 0) :=
    h.solution.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
  have hl (v : ℝ) (hv : v ∈ Icc a 0) :=
    h.solution.lam_pos (u, v) (hs ⟨rfl, hv⟩)
  have cr := Calculus.continuousOn_out_section h.solution.cont_r hs
  have cl := Calculus.continuousOn_out_section h.solution.cont_lam hs
  have cF : ContinuousOn (fun v => ‖S.theta u v / (S.lam u v : ℂ)‖) (Icc a 0) :=
    ((Calculus.continuousOn_out_section h.solution.cont_theta hs).div
    (Complex.continuous_ofReal.comp_continuousOn cl)
    (fun v hv => Complex.ofReal_ne_zero.mpr (hl v hv).ne')).norm
  have hSF : 0 ≤ SF := (norm_nonneg _).trans (hF a ⟨le_rfl, ha⟩)
  have hi := (((cF.pow 3).div (cr.pow 2)
    (fun v hv => pow_ne_zero _ (hr v hv).ne')).mul cl).intervalIntegrable_of_Icc
    (μ := volume) ha
  have hj := (((cF.pow 2).mul cl).const_mul (SF / S.r u a ^ 2)).intervalIntegrable_of_Icc
    (μ := volume) ha
  calc
    _ ≤ ∫ v in a..0, (SF / S.r u a ^ 2) *
        (‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v) := by
      apply intervalIntegral.integral_mono_on ha hi hj
      intro v hv
      have hrl := outgoing_radius_mono h hua.le hv.1
        (fun _ hx => hs (outSeg_subset_outSeg le_rfl hv.2 hx))
      have hb : ‖S.theta u v / (S.lam u v : ℂ)‖ / S.r u v ^ 2 ≤ SF / S.r u a ^ 2 :=
        (div_le_div_of_nonneg_right (hF v hv) (sq_nonneg _)).trans
          (div_le_div_of_nonneg_left hSF (sq_pos_of_pos (hr a ⟨le_rfl, ha⟩))
            (pow_le_pow_left₀ (hr a ⟨le_rfl, ha⟩).le hrl 2))
      have hh := mul_le_mul_of_nonneg_right hb
        (mul_nonneg (sq_nonneg ‖S.theta u v / (S.lam u v : ℂ)‖) (hl v hv).le)
      convert hh using 1
      all_goals dsimp only [Pi.pow_apply, Pi.mul_apply, Pi.div_apply, Function.comp_apply,
        terminalMass]
      all_goals ring
    _ = (SF / S.r u a ^ 2) * ∫ v in a..0,
        ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (scalar_energy_le_of_gap h hua ha hs hg)
        (div_nonneg hSF (sq_nonneg (S.r u a)))
      convert hh using 1
      all_goals dsimp only [Pi.pow_apply, Pi.mul_apply, Pi.div_apply, Function.comp_apply,
        terminalMass]
      all_goals ring

/-- [internal]
The scalar reciprocal-radius moment is at most `2 sqrt(M/ell)`.
The coefficient `2` is universal and follows from the proved energy. -/
theorem source_scalar_inverse_moment_of_gap (h : OriginalData ui e S)
    {u a : ℝ} (hua : u < a) (ha : a ≤ 0)
    (hs : outSeg u a 0 ⊆ origDomain ui)
    (hg : ∀ v ∈ Icc a 0, 1 / 2 ≤ 1 - S.mu u v) :
    (∫ v in a..0, ‖S.theta u v / (S.lam u v : ℂ)‖ / S.r u v * S.lam u v) ≤
      2 * Real.sqrt (terminalMass S u / S.r u a) := by
  have hr (v : ℝ) (hv : v ∈ Icc a 0) :=
    h.solution.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
  have hl (v : ℝ) (hv : v ∈ Icc a 0) :=
    h.solution.lam_pos (u, v) (hs ⟨rfl, hv⟩)
  have cr := Calculus.continuousOn_out_section h.solution.cont_r hs
  have cl := Calculus.continuousOn_out_section h.solution.cont_lam hs
  have cF : ContinuousOn (fun v => ‖S.theta u v / (S.lam u v : ℂ)‖) (Icc a 0) :=
    ((Calculus.continuousOn_out_section h.solution.cont_theta hs).div
    (Complex.continuous_ofReal.comp_continuousOn cl)
    (fun v hv => Complex.ofReal_ne_zero.mpr (hl v hv).ne')).norm
  have hc := weighted_integral_cauchy_schwarz ha cF
    (cr.inv₀ (fun v hv => (hr v hv).ne')) cl (fun v hv => (hl v hv).le)
  have he := scalar_energy_le_of_gap h hua ha hs hg
  have hm : (∫ v in a..0, (S.r u v)⁻¹ ^ 2 * S.lam u v) ≤ (S.r u a)⁻¹ := by
    have heq : (∫ v in a..0, (S.r u v)⁻¹ ^ 2 * S.lam u v) =
        ∫ v in a..0, S.lam u v / S.r u v ^ 2 := by
      apply intervalIntegral.integral_congr
      intro v _
      simp only [inv_pow, div_eq_mul_inv, mul_comm]
    rw [heq, inverse_radius_moment h hua ha hs]
    exact sub_le_self _ (inv_nonneg.mpr (hr 0 ⟨ha, le_rfl⟩).le)
  have hM := mass_nonneg h (hs ⟨rfl, ha, le_rfl⟩)
  have hgn := intervalIntegral.integral_nonneg (μ := volume) ha
    (fun v hv => mul_nonneg (sq_nonneg ((S.r u v)⁻¹)) (hl v hv).le)
  have hprod := mul_le_mul he hm hgn (by positivity)
  have hsq := hc.trans hprod
  have hsqrt := Real.sq_sqrt (div_nonneg hM (hr a ⟨le_rfl, ha⟩).le)
  simp only [Pi.inv_apply, ← div_eq_mul_inv] at hsq
  simp only [mul_div_assoc] at hsq
  dsimp only [terminalMass] at hsq hsqrt ⊢
  nlinarith only [hsq, hsqrt, Real.sqrt_nonneg (S.m u 0 / S.r u a)]

/-- [internal]
The mass-source moment is at most `2 (M/ell²) sqrt(M/ell)`.
The coefficient `2` is universal; this deliberately avoids fractional
powers and uses the proved scalar reciprocal-radius moment. -/
theorem source_mass_bound_of_gap (h : OriginalData ui e S)
    {u a : ℝ} (hua : u < a) (ha : a ≤ 0)
    (hs : outSeg u a 0 ⊆ origDomain ui)
    (hg : ∀ v ∈ Icc a 0, 1 / 2 ≤ 1 - S.mu u v) :
    (∫ v in a..0, terminalMass S u *
      ‖S.theta u v / (S.lam u v : ℂ)‖ / S.r u v ^ 3 * S.lam u v) ≤
      2 * (terminalMass S u / S.r u a ^ 2) *
        Real.sqrt (terminalMass S u / S.r u a) := by
  have hr (v : ℝ) (hv : v ∈ Icc a 0) :=
    h.solution.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
  have hl (v : ℝ) (hv : v ∈ Icc a 0) :=
    h.solution.lam_pos (u, v) (hs ⟨rfl, hv⟩)
  have cr := Calculus.continuousOn_out_section h.solution.cont_r hs
  have cl := Calculus.continuousOn_out_section h.solution.cont_lam hs
  have cF : ContinuousOn (fun v => ‖S.theta u v / (S.lam u v : ℂ)‖) (Icc a 0) :=
    ((Calculus.continuousOn_out_section h.solution.cont_theta hs).div
    (Complex.continuous_ofReal.comp_continuousOn cl)
    (fun v hv => Complex.ofReal_ne_zero.mpr (hl v hv).ne')).norm
  have hM := mass_nonneg h (hs ⟨rfl, ha, le_rfl⟩)
  have hi := ((((cF.const_mul (terminalMass S u)).div (cr.pow 3)
    (fun v hv => pow_ne_zero _ (hr v hv).ne')).mul cl)).intervalIntegrable_of_Icc
    (μ := volume) ha
  have hj := (((cF.div cr (fun v hv => (hr v hv).ne')).mul cl).const_mul
    (terminalMass S u / S.r u a ^ 2)).intervalIntegrable_of_Icc (μ := volume) ha
  calc
    _ ≤ ∫ v in a..0, (terminalMass S u / S.r u a ^ 2) *
        (‖S.theta u v / (S.lam u v : ℂ)‖ / S.r u v * S.lam u v) := by
      apply intervalIntegral.integral_mono_on ha hi hj
      intro v hv
      have hrl := outgoing_radius_mono h hua.le hv.1
        (fun _ hx => hs (outSeg_subset_outSeg le_rfl hv.2 hx))
      have hb := div_le_div_of_nonneg_left hM (sq_pos_of_pos (hr a ⟨le_rfl, ha⟩))
        (pow_le_pow_left₀ (hr a ⟨le_rfl, ha⟩).le hrl 2)
      have hh := mul_le_mul_of_nonneg_right hb
        (mul_nonneg (div_nonneg (norm_nonneg (S.theta u v / (S.lam u v : ℂ)))
          (hr v hv).le) (hl v hv).le)
      convert hh using 1
      all_goals dsimp only [Pi.pow_apply, Pi.mul_apply, Pi.div_apply, Function.comp_apply,
        terminalMass]
      all_goals ring
    _ = (terminalMass S u / S.r u a ^ 2) * ∫ v in a..0,
        ‖S.theta u v / (S.lam u v : ℂ)‖ / S.r u v * S.lam u v :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (source_scalar_inverse_moment_of_gap h hua ha hs hg)
        (div_nonneg hM (sq_nonneg (S.r u a)))
      convert hh using 1
      all_goals dsimp only [Pi.pow_apply, Pi.mul_apply, Pi.div_apply, Function.comp_apply,
        terminalMass]
      all_goals ring

end EmcsfAcExtension.Global.Exterior
