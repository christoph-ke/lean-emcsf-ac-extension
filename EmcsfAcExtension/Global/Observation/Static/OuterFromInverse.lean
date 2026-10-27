module

public import EmcsfAcExtension.Global.Observation.Static.Outer
import EmcsfAcExtension.Global.Observation.BoundaryData
import EmcsfAcExtension.Infra.Null.IntegralForm
import Mathlib

/-! # Radial outer comparison fields from a chosen inverse-radius family

The inverse-radius trajectory remains explicit so that its endpoint can
be matched to the same member of the stopped inner family.
Source: charged_SF_new_version.tex:L2168–2239; approved internal project record static references.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
Convert a chosen checked outer inverse-radius solution to all static
fields required by the outer comparison. The scalar coefficient is
`C+1`, uniformly in both radii and normalized parameters. Retaining the
literal trajectory makes its boundary mass and ratio available for
matching to its own stopped inner continuation. No radial derivative
or radial estimate is assumed. -/
theorem outer_radial_reference_of_inverse_solution
    {Lzero L M q C : ℝ} {P : ℂ} (h128 : 128 ≤ Lzero) (hL : Lzero ≤ L)
    (_hC : 0 < C) (z : ℝ → ℝ × ℝ × ℂ)
    (hzinit : z L⁻¹ = (M, 1 / 2, P * (L⁻¹ : ℝ)))
    (hz : ∀ x ∈ Icc L⁻¹ Lzero⁻¹,
      HasDerivAt z (staticInvRadiusRHS P q x (z x)) x ∧
      (z x).2.1 ∈ Icc (1 / 4) 1 ∧ |(z x).1| ≤ 2 ∧
      1 / 2 ≤ 1 - 2 * x * (z x).1 ∧
      ‖(z x).2.2‖ + ‖(P / ((2 * (z x).2.1 : ℝ) : ℂ)) * x‖ ≤ C * x ∧
      ‖(z x).2.2 - (P / ((2 * (z x).2.1 : ℝ) : ℂ)) * x‖ ≤ C * x ^ 2) :
    ∃ (phi y : ℝ → ℂ) (m : ℝ → ℝ),
    (∀ r, m r = (z r⁻¹).1) ∧ (∀ r, phi r = (z r⁻¹).2.2) ∧
      (∀ r, y r = -P / ((2 * r * (z r⁻¹).2.1 : ℝ) : ℂ)) ∧
    AbsolutelyContinuousOnInterval m Lzero L ∧
      ContinuousOn phi (Icc Lzero L) ∧ ContinuousOn y (Icc Lzero L) ∧
      m L = M ∧ phi L = P / (L : ℂ) ∧ phi L + y L = 0 ∧
      (∀ r ∈ Icc Lzero L,
        let k := (2 * m r / r - q ^ 2 / r ^ 2) / (1 - 2 * m r / r)
        HasDerivAt (fun s : ℝ => (s : ℂ) * phi s) (phi r + y r) r ∧
        HasDerivAt (fun s => phi s + y s) ((-k / r : ℝ) * y r) r ∧
        HasDerivAt m ((1 - 2 * m r / r) * ‖y r‖ ^ 2 / 2 + q ^ 2 / (2 * r ^ 2)) r) ∧
      ∀ r ∈ Icc Lzero L,
        |m r| ≤ 2 ∧ ‖y r‖ ≤ (C + 1) / r ∧ |1 - 2 * m r / r| ≤ 2 ∧
        ‖(r : ℂ) * phi r‖ ≤ C + 1 ∧ ‖phi r + y r‖ ≤ (C + 1) / r ^ 2 ∧
        1 / 2 ≤ 1 - 2 * m r / r := by
  have hLzeroPos : 0 < Lzero := lt_of_lt_of_le (by norm_num) h128
  have hLpos : 0 < L := hLzeroPos.trans_le hL
  let m := fun r : ℝ => (z r⁻¹).1
  let lam := fun r : ℝ => (z r⁻¹).2.1
  let phi := fun r : ℝ => (z r⁻¹).2.2
  let y := fun r : ℝ => -P / ((2 * r * lam r : ℝ) : ℂ)
  have hpos (r : ℝ) (hr : r ∈ Icc Lzero L) : 0 < r := hLzeroPos.trans_le hr.1
  have hinv (r : ℝ) (hr : r ∈ Icc Lzero L) : r⁻¹ ∈ Icc L⁻¹ Lzero⁻¹ :=
    by simpa only [one_div, mem_Icc] using
      (show 1 / L ≤ 1 / r ∧ 1 / r ≤ 1 / Lzero from
        ⟨one_div_le_one_div_of_le (hpos r hr) hr.2,
          one_div_le_one_div_of_le hLzeroPos hr.1⟩)
  have hradial (r : ℝ) (hr : r ∈ Icc Lzero L) :=
    static_radial_equations_of_solution (hpos r hr) (hz _ (hinv r hr)).1
      (lt_of_lt_of_le (by norm_num) (hz _ (hinv r hr)).2.1.1)
      (lt_of_lt_of_le (by norm_num) (hz _ (hinv r hr)).2.2.2.1)
  have cm : ContinuousOn m (Icc Lzero L) := fun r hr =>
    (hradial r hr).2.1.continuousAt.continuousWithinAt
  have cy : ContinuousOn y (Icc Lzero L) := fun r hr =>
    (hradial r hr).2.2.1.continuousAt.continuousWithinAt
  have cp : ContinuousOn phi (Icc Lzero L) := fun r hr =>
    (hradial r hr).2.2.2.1.continuousAt.continuousWithinAt
  let density := fun r => (1 - 2 * m r / r) * ‖y r‖ ^ 2 / 2 + q ^ 2 / (2 * r ^ 2)
  have cd : ContinuousOn density (Icc Lzero L) :=
    (((continuousOn_const.sub ((continuousOn_const.mul cm).div continuousOn_id
      (fun r hr => (hpos r hr).ne'))).mul (cy.norm.pow 2)).div_const 2).add
      (continuousOn_const.div (continuousOn_const.mul (continuousOn_id.pow 2))
        (fun r hr => mul_ne_zero (by norm_num) (pow_ne_zero 2 (hpos r hr).ne')))
  have hforms := integralForm_on_of_continuous_tangent cm cd
    (fun r hr => (hradial r (Ioo_subset_Icc_self hr)).2.1)
  have hmAC : AbsolutelyContinuousOnInterval m Lzero L :=
    absolutelyContinuousOnInterval_of_integralForm_on hL
      (fun r hr => hforms Lzero (left_mem_Icc.mpr hL) r hr)
  have hmL : m L = M := by simp only [m, hzinit]
  have hpL : phi L = P / (L : ℂ) := by
    simp only [phi, hzinit]
    push_cast
    ring
  have hyL : y L = -P / (L : ℂ) := by
    dsimp only [y, lam]
    rw [hzinit]
    norm_num
    ring
  have hyid (r : ℝ) : y r = -((P / ((2 * (z r⁻¹).2.1 : ℝ) : ℂ)) * (r⁻¹ : ℝ)) := by
    simp [y, lam, div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm]
  refine ⟨phi, y, m, fun _ => rfl, fun _ => rfl, fun _ => rfl, hmAC, cp, cy, hmL, hpL,
      by rw [hpL, hyL]; ring, ?_, ?_⟩
  · intro r hr
    have hh := hradial r hr
    have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hpos r hr).ne'
    refine ⟨?_, ?_, hh.2.1⟩
    · have hw := static_radial_weighted_scalar_deriv_of_solution
        (inv_pos.mpr (hpos r hr)) (hz _ (hinv r hr)).1
      simp only [inv_inv] at hw
      simpa only [phi, hyid, sub_eq_add_neg] using hw
    · have halg (k : ℝ) : ((-k / r : ℝ) : ℂ) * y r =
          y r / (r : ℂ) + ((-(1 + k) / r : ℝ) : ℂ) * y r := by
        push_cast
        field_simp
        ring
      convert hh.2.2.2.1.add hh.2.2.1 using 1
      exact halg _
  · intro r hr
    have hh := hz _ (hinv r hr)
    have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hpos r hr).ne'
    have hscalar := hh.2.2.2.2.1
    have hsecond := hh.2.2.2.2.2
    have hybound : ‖y r‖ ≤ C / r := by
      rw [hyid, norm_neg]
      exact (le_add_of_nonneg_left (norm_nonneg _)).trans
        (by simpa only [div_eq_mul_inv] using hscalar)
    have hphibound : ‖phi r‖ ≤ C / r :=
      (le_add_of_nonneg_right (norm_nonneg _)).trans
        (by simpa only [phi, div_eq_mul_inv] using hscalar)
    have hsecond' : ‖phi r + y r‖ ≤ C / r ^ 2 := by
      rw [hyid, ← sub_eq_add_neg]
      simpa only [phi, inv_pow, div_eq_mul_inv] using hsecond
    have hgap : 1 / 2 ≤ 1 - 2 * m r / r := by
      simpa only [m, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh.2.2.2.1
    have hr128 : 128 ≤ r := h128.trans hr.1
    have habsgap : |1 - 2 * m r / r| ≤ 2 := by
      rw [abs_of_nonneg ((by norm_num : (0 : ℝ) ≤ 1 / 2).trans hgap)]
      have hmabs : |m r| ≤ 2 := hh.2.2.1
      have hlower : -2 ≤ m r := (abs_le.mp hmabs).1
      have hratio : -1 ≤ 2 * m r / r := (le_div_iff₀ (hpos r hr)).mpr (by linarith)
      linarith only [hratio]
    refine ⟨hh.2.2.1, hybound.trans ?_, habsgap, ?_, hsecond'.trans ?_, hgap⟩
    · exact div_le_div_of_nonneg_right (by linarith) (hpos r hr).le
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos r hr)]
      have h := mul_le_mul_of_nonneg_left hphibound (hpos r hr).le
      rw [mul_div_cancel₀ _ (hpos r hr).ne'] at h
      exact h.trans (by linarith)
    · exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg r)

end EmcsfAcExtension.Global.Observation
