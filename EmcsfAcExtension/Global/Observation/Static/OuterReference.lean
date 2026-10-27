module

public import EmcsfAcExtension.Global.Observation.Static.Outer
import EmcsfAcExtension.Global.Observation.BoundaryData
import EmcsfAcExtension.Infra.Null.IntegralForm
import Mathlib

/-! # Radial reference fields for the outer comparison record

The inverse-radius ODE is converted to the three literal radial
reference functions consumed by the comparison interface.
Source: charged_SF_new_version.tex:L2168–2225; approved internal project record, static outer
bounds.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
Construct the radial outer reference with every reference field of the
outer normalization interface discharged. The lower cutoff and scalar
coefficient are universal and precede all radii and normalized parameters.
The reference has the exact central mass and scalar data, all three
radial equations and uniform outer bounds; no reference equation or
estimate is an input. -/
theorem outer_radial_reference :
    ∃ Lmin Kstatic : ℝ, 0 < Lmin ∧ 0 < Kstatic ∧
    ∀ Lzero L M q : ℝ, ∀ P : ℂ,
    Lmin ≤ Lzero → Lzero ≤ L → 0 ≤ M → M + ‖P‖ + |q| = 1 →
    ∃ (phiStar yStar : ℝ → ℂ) (mStar : ℝ → ℝ),
      AbsolutelyContinuousOnInterval mStar Lzero L ∧
      ContinuousOn phiStar (Icc Lzero L) ∧ ContinuousOn yStar (Icc Lzero L) ∧
      mStar L = M ∧ phiStar L = P / (L : ℂ) ∧ phiStar L + yStar L = 0 ∧
      (∀ s ∈ Icc Lzero L,
        let k := (2 * mStar s / s - q ^ 2 / s ^ 2) / (1 - 2 * mStar s / s)
        HasDerivAt (fun r : ℝ => (r : ℂ) * phiStar r) (phiStar s + yStar s) s ∧
        HasDerivAt (fun r => phiStar r + yStar r) ((-k / s : ℝ) * yStar s) s ∧
        HasDerivAt mStar ((1 - 2 * mStar s / s) * ‖yStar s‖ ^ 2 / 2 + q ^ 2 / (2 * s ^ 2)) s) ∧
      ∀ s ∈ Icc Lzero L,
        |mStar s| ≤ 2 ∧ ‖yStar s‖ ≤ Kstatic / s ∧ |1 - 2 * mStar s / s| ≤ 2 ∧
        ‖(s : ℂ) * phiStar s‖ ≤ Kstatic ∧ ‖phiStar s + yStar s‖ ≤ Kstatic / s ^ 2 ∧
        1 / 2 ≤ 1 - 2 * mStar s / s := by
  obtain ⟨a, ha, C, hC, ha128, houter⟩ := co_static_outer
  let Lmin := a⁻¹
  let Kstatic := C + 1
  refine ⟨Lmin, Kstatic, inv_pos.mpr ha, by dsimp only [Kstatic]; positivity, ?_⟩
  intro Lzero L M q P hLzero hL hM hnorm
  have hLzeroPos : 0 < Lzero := (inv_pos.mpr ha).trans_le hLzero
  have hLpos : 0 < L := hLzeroPos.trans_le hL
  have hcut : Lzero⁻¹ ≤ a := by
    simpa only [Lmin, one_div, inv_inv] using one_div_le_one_div_of_le (inv_pos.mpr ha) hLzero
  have hxL : L⁻¹ ≤ Lzero⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hLzeroPos hL
  obtain ⟨z, hzinit, hz⟩ := houter Lzero⁻¹ ⟨inv_pos.mpr hLzeroPos, hcut⟩
    P q M L⁻¹ hM hnorm ⟨(inv_pos.mpr hLpos).le, hxL⟩
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
  refine ⟨phi, y, m, hmAC, cp, cy, hmL, hpL, by rw [hpL, hyL]; ring, ?_, ?_⟩
  · intro r hr
    have hh := hradial r hr
    have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hpos r hr).ne'
    refine ⟨?_, ?_, hh.2.1⟩
    · have hw := ((hz _ (hinv r hr)).2.2.2.2.2.2 (inv_pos.mpr (hpos r hr))).1
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
    have hsecond := hh.2.2.2.2.2.1
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
    have hr128 : 128 ≤ r := by
      have haInv := one_div_le_one_div_of_le ha ha128
      norm_num at haInv
      exact haInv.trans (hLzero.trans hr.1)
    have habsgap : |1 - 2 * m r / r| ≤ 2 := by
      rw [abs_of_nonneg ((by norm_num : (0 : ℝ) ≤ 1 / 2).trans hgap)]
      have hmabs : |m r| ≤ 2 := hh.2.2.1
      have hlower : -2 ≤ m r := (abs_le.mp hmabs).1
      have hratio : -1 ≤ 2 * m r / r := (le_div_iff₀ (hpos r hr)).mpr (by linarith)
      linarith only [hratio]
    refine ⟨hh.2.2.1, hybound.trans ?_, habsgap, ?_, hsecond'.trans ?_, hgap⟩
    · exact div_le_div_of_nonneg_right (by dsimp only [Kstatic]; linarith) (hpos r hr).le
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos r hr)]
      have h := mul_le_mul_of_nonneg_left hphibound (hpos r hr).le
      rw [mul_div_cancel₀ _ (hpos r hr).ne'] at h
      exact h.trans (by dsimp only [Kstatic]; linarith)
    · exact div_le_div_of_nonneg_right (by dsimp only [Kstatic]; linarith) (sq_nonneg r)

end EmcsfAcExtension.Global.Observation
