module

public import EmcsfAcExtension.Global.Observation.Static.UniformBarrier
import Mathlib

/-! # Static barriers after the outer comparison cutoff

The compact family is rebased at an inverse radius small enough for the
already selected outer comparison. Its separate stopped references and
strict margins remain uniform over the entire normalized parameter set.
Source: charged_SF_new_version.tex:L2196–2239; approved internal project record, quantifier closure.
-/

public section

open Set

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
Select uniform stopped static references after any fixed outer cutoff.
All witnesses depend only on `δ,Lmin`, before the normalized member.
The common width retains a proper interval around every outer initial
inverse radius; each inner reference stops at its own selected barrier.
This supplies the cutoff order required by the outer comparison and
does not extend one member below its own stopping radius. -/
theorem uniform_static_barriers_after_cutoff (δ Lmin : ℝ) (hδ : δ ∈ Ioo 0 1) :
    ∃ a width r γ C : ℝ,
      0 < a ∧ 0 < width ∧ a ≤ width ∧ a ≤ 1 / 128 ∧ Lmin ≤ a⁻¹ ∧
      0 < r ∧ 0 < γ ∧ 0 < C ∧
      let parameters := {p : ℝ × ℂ × ℝ × ℝ | 0 ≤ p.1 ∧
        p.1 + ‖p.2.1‖ + |p.2.2.1| = 1 ∧ p.2.2.2 ∈ Icc 0 a}
      ∃ outer : (ℝ × ℂ × ℝ × ℝ) → ℝ → ℝ × ℝ × ℂ,
        (∀ p ∈ parameters,
          outer p p.2.2.2 = (p.1, 1 / 2, p.2.1 * p.2.2.2) ∧
          IsIntegralCurveOn (outer p) (staticInvRadiusRHS p.2.1 p.2.2.1)
            (Icc (p.2.2.2 - 2 * width) (p.2.2.2 + 2 * width)) ∧
          ∀ x ∈ Icc (p.2.2.2 - 2 * width) (p.2.2.2 + 2 * width),
            |x| ≤ 1 / 32 ∧ |(outer p x).1| ≤ 2 ∧
              (outer p x).2.1 ∈ Icc (1 / 4) 1 ∧ ‖(outer p x).2.2‖ ≤ 1) ∧
        ∀ p ∈ parameters, ∃ ρ ∈ Icc r a⁻¹, ∃ z : ℝ → ℝ × ℝ × ℂ,
          z a = outer p a ∧
          IsIntegralCurveOn z (staticInvRadiusRHS p.2.1 p.2.2.1) (Icc a ρ⁻¹) ∧
          (∀ x ∈ Icc a ρ⁻¹, 0 < (z x).2.1 ∧ 0 < 1 - 2 * x * (z x).1 ∧
            ‖(x, z x)‖ + |(z x).2.1⁻¹| + |(1 - 2 * x * (z x).1)⁻¹| +
              ‖(p.2.1 / ((2 * (z x).2.1 : ℝ) : ℂ)) * x‖ +
              |(2 * x * (z x).1 - p.2.2.1 ^ 2 * x ^ 2) / (1 - 2 * x * (z x).1)| ≤ C) ∧
          ((z ρ⁻¹).1 ≤ -γ ∨ 1 - 2 * ρ⁻¹ * (z ρ⁻¹).1 ≤ δ - γ) := by
  obtain ⟨width, hw, hw128, hfamily⟩ := compact_static_family
  let a := min width (max Lmin 1)⁻¹
  have hmax : 0 < max Lmin 1 := zero_lt_one.trans_le (le_max_right _ _)
  have ha : 0 < a := lt_min hw (inv_pos.mpr hmax)
  have haw : a ≤ width := min_le_left _ _
  have hcut : Lmin ≤ a⁻¹ := by
    have hh := one_div_le_one_div_of_le ha (min_le_right width (max Lmin 1)⁻¹)
    simp only [one_div, inv_inv] at hh
    exact (le_max_left _ _).trans hh
  obtain ⟨outer, hout, hcontinuous, _⟩ := hfamily a ⟨ha, haw⟩
  let parameters := {p : ℝ × ℂ × ℝ × ℝ | 0 ≤ p.1 ∧
    p.1 + ‖p.2.1‖ + |p.2.2.1| = 1 ∧ p.2.2.2 ∈ Icc 0 a}
  have hsub (p) (hp : p ∈ parameters) : Icc p.2.2.2 a ⊆
      Icc (p.2.2.2 - 2 * width) (p.2.2.2 + 2 * width) :=
    Icc_subset_Icc (by linarith only [hw])
      (by linarith only [hp.2.2.1, haw, hw])
  have hcurves (p) (hp : p ∈ parameters) :
      outer p p.2.2.2 = (p.1, 1 / 2, p.2.1 * p.2.2.2) ∧
      IsIntegralCurveOn (outer p) (staticInvRadiusRHS p.2.1 p.2.2.1) (Icc p.2.2.2 a) :=
    ⟨(hout p hp).1, (hout p hp).2.1.mono (hsub p hp)⟩
  have hpositive (p) (hp : p ∈ parameters) :
      0 < (outer p a).2.1 ∧ 0 < 1 - 2 * a * (outer p a).1 := by
    have hh := (hout p hp).2.2 a (hsub p hp (right_mem_Icc.mpr hp.2.2.2))
    have hprod : |2 * a * (outer p a).1| ≤ 1 / 8 := by
      calc
        |2 * a * (outer p a).1| = 2 * |a| * |(outer p a).1| := by
          rw [abs_mul, abs_mul]; norm_num
        _ ≤ 2 * (1 / 32) * 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hh.1 (by norm_num)) hh.2.1
            (abs_nonneg _) (by norm_num)
        _ = 1 / 8 := by norm_num
    exact ⟨lt_of_lt_of_le (by norm_num) hh.2.2.1.1,
      by linarith only [le_abs_self (2 * a * (outer p a).1), hprod]⟩
  obtain ⟨r, hr, γ, hγ, C, hC, hbar⟩ :=
    uniform_static_barriers_of_outer_family δ a hδ ha outer hcurves hcontinuous hpositive
  exact ⟨a, width, r, γ, C, ha, hw, haw, haw.trans hw128, hcut, hr, hγ, hC,
    outer, hout, hbar⟩

end EmcsfAcExtension.Global.Observation
