module

public import EmcsfAcExtension.Global.Observation.SourceCore
import Mathlib

/-! # Uniform inner charge bounds from the global core estimate

At a fixed inner radius the absolute normalized charge is O(eta), even
when the outer scale is arbitrarily large. The outer Maxwell comparison
at one actual level point then controls the reference charge as well.
Source: charged_SF_new_version.tex:L2114–2140, L2587–2608; approved internal project record (C2).
-/

public section

open Complex

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
The core-charge estimate gives a uniform absolute charge bound on the
fixed inner annulus. The positive coefficient depends only on `Ccore`
and `Lzero`, before all fields, backgrounds, couplings, outer scales
and charged errors. The actual core-estimate consumer supplies `hQ`.
No reference or incoming scalar supremum is involved. -/
theorem inner_charge_constant_of_core_estimate (Ccore Lzero : ℝ)
    (hCcore : 0 ≤ Ccore) (hLzero : 1 ≤ Lzero) :
    ∃ Cq : ℝ, 0 < Cq ∧
    ∀ (r m Q e L eta : ℝ) (H : ℂ),
      0 < r → r ≤ Lzero → m ∈ Set.Icc 0 2 → 1 ≤ L → 0 ≤ eta →
      |e| * L * (1 + ‖H‖) = eta →
      Q ^ 2 ≤ Ccore * e ^ 2 * m * (‖H‖ ^ 2 * r ^ 3 + r ^ 2) →
      |Q| ≤ Cq * eta := by
  let A := 2 * Ccore * (Lzero ^ 3 + Lzero ^ 2)
  have hLp : 0 < Lzero := zero_lt_one.trans_le hLzero
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  refine ⟨A + 1, by positivity, ?_⟩
  intro r m Q e L eta H hr hrL hm hL heta hscale hQ
  have hE : |e| * (1 + ‖H‖) ≤ eta := by
    have hh := mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ |e| * (1 + ‖H‖))
    rw [mul_one] at hh
    exact hh.trans_eq (by rw [← hscale]; ring)
  have hHsq : ‖H‖ ^ 2 + 1 ≤ (1 + ‖H‖) ^ 2 := by nlinarith only [norm_nonneg H]
  have hE2 : e ^ 2 * (‖H‖ ^ 2 + 1) ≤ eta ^ 2 := by
    have hs := (sq_le_sq₀ (by positivity : 0 ≤ |e| * (1 + ‖H‖)) heta).mpr hE
    rw [mul_pow, sq_abs] at hs
    exact (mul_le_mul_of_nonneg_left hHsq (sq_nonneg e)).trans hs
  have hr2 : r ^ 2 ≤ Lzero ^ 2 := pow_le_pow_left₀ hr.le hrL 2
  have hr3 : r ^ 3 ≤ Lzero ^ 3 := pow_le_pow_left₀ hr.le hrL 3
  have hbracket : ‖H‖ ^ 2 * r ^ 3 + r ^ 2 ≤
      (‖H‖ ^ 2 + 1) * (Lzero ^ 3 + Lzero ^ 2) := by
    have hh := add_le_add (mul_le_mul_of_nonneg_left hr3 (sq_nonneg ‖H‖)) hr2
    have h1 : 0 ≤ ‖H‖ ^ 2 * Lzero ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have h2 : 0 ≤ Lzero ^ 3 := pow_nonneg hLp.le 3
    nlinarith only [hh, h1, h2]
  have hq2 : Q ^ 2 ≤ A * eta ^ 2 := by
    calc
      Q ^ 2 ≤ Ccore * e ^ 2 * m * (‖H‖ ^ 2 * r ^ 3 + r ^ 2) := hQ
      _ ≤ Ccore * e ^ 2 * 2 * (‖H‖ ^ 2 * r ^ 3 + r ^ 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hm.2 (mul_nonneg hCcore (sq_nonneg e))) (by positivity)
      _ ≤ Ccore * e ^ 2 * 2 * ((‖H‖ ^ 2 + 1) * (Lzero ^ 3 + Lzero ^ 2)) :=
        mul_le_mul_of_nonneg_left hbracket (by positivity)
      _ = A * (e ^ 2 * (‖H‖ ^ 2 + 1)) := by dsimp only [A]; ring
      _ ≤ A * eta ^ 2 := mul_le_mul_of_nonneg_left hE2 hA
  have hcoef : A ≤ (A + 1) ^ 2 := by nlinarith only [hA, sq_nonneg A]
  apply (sq_le_sq₀ (abs_nonneg Q) (mul_nonneg (by positivity : 0 ≤ A + 1) heta)).mp
  rw [sq_abs, mul_pow]
  exact hq2.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg eta))

/-- [internal]
One actual outer level point converts the absolute inner charge bound
into a charge-difference bound relative to the same static member.
The exact coefficient depends only on the two prior uniform coefficients
`Cq,B`; all fields, reference charges and charged errors come afterward.
The outer-comparison consumer must supply the displayed level-point error. -/
theorem inner_charge_difference_of_level_point
    {Cq B eta Q Qlevel qStar : ℝ}
    (hQ : |Q| ≤ Cq * eta) (hlevel : |Qlevel| ≤ Cq * eta)
    (houter : |Qlevel - qStar| ≤ B * eta) :
    |Q - qStar| ≤ (2 * Cq + B) * eta := by
  have hq : |qStar| ≤ Cq * eta + B * eta := by
    calc
      |qStar| = |Qlevel - (Qlevel - qStar)| := by congr 1; ring
      _ ≤ |Qlevel| + |Qlevel - qStar| := abs_sub _ _
      _ ≤ Cq * eta + B * eta := add_le_add hlevel houter
  exact (abs_sub _ _).trans ((add_le_add hQ hq).trans_eq (by ring))

end EmcsfAcExtension.Global.Observation
