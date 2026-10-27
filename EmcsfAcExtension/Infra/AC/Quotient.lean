module

public import Mathlib
public import EmcsfAcExtension.Infra.BV.Basic

/-!
# Products, reciprocals, logarithms, exponentials and unit phases

Reciprocals have Lipschitz constant `c⁻²` when the norm is at least `c > 0`.
The logarithm has constant `c⁻¹` on `[c, ∞)`, and the real exponential has constant
`exp M` on `(-∞, M]`. These constants are uniform in the interval and the functions.
-/

public section

open Set
open scoped ENNReal

namespace LipschitzOnWith

/-- Inversion is Lipschitz on values whose norm is bounded below by a positive constant. -/
theorem inv_on_norm_ge {K : Type*} [NormedDivisionRing K] {c : ℝ} (hc : 0 < c) :
    LipschitzOnWith ⟨c⁻¹ * c⁻¹, by positivity⟩ (fun z : K => z⁻¹) {z | c ≤ ‖z‖} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro z hz w hw
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hc.trans_le hz)
  have hw0 : w ≠ 0 := norm_pos_iff.mp (hc.trans_le hw)
  rw [dist_inv_inv₀ hz0 hw0]
  change dist z w / (‖z‖ * ‖w‖) ≤ (c⁻¹ * c⁻¹) * dist z w
  calc
    _ ≤ dist z w / (c * c) := div_le_div_of_nonneg_left dist_nonneg (mul_pos hc hc)
      (mul_le_mul hz hw hc.le (norm_nonneg _))
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

/-- The real logarithm is Lipschitz above a positive lower bound. -/
theorem log_on_Ici {c : ℝ} (hc : 0 < c) :
    LipschitzOnWith ⟨c⁻¹, by positivity⟩ Real.log (Ici c) := by
  apply (convex_Ici c).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun x hx => (Real.hasDerivAt_log (ne_of_gt (hc.trans_le hx))).hasDerivWithinAt)
  intro x hx
  change ‖x⁻¹‖ ≤ c⁻¹
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hc.trans_le hx))]
  exact inv_anti₀ hc hx

/-- The real exponential is Lipschitz below any fixed upper bound. -/
theorem exp_on_Iic (M : ℝ) :
    LipschitzOnWith ⟨Real.exp M, (Real.exp_pos M).le⟩ Real.exp (Iic M) := by
  apply (convex_Iic M).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
  intro x hx
  change ‖Real.exp x‖ ≤ Real.exp M
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]
  exact Real.exp_le_exp.mpr hx

end LipschitzOnWith

namespace LipschitzWith

/-- The unit complex phase is globally Lipschitz with constant one. -/
theorem unit_phase : LipschitzWith 1 (fun x : ℝ => Complex.exp (Complex.I * (x : ℂ))) := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro x
    exact ((hasDerivAt_id x).ofReal_comp.const_mul Complex.I).cexp.differentiableAt
  · intro x
    have hd : HasDerivAt (fun y : ℝ => Complex.exp (Complex.I * (y : ℂ)))
        (Complex.exp (Complex.I * (x : ℂ)) * Complex.I) x := by
      simpa only [id_eq, Complex.ofReal_one, mul_one] using!
        ((hasDerivAt_id x).ofReal_comp.const_mul Complex.I).cexp
    rw [hd.deriv]
    simp only [nnnorm_mul, Complex.nnnorm_I, mul_one]
    exact_mod_cast (Complex.norm_exp_I_mul_ofReal x).le

end LipschitzWith

namespace AbsolutelyContinuousOnInterval

/-- Pointwise multiplication preserves AC in a normed ring with multiplicative norm. -/
theorem mul_normed_ring {K : Type*} [NormedRing K] [NormMulClass K]
    {f g : ℝ → K} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (fun x => f x * g x) a b := by
  simpa only [Pi.smul_apply, smul_eq_mul, Pi.mul_def] using! hf.smul hg

/-- A positive norm lower bound makes the reciprocal of an AC function AC. -/
theorem inv_of_le_norm {K : Type*} [NormedDivisionRing K] {g : ℝ → K} {a b c : ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b) (hc : 0 < c)
    (hlo : ∀ x ∈ uIcc a b, c ≤ ‖g x‖) :
    AbsolutelyContinuousOnInterval (fun x => (g x)⁻¹) a b :=
  (LipschitzOnWith.inv_on_norm_ge hc).comp_absolutelyContinuousOnInterval hlo hg

/-- A quotient of AC functions is AC when its denominator is bounded away from zero. -/
theorem div_of_le_norm {K : Type*} [NormedDivisionRing K] {f g : ℝ → K} {a b c : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b)
    (hc : 0 < c) (hlo : ∀ x ∈ uIcc a b, c ≤ ‖g x‖) :
    AbsolutelyContinuousOnInterval (fun x => f x / g x) a b := by
  simpa only [div_eq_mul_inv] using hf.mul_normed_ring (hg.inv_of_le_norm hc hlo)

/-- The logarithm of a real AC function with a positive lower bound is AC. -/
theorem log_of_pos_le {g : ℝ → ℝ} {a b c : ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b) (hc : 0 < c)
    (hlo : ∀ x ∈ uIcc a b, c ≤ g x) :
    AbsolutelyContinuousOnInterval (fun x => Real.log (g x)) a b :=
  (LipschitzOnWith.log_on_Ici hc).comp_absolutelyContinuousOnInterval hlo hg

/-- The real exponential of an AC function on a compact interval is AC. -/
theorem exp {g : ℝ → ℝ} {a b : ℝ} (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (fun x => Real.exp (g x)) a b := by
  obtain ⟨M, hM⟩ := hg.exists_bound
  exact (LipschitzOnWith.exp_on_Iic M).comp_absolutelyContinuousOnInterval
    (fun x hx => (le_abs_self (g x)).trans (hM x hx)) hg

/-- The unit complex phase of a real AC angle is AC. -/
theorem unit_phase {θ : ℝ → ℝ} {a b : ℝ} (hθ : AbsolutelyContinuousOnInterval θ a b) :
    AbsolutelyContinuousOnInterval (fun x => Complex.exp (Complex.I * (θ x : ℂ))) a b :=
  LipschitzWith.unit_phase.comp_absolutelyContinuousOnInterval hθ

end AbsolutelyContinuousOnInterval

namespace eVariationOn

variable {α : Type*} [LinearOrder α] {s : Set α}

/-- The product variation bound in a normed real algebra has explicit uniform norm bounds. -/
theorem mul_le {K : Type*} [NormedRing K] [NormMulClass K] [NormedAlgebra ℝ K] {f g : α → K}
    {C D : ℝ≥0∞} (hf : ∀ x ∈ s, ‖f x‖ₑ ≤ C) (hg : ∀ x ∈ s, ‖g x‖ₑ ≤ D) :
    eVariationOn (fun x => f x * g x) s ≤ C * eVariationOn g s + D * eVariationOn f s := by
  simpa only [Pi.smul_apply, smul_eq_mul] using! eVariationOn_smul_le hf hg

/-- Forming a unit complex phase does not increase variation. -/
theorem unit_phase_le (θ : α → ℝ) (s : Set α) :
    eVariationOn (fun x => Complex.exp (Complex.I * (θ x : ℂ))) s ≤ eVariationOn θ s := by
  simpa only [ENNReal.coe_one, one_mul, Function.comp_def] using!
    LipschitzWith.unit_phase.lipschitzOnWith.comp_eVariationOn_le (mapsTo_univ θ s)

end eVariationOn

namespace BoundedVariationOn

variable {α : Type*} [LinearOrder α] {s : Set α}

/-- Pointwise products preserve bounded variation in normed real algebras. -/
theorem mul_normed_algebra {K : Type*} [NormedRing K] [NormMulClass K] [NormedAlgebra ℝ K]
    {f g : α → K}
    (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (fun x => f x * g x) s := by
  simpa only [Pi.smul_apply, smul_eq_mul] using! hf.smul hg

/-- A positive norm lower bound makes the reciprocal of a BV function BV. -/
theorem inv_of_le_norm {K : Type*} [NormedDivisionRing K] {g : α → K} {c : ℝ}
    (hg : BoundedVariationOn g s) (hc : 0 < c) (hlo : ∀ x ∈ s, c ≤ ‖g x‖) :
    BoundedVariationOn (fun x => (g x)⁻¹) s :=
  (LipschitzOnWith.inv_on_norm_ge hc).comp_boundedVariationOn hlo hg

/-- A quotient of BV functions is BV when the denominator is bounded away from zero. -/
theorem div_of_le_norm {K : Type*} [NormedDivisionRing K] [NormedAlgebra ℝ K] {f g : α → K}
    {c : ℝ} (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s)
    (hc : 0 < c) (hlo : ∀ x ∈ s, c ≤ ‖g x‖) :
    BoundedVariationOn (fun x => f x / g x) s := by
  simpa only [div_eq_mul_inv] using hf.mul_normed_algebra (hg.inv_of_le_norm hc hlo)

/-- The logarithm of a real BV function with a positive lower bound is BV. -/
theorem log_of_pos_le {g : α → ℝ} {c : ℝ} (hg : BoundedVariationOn g s)
    (hc : 0 < c) (hlo : ∀ x ∈ s, c ≤ g x) :
    BoundedVariationOn (fun x => Real.log (g x)) s :=
  (LipschitzOnWith.log_on_Ici hc).comp_boundedVariationOn hlo hg

/-- A function of bounded variation into a normed group has a bounded norm on its set. -/
theorem exists_bound_norm {E : Type*} [NormedAddCommGroup E] {f : α → E}
    (hf : BoundedVariationOn f s) : ∃ M, ∀ x ∈ s, ‖f x‖ ≤ M := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨0, fun _ hx => False.elim hx⟩
  refine ⟨‖f x₀‖ + (eVariationOn f s).toReal, fun x hx => ?_⟩
  have hd : ‖f x - f x₀‖ ≤ (eVariationOn f s).toReal := by
    simpa only [dist_eq_norm] using hf.dist_le hx hx₀
  exact (norm_le_norm_add_norm_sub' (f x) (f x₀)).trans (add_le_add le_rfl hd)

/-- The real exponential of a real BV function is BV. -/
theorem exp {g : α → ℝ} (hg : BoundedVariationOn g s) :
    BoundedVariationOn (fun x => Real.exp (g x)) s := by
  obtain ⟨M, hM⟩ := hg.exists_bound_norm
  exact (LipschitzOnWith.exp_on_Iic M).comp_boundedVariationOn
    (fun x hx => (le_abs_self (g x)).trans (hM x hx)) hg

/-- The unit complex phase of a real BV angle is BV. -/
theorem unit_phase {θ : α → ℝ} (hθ : BoundedVariationOn θ s) :
    BoundedVariationOn (fun x => Complex.exp (Complex.I * (θ x : ℂ))) s :=
  LipschitzWith.unit_phase.comp_boundedVariationOn hθ

end BoundedVariationOn
