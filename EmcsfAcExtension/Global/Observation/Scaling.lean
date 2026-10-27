module

public import EmcsfAcExtension.Global.Api.Definitions
public import EmcsfAcExtension.Frozen.IsSolution

/-! # The mass, scalar and charge scale for observation

The scale is chosen in physical variables, before any lower bound for the
normalized outer radius is used. The scalar background is retained.
Source: charged_SF_new_version.tex:L1964–2058; internal project record, normalization sections.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global

/-- [node prop:charged-observation#mass-scalar-charge-normalization]
The zero branch has zero observation left side. Otherwise the enlarged
mass–scalar–charge denominator is positive. There are no constants. -/
theorem Observation.mass_scalar_charge_normalization {b m q : ℝ} (y : ℂ)
    (hb : 0 < b) (hm : 0 ≤ m) :
    (m + b * ‖y‖ = 0 ∧ b * (‖y‖ ^ 2 + (2 * m / b) ^ 2) = 0) ∨
      0 < m + b * ‖y‖ + |q| := by
  by_cases hzero : m + b * ‖y‖ = 0
  · left
    have hm0 : m = 0 := le_antisymm (by linarith [mul_nonneg hb.le (norm_nonneg y)]) hm
    have hy0 : ‖y‖ = 0 := by
      rw [hm0, zero_add] at hzero
      exact (mul_eq_zero.mp hzero).resolve_left hb.ne'
    simp [hm0, hy0]
  · right
    exact add_pos_of_pos_of_nonneg
      (lt_of_le_of_ne (add_nonneg hm (mul_nonneg hb.le (norm_nonneg y))) (Ne.symm hzero))
      (abs_nonneg q)

/-- [def-node eq:co-eta]
The charged observation parameter is unchanged by any positive length scale.
There are no constants and no restriction on the coupling or background. -/
theorem co_eta (e b s : ℝ) (H : ℂ) (hs : 0 < s) :
    |s * e| * (b / s) * (1 + ‖H‖) = |e| * b * (1 + ‖H‖) := by
  rw [abs_mul, abs_of_pos hs]
  field_simp

/-- [node prop:charged-observation#normalized-central-data]
The central normalized parameters lie in the unit parameter family.
Here `H = φ + y` is the central outgoing normalized scalar, and `s` is
the enlarged physical scale. There are no constants. -/
theorem Observation.normalized_central_data {b m q s : ℝ} {φ y H : ℂ}
    (hb : 0 < b) (hs : 0 < s) (hscale : s = m + b * ‖y‖ + |q|)
    (hH : H = φ + y) :
    m / s + ‖(b / s : ℝ) * (φ - H)‖ + |q / s| = 1 := by
  have hbs : 0 ≤ b / s := (div_pos hb hs).le
  have hd : φ - H = -y := by rw [hH]; abel
  rw [hd, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hbs,
    norm_neg, abs_div, abs_of_pos hs]
  rw [div_mul_eq_mul_div, ← add_div, ← add_div, ← hscale, div_self hs.ne']

/-- [internal]
The inverse normalized radius is the physical mass, scalar and charge sum.
This identity precedes the physical charge estimate. -/
theorem Observation.inverse_radius_eq (b m q : ℝ) (y : ℂ) (hb : 0 < b) :
    (b / (m + b * ‖y‖ + |q|))⁻¹ = (2 * m / b) / 2 + ‖y‖ + |q| / b := by
  rw [inv_div]
  field_simp

/-- [internal]
For fixed nonnegative charge coefficient and charged threshold, physical
smallness forces any prescribed normalized radius. The chosen `δ` depends
only on `C`, `η` and `L₀`, before the physical data are quantified. The
physical-charge consumer must discharge the displayed charge estimate. -/
theorem co_normalization_large_of_physical_charge {C η L₀ : ℝ}
    (hC : 0 ≤ C) (hη : 0 ≤ η) (hL₀ : 0 < L₀) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ (b m q : ℝ) (y : ℂ), 0 < b → 0 ≤ m →
        0 < m + b * ‖y‖ + |q| →
        2 * m / b + ‖y‖ ≤ δ →
        |q| / b ≤ C * η * Real.sqrt (2 * m / b) →
        L₀ ≤ b / (m + b * ‖y‖ + |q|) := by
  let f : ℝ → ℝ := fun x => x + C * η * Real.sqrt x
  have hc : ContinuousAt f 0 := by fun_prop
  obtain ⟨d, hd, hbound⟩ := Metric.continuousAt_iff.mp hc (1 / L₀) (by positivity)
  let δ := min 1 (d / 2)
  have hδ : 0 < δ := lt_min zero_lt_one (half_pos hd)
  have hδd : dist δ 0 < d := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ]
    exact (min_le_right _ _).trans_lt (by linarith)
  have hf : f δ < 1 / L₀ := by
    have h := hbound hδd
    have hf0 : f 0 = 0 := by simp [f]
    rw [hf0, Real.dist_eq, sub_zero] at h
    exact (le_abs_self _).trans_lt h
  refine ⟨δ, hδ, min_le_left _ _, ?_⟩
  intro b m q y hb hm hs hsmall hcharge
  have hμ : 0 ≤ 2 * m / b := by positivity
  have hμδ : 2 * m / b ≤ δ := by linarith [norm_nonneg y]
  have hinv : (b / (m + b * ‖y‖ + |q|))⁻¹ ≤ f δ := by
    rw [Observation.inverse_radius_eq b m q y hb]
    have hsqrt := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hμδ) (mul_nonneg hC hη)
    dsimp [f]
    linarith
  have hsmallinv : (b / (m + b * ‖y‖ + |q|))⁻¹ ≤ L₀⁻¹ := by
    simpa only [one_div] using hinv.trans hf.le
  exact (inv_le_inv₀ (div_pos hb hs) hL₀).mp hsmallinv

/-- [internal]
An integral equation pulls back under a nonzero affine dilation, with its
exact signed Jacobian. There is no differentiability premise on the fields. -/
theorem Observation.integralForm_comp_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {a s t : ℝ} (ha : a ≠ 0)
    (h : IntegralForm f g (a * s) (a * t)) :
    IntegralForm (fun x => f (a * x)) (fun x => a • g (a * x)) s t := by
  have hi : IntervalIntegrable (fun x => g (a * x)) volume s t := by
    simpa only [mul_div_cancel_left₀ _ ha] using! h.1.comp_mul_left (c := a)
  refine ⟨by simpa only [Pi.smul_apply] using! hi.smul a, ?_⟩
  rw [intervalIntegral.integral_smul, intervalIntegral.smul_integral_comp_mul_left]
  exact h.2

/-- [internal]
Right multiplication by a fixed scalar preserves integral form, with no
regularity beyond the original integral identity and its integrable density. -/
theorem Observation.integralForm_mul_const
    {K : Type*} [RCLike K]
    {f g : ℝ → K} {s t : ℝ} (h : IntegralForm f g s t) (c : K) :
    IntegralForm (fun x => f x * c) (fun x => g x * c) s t := by
  refine ⟨h.1.mul_const c, ?_⟩
  change f t * c - f s * c = ∫ x in s..t, g x * c
  rw [← sub_mul, h.2]
  exact (intervalIntegral.integral_mul_const c g).symm

private theorem scaled_outSeg_subset {D : Set (ℝ × ℝ)} {a u s t : ℝ} (ha : 0 < a)
    (hseg : outSeg u s t ⊆ {p : ℝ × ℝ | (a * p.1, a * p.2) ∈ D}) :
    outSeg (a * u) (a * s) (a * t) ⊆ D := by
  rintro ⟨x, y⟩ ⟨rfl, hsy, hyt⟩
  have hy : (u, y / a) ∈ outSeg u s t := by
    refine ⟨rfl, ?_, ?_⟩
    · exact (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hsy)
    · exact (div_le_iff₀ ha).mpr (by simpa only [mul_comm] using hyt)
  simpa only [mem_ofPred_eq, mul_div_cancel₀ _ ha.ne'] using hseg hy

/-- [internal]
Positive scaling transports the outgoing integral system from explicit
integral-equation inputs. This compositional helper is consumed both by
the original-solution wrapper and by the gauged observation chart. -/
theorem Observation.rescaled_out_integral_forms_of_integral_forms
    (S : Fields) (a e u s t : ℝ) (ha : 0 < a)
    (hout : IntegralForm (S.r (a * u)) (S.lam (a * u)) (a * s) (a * t) ∧
      IntegralForm (S.nu (a * u)) (S.rUV (a * u)) (a * s) (a * t) ∧
      IntegralForm (S.m (a * u)) (S.mV (a * u)) (a * s) (a * t) ∧
      IntegralForm (S.Q (a * u)) (S.QV e (a * u)) (a * s) (a * t) ∧
      IntegralForm (S.A (a * u)) (S.AV (a * u)) (a * s) (a * t) ∧
      IntegralForm (S.phi (a * u)) (S.phiV (a * u)) (a * s) (a * t) ∧
      IntegralForm (S.xi (a * u)) (S.xiV e (a * u)) (a * s) (a * t)) :
    let P := rescaleFields S a
    IntegralForm (P.r u) (P.lam u) s t ∧
    IntegralForm (P.nu u) (P.rUV u) s t ∧
    IntegralForm (P.m u) (P.mV u) s t ∧
    IntegralForm (P.Q u) (P.QV (a * e) u) s t ∧
    IntegralForm (P.A u) (P.AV u) s t ∧
    IntegralForm (P.phi u) (P.phiV u) s t ∧
    IntegralForm (P.xi u) (P.xiV (a * e) u) s t := by
  rcases hout with ⟨hr, hn, hm, hQ, hA, hφ, hξ⟩
  have k₁ := funext (fun v : ℝ => (rescaleFields_rhs S a e u v ha).1)
  have k₂ := funext (fun v : ℝ => (rescaleFields_rhs S a e u v ha).2.1)
  have k₄ := funext (fun v : ℝ => (rescaleFields_rhs S a e u v ha).2.2.2.1)
  have k₆ := funext (fun v : ℝ => (rescaleFields_rhs S a e u v ha).2.2.2.2.2.1)
  have k₇ := funext (fun v : ℝ => (rescaleFields_rhs S a e u v ha).2.2.2.2.2.2.1)
  have k₉ := funext (fun v : ℝ => (rescaleFields_rhs S a e u v ha).2.2.2.2.2.2.2.2.1)
  dsimp only
  simp_rw [k₁, k₂, k₄, k₆, k₇, k₉]
  have ha0 := ha.ne'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [rescaleFields, smul_eq_mul, div_eq_mul_inv, ha0, mul_assoc,
      mul_comm, mul_left_comm] using!
      Observation.integralForm_mul_const (Observation.integralForm_comp_mul ha0 hr) a⁻¹
  · simpa only [rescaleFields, smul_eq_mul] using! Observation.integralForm_comp_mul ha0 hn
  · simpa [rescaleFields, smul_eq_mul, div_eq_mul_inv, ha0, mul_assoc,
      mul_comm, mul_left_comm] using!
      Observation.integralForm_mul_const (Observation.integralForm_comp_mul ha0 hm) a⁻¹
  · simpa [rescaleFields, smul_eq_mul, div_eq_mul_inv, ha0, mul_assoc,
      mul_comm, mul_left_comm] using!
      Observation.integralForm_mul_const (Observation.integralForm_comp_mul ha0 hQ) a⁻¹
  · simpa only [rescaleFields, smul_eq_mul] using! Observation.integralForm_comp_mul ha0 hA
  · simpa only [rescaleFields, Complex.real_smul] using!
      Observation.integralForm_comp_mul ha0 hφ
  · simpa only [rescaleFields, Complex.real_smul] using!
      Observation.integralForm_comp_mul ha0 hξ

/-- [node prop:charged-observation#rescaled-equations]
All seven outgoing integral equations pull back to the exact inverse-image
domain under positive length scaling, with coupling `a*e`. This proof uses
only the original frozen solution, and applies on every proper subsegment.
No normalized-domain `IsSolution` or diagonal-axis assertion is made. -/
theorem Observation.rescaled_out_integral_forms
    {e a : ℝ} {S : Fields} {D : Set (ℝ × ℝ)} (hS : IsSolution e S D) (ha : 0 < a)
    {u s t : ℝ} (hus : u < s) (hst : s ≤ t)
    (hseg : outSeg u s t ⊆ {p : ℝ × ℝ | (a * p.1, a * p.2) ∈ D}) :
    let P := rescaleFields S a
    IntegralForm (P.r u) (P.lam u) s t ∧
    IntegralForm (P.nu u) (P.rUV u) s t ∧
    IntegralForm (P.m u) (P.mV u) s t ∧
    IntegralForm (P.Q u) (P.QV (a * e) u) s t ∧
    IntegralForm (P.A u) (P.AV u) s t ∧
    IntegralForm (P.phi u) (P.phiV u) s t ∧
    IntegralForm (P.xi u) (P.xiV (a * e) u) s t := by
  obtain ⟨hr, hn, hm, hQ, hA, hφ, hξ⟩ := hS.eq_out (a * u) (a * s) (a * t)
    (mul_lt_mul_of_pos_left hus ha) (mul_le_mul_of_nonneg_left hst ha.le)
    (scaled_outSeg_subset ha hseg)
  exact Observation.rescaled_out_integral_forms_of_integral_forms S a e u s t ha
    ⟨hr, hn, hm, hQ, hA, hφ, hξ⟩

private theorem scaled_inSeg_subset {D : Set (ℝ × ℝ)} {a s t v : ℝ} (ha : 0 < a)
    (hseg : inSeg s t v ⊆ {p : ℝ × ℝ | (a * p.1, a * p.2) ∈ D}) :
    inSeg (a * s) (a * t) (a * v) ⊆ D := by
  rintro ⟨x, y⟩ ⟨hsx, hxt, rfl⟩
  have hx : (x / a, v) ∈ inSeg s t v := by
    refine ⟨?_, ?_, rfl⟩
    · exact (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hsx)
    · exact (div_le_iff₀ ha).mpr (by simpa only [mul_comm] using hxt)
  simpa only [mem_ofPred_eq, mul_div_cancel₀ _ ha.ne'] using hseg hx

/-- [internal]
Positive scaling transports the incoming integral system from explicit
integral-equation inputs. This compositional helper is consumed both by
the original-solution wrapper and by the gauged observation chart. -/
theorem Observation.rescaled_in_integral_forms_of_integral_forms
    (S : Fields) (a e s t v : ℝ) (ha : 0 < a)
    (hin : IntegralForm (fun u => S.r u (a * v)) (fun u => S.nu u (a * v)) (a * s) (a * t) ∧
      IntegralForm (fun u => S.lam u (a * v)) (fun u => S.rUV u (a * v)) (a * s) (a * t) ∧
      IntegralForm (fun u => S.m u (a * v)) (fun u => S.mU u (a * v)) (a * s) (a * t) ∧
      IntegralForm (fun u => S.Q u (a * v)) (fun u => S.QU e u (a * v)) (a * s) (a * t) ∧
      IntegralForm (fun u => S.phi u (a * v)) (fun u => S.phiU e u (a * v)) (a * s) (a * t) ∧
      IntegralForm (fun u => S.theta u (a * v)) (fun u => S.thetaU e u (a * v)) (a * s) (a * t)) :
    let P := rescaleFields S a
    IntegralForm (fun x => P.r x v) (fun x => P.nu x v) s t ∧
    IntegralForm (fun x => P.lam x v) (fun x => P.rUV x v) s t ∧
    IntegralForm (fun x => P.m x v) (fun x => P.mU x v) s t ∧
    IntegralForm (fun x => P.Q x v) (fun x => P.QU (a * e) x v) s t ∧
    IntegralForm (fun x => P.phi x v) (fun x => P.phiU (a * e) x v) s t ∧
    IntegralForm (fun x => P.theta x v) (fun x => P.thetaU (a * e) x v) s t := by
  rcases hin with ⟨hr, hlam, hm, hQ, hφ, hθ⟩
  have k₁ := funext (fun u : ℝ => (rescaleFields_rhs S a e u v ha).1)
  have k₃ := funext (fun u : ℝ => (rescaleFields_rhs S a e u v ha).2.2.1)
  have k₅ := funext (fun u : ℝ => (rescaleFields_rhs S a e u v ha).2.2.2.2.1)
  have k₈ := funext (fun u : ℝ => (rescaleFields_rhs S a e u v ha).2.2.2.2.2.2.2.1)
  have k₁₀ := funext (fun u : ℝ => (rescaleFields_rhs S a e u v ha).2.2.2.2.2.2.2.2.2)
  dsimp only
  rw [k₁, k₃, k₅, k₈, k₁₀]
  have ha0 := ha.ne'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [rescaleFields, smul_eq_mul, div_eq_mul_inv, ha0, mul_assoc,
      mul_comm, mul_left_comm] using!
      Observation.integralForm_mul_const (Observation.integralForm_comp_mul ha0 hr) a⁻¹
  · simpa only [rescaleFields, smul_eq_mul] using! Observation.integralForm_comp_mul ha0 hlam
  · simpa [rescaleFields, smul_eq_mul, div_eq_mul_inv, ha0, mul_assoc,
      mul_comm, mul_left_comm] using!
      Observation.integralForm_mul_const (Observation.integralForm_comp_mul ha0 hm) a⁻¹
  · simpa [rescaleFields, smul_eq_mul, div_eq_mul_inv, ha0, mul_assoc,
      mul_comm, mul_left_comm] using!
      Observation.integralForm_mul_const (Observation.integralForm_comp_mul ha0 hQ) a⁻¹
  · simpa only [rescaleFields, Complex.real_smul] using!
      Observation.integralForm_comp_mul ha0 hφ
  · simpa only [rescaleFields, Complex.real_smul] using!
      Observation.integralForm_comp_mul ha0 hθ

/-- [node prop:charged-observation#rescaled-equations]
All six incoming integral equations pull back on the exact inverse-image
domain with coupling `a*e`. Together with the outgoing theorem this proves
the full reduced integral system on every proper characteristic subsegment,
retaining the original solution rather than assigning an axis to a chart. -/
theorem Observation.rescaled_in_integral_forms
    {e a : ℝ} {S : Fields} {D : Set (ℝ × ℝ)} (hS : IsSolution e S D) (ha : 0 < a)
    {s t v : ℝ} (hst : s ≤ t) (htv : t < v)
    (hseg : inSeg s t v ⊆ {p : ℝ × ℝ | (a * p.1, a * p.2) ∈ D}) :
    let P := rescaleFields S a
    IntegralForm (fun x => P.r x v) (fun x => P.nu x v) s t ∧
    IntegralForm (fun x => P.lam x v) (fun x => P.rUV x v) s t ∧
    IntegralForm (fun x => P.m x v) (fun x => P.mU x v) s t ∧
    IntegralForm (fun x => P.Q x v) (fun x => P.QU (a * e) x v) s t ∧
    IntegralForm (fun x => P.phi x v) (fun x => P.phiU (a * e) x v) s t ∧
    IntegralForm (fun x => P.theta x v) (fun x => P.thetaU (a * e) x v) s t := by
  obtain ⟨hr, hlam, hm, hQ, hφ, hθ⟩ := hS.eq_in (a * s) (a * t) (a * v)
    (mul_le_mul_of_nonneg_left hst ha.le) (mul_lt_mul_of_pos_left htv ha)
    (scaled_inSeg_subset ha hseg)
  exact Observation.rescaled_in_integral_forms_of_integral_forms S a e s t v ha
    ⟨hr, hlam, hm, hQ, hφ, hθ⟩

end EmcsfAcExtension.Global
