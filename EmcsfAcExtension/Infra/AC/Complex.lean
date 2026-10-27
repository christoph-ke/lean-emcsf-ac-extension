module

public import Mathlib

/-!
# Complex absolutely continuous calculus

Real and imaginary projections transfer the real AC theory to complex functions.
The fundamental theorem uses an almost everywhere derivative, including at the endpoints
only up to a null set. The primitive characterizations use ordered closed intervals.
-/

public section

open Set MeasureTheory Filter

namespace AbsolutelyContinuousOnInterval

/-- The real part of a complex absolutely continuous function is absolutely continuous. -/
theorem re {f : ℝ → ℂ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => (f x).re) a b :=
  Complex.reCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hf

/-- The imaginary part of a complex absolutely continuous function is absolutely continuous. -/
theorem im {f : ℝ → ℂ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => (f x).im) a b :=
  Complex.imCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hf

/-- Real-to-complex coercion preserves absolute continuity. -/
theorem ofReal {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => (f x : ℂ)) a b :=
  Complex.ofRealCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hf

/-- A complex function is AC if its real and imaginary parts are AC. -/
theorem of_re_im {f : ℝ → ℂ} {a b : ℝ}
    (hr : AbsolutelyContinuousOnInterval (fun x => (f x).re) a b)
    (hi : AbsolutelyContinuousOnInterval (fun x => (f x).im) a b) :
    AbsolutelyContinuousOnInterval f a b := by
  have h := hr.ofReal.fun_add (hi.ofReal.const_smul Complex.I)
  simp only [smul_eq_mul, mul_comm Complex.I, Complex.re_add_im] at h
  exact h

/-- AC functions with finite-dimensional real target are differentiable almost everywhere. -/
theorem ae_differentiableAt_of_mem_uIcc {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : ℝ → E} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    ∀ᵐ x, x ∈ uIcc a b → DifferentiableAt ℝ f x :=
  hf.boundedVariationOn.ae_differentiableAt_of_mem_uIcc

end AbsolutelyContinuousOnInterval

namespace IntervalIntegrable

/-- An integrable complex density has an absolutely continuous interval primitive. -/
theorem absolutelyContinuousOnInterval_intervalIntegral_complex {g : ℝ → ℂ} {a b c : ℝ}
    (hg : IntervalIntegrable g volume a b) (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ t in c..x, g t) a b := by
  have hr : IntervalIntegrable (fun x => (g x).re) volume a b := ⟨hg.1.re, hg.2.re⟩
  have hi : IntervalIntegrable (fun x => (g x).im) volume a b := ⟨hg.1.im, hg.2.im⟩
  apply AbsolutelyContinuousOnInterval.of_re_im
  · apply (hr.absolutelyContinuousOnInterval_intervalIntegral hc).congr
    intro x hx
    exact intervalIntegral.intervalIntegral_re (hg.mono_set (uIcc_subset_uIcc hc hx))
  · apply (hi.absolutelyContinuousOnInterval_intervalIntegral hc).congr
    intro x hx
    exact intervalIntegral.intervalIntegral_im (hg.mono_set (uIcc_subset_uIcc hc hx))

end IntervalIntegrable

namespace AbsolutelyContinuousOnInterval

/-- The derivative of a complex AC function is interval integrable. -/
theorem intervalIntegrable_deriv_complex {f : ℝ → ℂ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    IntervalIntegrable (deriv f) volume a b := by
  have hr := hf.re.intervalIntegrable_deriv
  have hi := hf.im.intervalIntegrable_deriv
  have hr' : IntervalIntegrable (fun x => ((deriv (fun y => (f y).re) x : ℝ) : ℂ)) volume a b :=
    ⟨hr.1.ofReal, hr.2.ofReal⟩
  have hi' : IntervalIntegrable (fun x => ((deriv (fun y => (f y).im) x : ℝ) : ℂ)) volume a b :=
    ⟨hi.1.ofReal, hi.2.ofReal⟩
  apply (hr'.add (hi'.mul_const Complex.I)).congr_ae
  apply (ae_restrict_iff' measurableSet_uIoc).mpr
  filter_upwards [hf.re.ae_differentiableAt, hf.im.ae_differentiableAt] with x hx hy hmem
  have hmem' := uIoc_subset_uIcc hmem
  have hd := (hx hmem').hasDerivAt.ofReal_comp.add
    ((hy hmem').hasDerivAt.ofReal_comp.mul_const Complex.I)
  have hd' : HasDerivAt f
      (((deriv (fun y => (f y).re) x : ℝ) : ℂ) +
        ((deriv (fun y => (f y).im) x : ℝ) : ℂ) * Complex.I) x := by
    simpa only [Pi.add_def, Complex.re_add_im] using! hd
  exact hd'.deriv.symm

/-- The complex FTC for any integrable almost everywhere derivative of an AC function. -/
theorem integral_eq_sub_of_ae_hasDerivAt_complex {f g : ℝ → ℂ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : IntervalIntegrable g volume a b)
    (hfg : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f (g x) x) :
    (∫ x in a..b, g x) = f b - f a := by
  have hp := hg.absolutelyContinuousOnInterval_intervalIntegral_complex left_mem_uIcc
  have hz : ∀ᵐ x, x ∈ uIcc a b →
      HasDerivAt (fun y => f y - ∫ t in a..y, g t) 0 x := by
    filter_upwards [hfg, hg.ae_hasDerivAt_integral] with x hx hy hmem
    simpa only [sub_self, Pi.sub_apply] using! (hx hmem).sub (hy hmem a left_mem_uIcc)
  obtain ⟨C, hC⟩ := (hf.sub hp).const_of_ae_hasDerivAt_zero hz
  have ha := hC a left_mem_uIcc
  have hb := hC b right_mem_uIcc
  simp only [Pi.sub_apply, intervalIntegral.integral_same, sub_zero] at ha hb
  rw [← ha] at hb
  calc
    (∫ x in a..b, g x) = f b - (f b - ∫ x in a..b, g x) := by abel
    _ = f b - f a := by rw [hb]

/-- Fundamental theorem of calculus for complex absolutely continuous functions. -/
theorem integral_deriv_eq_sub_complex {f : ℝ → ℂ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    (∫ x in a..b, deriv f x) = f b - f a :=
  hf.integral_eq_sub_of_ae_hasDerivAt_complex hf.intervalIntegrable_deriv_complex
    (hf.ae_differentiableAt_of_mem_uIcc.mono fun _ hx hmem => (hx hmem).hasDerivAt)

/-- A complex AC function is the integral of an integrable density, and conversely. -/
theorem iff_exists_integral_complex {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) :
    AbsolutelyContinuousOnInterval f a b ↔
      ∃ g : ℝ → ℂ, IntervalIntegrable g volume a b ∧
        ∀ x ∈ Icc a b, f x = f a + ∫ t in a..x, g t := by
  constructor
  · intro hf
    refine ⟨deriv f, hf.intervalIntegrable_deriv_complex, ?_⟩
    intro x hx
    have hax := (hf.mono (uIcc_subset_uIcc left_mem_uIcc
      (by simpa only [uIcc_of_le hab] using hx))).integral_deriv_eq_sub_complex
    rw [hax]
    abel
  · rintro ⟨g, hg, hfg⟩
    have hp := hg.absolutelyContinuousOnInterval_intervalIntegral_complex left_mem_uIcc
    have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => f a) a b :=
      (LipschitzWith.const (f a)).lipschitzOnWith.absolutelyContinuousOnInterval
    apply (hconst.fun_add hp).congr
    intro x hx
    exact (hfg x (by simpa only [uIcc_of_le hab] using hx)).symm

/-- A real AC function is the integral of an integrable density, and conversely. -/
theorem iff_exists_integral_real {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) :
    AbsolutelyContinuousOnInterval f a b ↔
      ∃ g : ℝ → ℝ, IntervalIntegrable g volume a b ∧
        ∀ x ∈ Icc a b, f x = f a + ∫ t in a..x, g t := by
  constructor
  · intro hf
    refine ⟨deriv f, hf.intervalIntegrable_deriv, ?_⟩
    intro x hx
    have hax := (hf.mono (uIcc_subset_uIcc left_mem_uIcc
      (by simpa only [uIcc_of_le hab] using hx))).integral_deriv_eq_sub
    rw [hax]
    abel
  · rintro ⟨g, hg, hfg⟩
    have hp := hg.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
    have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => f a) a b :=
      (LipschitzWith.const (f a)).lipschitzOnWith.absolutelyContinuousOnInterval
    apply (hconst.fun_add hp).congr
    intro x hx
    exact (hfg x (by simpa only [uIcc_of_le hab] using hx)).symm

end AbsolutelyContinuousOnInterval
