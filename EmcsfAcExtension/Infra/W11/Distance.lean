module

public import EmcsfAcExtension.Infra.AC.Variation
public import EmcsfAcExtension.Infra.BV.Basic
public import EmcsfAcExtension.Frozen.DatumVar

/-!
# The representative interval W¹¹ distance

The representative norm is the norm of the left endpoint value plus total variation.
Its use as a real norm or distance requires finite variation; all estimates below
state that requirement. On AC curves, internal project record identifies variation with the integral
of the derivative norm. This is the distance used at `charged_SF_new_version.tex:L6350–L6371`.
All constants in this file are literal and independent of the interval and curves.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.W11

/-- The representative W¹¹ norm on `[a,b]`, for curves of finite variation. -/
@[expose] noncomputable def intervalNorm (a b : ℝ) (f : ℝ → ℂ) : ℝ :=
  ‖f a‖ + (eVariationOn f (Icc a b)).toReal

/-- Unfold the representative interval norm. -/
theorem intervalNorm_def (a b : ℝ) (f : ℝ → ℂ) :
    intervalNorm a b f = ‖f a‖ + (eVariationOn f (Icc a b)).toReal := rfl

/-- The representative W¹¹ distance, for curves of finite variation. -/
@[expose] noncomputable def intervalDist (a b : ℝ) (f g : ℝ → ℂ) : ℝ :=
  intervalNorm a b (f - g)

/-- Unfold the representative interval distance. -/
theorem intervalDist_def (a b : ℝ) (f g : ℝ → ℂ) :
    intervalDist a b f g = ‖f a - g a‖ +
      (eVariationOn (fun x => f x - g x) (Icc a b)).toReal := rfl

/-- At vertex zero the distance uses exactly the frozen datum variation. -/
theorem intervalDist_zero (b : ℝ) (f g : ℝ → ℂ) :
    intervalDist 0 b f g = ‖f 0 - g 0‖ + datumVar (f - g) b := rfl

/-- Finite real variation is subadditive, with coefficient one uniformly in the curves. -/
theorem variation_add_le {a b : ℝ} {f g : ℝ → ℂ}
    (hf : BoundedVariationOn f (Icc a b)) (hg : BoundedVariationOn g (Icc a b)) :
    (eVariationOn (f + g) (Icc a b)).toReal ≤
      (eVariationOn f (Icc a b)).toReal + (eVariationOn g (Icc a b)).toReal := by
  simpa only [ENNReal.toReal_add hf hg] using!
    ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hf, hg⟩) (eVariationOn.add_le f g (Icc a b))

/-- Interchanging two curves does not change the variation of their difference. -/
theorem variation_sub_comm (a b : ℝ) (f g : ℝ → ℂ) :
    eVariationOn (f - g) (Icc a b) = eVariationOn (g - f) (Icc a b) := by
  have heq : f - g = fun x => -(g x - f x) := by ext x; simp
  rw [heq, eVariationOn.neg]
  rfl

/-- The representative interval norm satisfies the triangle inequality on BV curves. -/
theorem intervalNorm_add_le {a b : ℝ} {f g : ℝ → ℂ}
    (hf : BoundedVariationOn f (Icc a b)) (hg : BoundedVariationOn g (Icc a b)) :
    intervalNorm a b (f + g) ≤ intervalNorm a b f + intervalNorm a b g := by
  have hv := variation_add_le hf hg
  have hn := norm_add_le (f a) (g a)
  simp only [intervalNorm_def, Pi.add_apply] at *
  linarith

/-- The interval distance from a curve to itself vanishes. -/
@[simp] theorem intervalDist_self (a b : ℝ) (f : ℝ → ℂ) : intervalDist a b f f = 0 := by
  simp only [intervalDist_def, sub_self, norm_zero, zero_add]
  rw [(eVariationOn.eq_zero_iff _).2 (by intros; exact edist_self _), ENNReal.toReal_zero]

/-- The interval distance is symmetric. -/
theorem intervalDist_comm (a b : ℝ) (f g : ℝ → ℂ) :
    intervalDist a b f g = intervalDist a b g f := by
  simp only [intervalDist_def, norm_sub_rev (f a) (g a)]
  congr 1
  exact congrArg ENNReal.toReal (variation_sub_comm a b f g)

/-- The interval distance satisfies the triangle inequality on BV curves. -/
theorem intervalDist_triangle {a b : ℝ} {f g h : ℝ → ℂ}
    (hf : BoundedVariationOn f (Icc a b)) (hg : BoundedVariationOn g (Icc a b))
    (hh : BoundedVariationOn h (Icc a b)) :
    intervalDist a b f h ≤ intervalDist a b f g + intervalDist a b g h := by
  change intervalNorm a b (f - h) ≤ intervalNorm a b (f - g) + intervalNorm a b (g - h)
  have hhf : BoundedVariationOn (f - g) (Icc a b) := hf.sub hg
  have hhg : BoundedVariationOn (g - h) (Icc a b) := hg.sub hh
  simpa only [sub_add_sub_cancel] using intervalNorm_add_le hhf hhg

/-- The norm controls every value on the interval, uniformly with coefficient one. -/
theorem norm_le_intervalNorm {a b x : ℝ} {f : ℝ → ℂ}
    (hf : BoundedVariationOn f (Icc a b)) (hx : x ∈ Icc a b) :
    ‖f x‖ ≤ intervalNorm a b f := by
  have hv := hf.dist_le hx (left_mem_Icc.mpr (hx.1.trans hx.2))
  rw [dist_eq_norm] at hv
  calc
    ‖f x‖ ≤ ‖f x - f a‖ + ‖f a‖ := by simpa using norm_add_le (f x - f a) (f a)
    _ ≤ intervalNorm a b f := by rw [intervalNorm_def]; linarith

/-- The interval distance bounds the pointwise distance, uniformly with coefficient one. -/
theorem norm_sub_le_intervalDist {a b x : ℝ} {f g : ℝ → ℂ}
    (hf : BoundedVariationOn f (Icc a b)) (hg : BoundedVariationOn g (Icc a b))
    (hx : x ∈ Icc a b) : ‖f x - g x‖ ≤ intervalDist a b f g :=
  norm_le_intervalNorm (hf.sub hg) hx

/-- Variation is Lipschitz in the variation of the difference, uniformly with coefficient one. -/
theorem abs_variation_sub_le {a b : ℝ} {f g : ℝ → ℂ}
    (hf : BoundedVariationOn f (Icc a b)) (hg : BoundedVariationOn g (Icc a b)) :
    |(eVariationOn f (Icc a b)).toReal - (eVariationOn g (Icc a b)).toReal| ≤
      (eVariationOn (f - g) (Icc a b)).toReal := by
  have hfg : BoundedVariationOn (f - g) (Icc a b) := hf.sub hg
  have hgf : BoundedVariationOn (g - f) (Icc a b) := hg.sub hf
  have h₁ := variation_add_le hfg hg
  have h₂ := variation_add_le hgf hf
  simp only [sub_add_cancel] at h₁ h₂
  rw [variation_sub_comm a b g f] at h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Perturbing both inputs changes the datum distance by at most the sum of the errors.
The coefficient one is uniform in the interval and all four BV curves. -/
theorem abs_intervalDist_sub_le {a b : ℝ} {f g f' g' : ℝ → ℂ}
    (hf : BoundedVariationOn f (Icc a b)) (hg : BoundedVariationOn g (Icc a b))
    (hf' : BoundedVariationOn f' (Icc a b)) (hg' : BoundedVariationOn g' (Icc a b)) :
    |intervalDist a b f' g' - intervalDist a b f g| ≤
      intervalDist a b f' f + intervalDist a b g' g := by
  have h₁ := intervalDist_triangle hf' hf hg'
  have h₂ := intervalDist_triangle hf hg hg'
  have h₃ := intervalDist_triangle hf hf' hg
  have h₄ := intervalDist_triangle hf' hg' hg
  rw [intervalDist_comm a b g g'] at h₂
  rw [intervalDist_comm a b f f'] at h₃
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end EmcsfAcExtension.W11
