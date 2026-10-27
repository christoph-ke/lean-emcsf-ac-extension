module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Smooth convolution in L¹

Normalized nonnegative kernels contract the L¹ norm. Shrinking smooth bump
kernels approximate an integrable complex function in L¹. The proof combines
Mathlib's almost everywhere mollifier convergence with dominated convergence
for the norm defect. All estimates have coefficient one, independently of the
function and the kernel. This supplies the convolution step of internal project record's
smallness-preserving smooth-data construction (`charged_SF_new_version.tex:L6350–L6371`).

In the pinned Mathlib, `∞ : ℕ∞ω` denotes C∞, whereas `⊤` denotes analytic
regularity. The convolution API takes its order in `ℕ∞` and coerces it to `ℕ∞ω`.
-/

public section

open Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology Convolution ContDiff

namespace EmcsfAcExtension.W11

/-- A nonnegative mass-one kernel contracts the global L¹ norm. The coefficient
one is uniform in both functions. The product integrability and integral swap
are Mathlib's Tonelli/Fubini convolution lemmas. -/
theorem integral_norm_convolution_le {ρ : ℝ → ℝ} {f : ℝ → ℂ}
    (hρ : Integrable ρ) (hρ₀ : ∀ x, 0 ≤ ρ x) (hρ₁ : ∫ x, ρ x = 1)
    (hf : Integrable f) :
    (∫ x, ‖(ρ ⋆[lsmul ℝ ℝ] f) x‖) ≤ ∫ x, ‖f x‖ := by
  have hpoint (x : ℝ) : ‖(ρ ⋆[lsmul ℝ ℝ] f) x‖ ≤
      (ρ ⋆[mul ℝ ℝ] (fun y => ‖f y‖)) x := by
    calc
      _ ≤ ∫ y, ‖ρ y • f (x - y)‖ := norm_integral_le_integral_norm _
      _ = _ := by
        simp only [convolution_def, mul_apply', norm_smul,
          Real.norm_of_nonneg (hρ₀ _)]
  calc
    _ ≤ ∫ x, (ρ ⋆[mul ℝ ℝ] (fun y => ‖f y‖)) x :=
      integral_mono (hρ.integrable_convolution (lsmul ℝ ℝ) hf).norm
        (hρ.integrable_convolution (mul ℝ ℝ) hf.norm) hpoint
    _ = _ := by rw [integral_convolution _ hρ hf.norm, hρ₁]; simp

/-- Almost everywhere convergence and an upper bound by the limiting L¹ norm
imply strong L¹ convergence. This norm-defect argument applies to complex
functions, with coefficient one and no measure-size constant. -/
theorem tendsto_integral_norm_sub_of_ae_of_integral_norm_le
    {F : ℕ → ℝ → ℂ} {f : ℝ → ℂ} (hF : ∀ n, Integrable (F n))
    (hf : Integrable f) (hb : ∀ n, (∫ x, ‖F n x‖) ≤ ∫ x, ‖f x‖)
    (ht : ∀ᵐ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => ∫ x, ‖F n x - f x‖) atTop (𝓝 0) := by
  let d : ℕ → ℝ → ℝ := fun n x => ‖F n x - f x‖ - ‖F n x‖
  have hd n : Integrable (d n) := ((hF n).sub hf).norm.sub (hF n).norm
  have hdt : Tendsto (fun n => ∫ x, d n x) atTop (𝓝 (- ∫ x, ‖f x‖)) := by
    rw [← integral_neg]
    apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
      (fun n => (hd n).aestronglyMeasurable) hf.norm
    · intro n
      exact ae_of_all _ fun x => by
        simpa [d, Real.norm_eq_abs] using abs_norm_sub_norm_le (F n x - f x) (F n x)
    · filter_upwards [ht] with x hx
      simpa [d] using (hx.sub_const (f x)).norm.sub hx.norm
  have hupper : Tendsto (fun n => (∫ x, ‖f x‖) + ∫ x, d n x) atTop (𝓝 0) := by
    simpa only [add_neg_cancel] using
      (tendsto_const_nhds (x := ∫ x, ‖f x‖)).add hdt
  apply squeeze_zero (fun n => integral_nonneg (fun x => norm_nonneg _)) _ hupper
  intro n
  rw [show (∫ x, ‖F n x - f x‖) = (∫ x, ‖F n x‖) + ∫ x, d n x by
    have hi := integral_sub ((hF n).sub hf).norm (hF n).norm
    simp only [Pi.sub_apply] at hi
    dsimp only [d]
    rw [hi]
    ring]
  linarith [hb n]

/-- Smooth shrinking bump kernels give global L¹ convergence and never increase
the global L¹ norm. This statement has no constants depending on `f`. -/
theorem exists_smooth_convolution_approximation {f : ℝ → ℂ} (hf : Integrable f) :
    ∃ F : ℕ → ℝ → ℂ, (∀ n, ContDiff ℝ ∞ (F n)) ∧
      (∀ n, Integrable (F n)) ∧
      (∀ n, (∫ x, ‖F n x‖) ≤ ∫ x, ‖f x‖) ∧
      Tendsto (fun n => ∫ x, ‖F n x - f x‖) atTop (𝓝 0) := by
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hr n : 0 < r n := by dsimp [r]; positivity
  let φ : ℕ → ContDiffBump (0 : ℝ) := fun n =>
    ⟨r n / 2, r n, half_pos (hr n), half_lt_self (hr n)⟩
  let F : ℕ → ℝ → ℂ := fun n => (φ n).normed volume ⋆[lsmul ℝ ℝ] f
  have hFi n : Integrable (F n) :=
    (φ n).integrable_normed.integrable_convolution _ hf
  have hFb n : (∫ x, ‖F n x‖) ≤ ∫ x, ‖f x‖ :=
    integral_norm_convolution_le (φ n).integrable_normed
      (φ n).nonneg_normed (φ n).integral_normed hf
  refine ⟨F, fun n => ?_, hFi, hFb, ?_⟩
  · exact (φ n).hasCompactSupport_normed.contDiff_convolution_left _
      (φ n).contDiff_normed hf.locallyIntegrable
  · apply tendsto_integral_norm_sub_of_ae_of_integral_norm_le hFi hf hFb
    apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (K := 2) (φ := φ) tendsto_one_div_add_atTop_nhds_zero_nat _ hf.locallyIntegrable
    exact .of_forall fun n => by dsimp [φ]; linarith

end EmcsfAcExtension.W11
