module

public import EmcsfAcExtension.Frozen.IntegralForm
import EmcsfAcExtension.Global.Observation.BoundaryData
import EmcsfAcExtension.Global.Terminal.Scalar

/-! # Quantitative boundary estimates for observation

This separates the scalar, mass and Maxwell window estimates from the
gauge and coordinate identities, keeping the combined boundary development
in modules of at most 600 lines. Source: charged_SF_new_version.tex:L2060–2106;
approved internal project record, supporting calculus (B), (B1), (B2).
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global

/-- [internal]
The small outgoing oscillation and incoming error control the measured
scalar difference in `L²`. The coefficient `4T+2` depends only on the
window parameter, uniformly in radius, background and all trace functions. -/
theorem Observation.measured_boundary_l2_of_small_boundary
    {T L ε : ℝ} (φ y z : ℝ → ℂ) (H : ℂ) (hT : 0 ≤ T) (hL : 0 < L) (hε : 0 ≤ ε)
    (hφ : ContinuousOn φ (Icc (-T * L) (T * L)))
    (hy : ContinuousOn y (Icc (-T * L) (T * L)))
    (hz : ContinuousOn z (Icc (-T * L) (T * L)))
    (ha : ∀ t ∈ Icc (-T * L) (T * L), ‖φ t + y t - H‖ ≤ ε / L)
    (hβ : (∫ t in (-T * L)..(T * L), ‖φ t - H + z t‖ ^ 2) ≤ ε ^ 2 / L) :
    (∫ t in (-T * L)..(T * L), ‖y t - z t‖ ^ 2) ≤ (4 * T + 2) * ε ^ 2 / L := by
  have hb : ContinuousOn (fun t => φ t - H + z t) (Icc (-T * L) (T * L)) :=
    (hφ.sub continuousOn_const).add hz
  have hi := Observation.incoming_boundary_l2_of_error_budget
    (fun t => φ t + y t) (fun t => φ t - H + z t) H hT hL
    (hφ.add hy) hb ha (div_nonneg hε hL.le) hβ
  have he (t : ℝ) : (φ t + y t) - H - (φ t - H + z t) = y t - z t := by ring
  simp_rw [he] at hi
  apply hi.trans_eq
  field_simp

/-- [internal]
The normalized scalar clock equation and the measured `L²` bound give
the coefficient `2(T+1)` in its increment estimate. This coefficient is
independent of the background, radius and trace functions. -/
theorem Observation.scalar_boundary_increment_of_l2
    {T L ε : ℝ} (φ y z : ℝ → ℂ) (hT : 0 ≤ T) (hL : 0 < L) (hε : 0 ≤ ε)
    (hy : ContinuousOn y (Icc (-T * L) (T * L)))
    (hz : ContinuousOn z (Icc (-T * L) (T * L)))
    (hform : ∀ s ∈ Icc (-T * L) (T * L), ∀ t ∈ Icc (-T * L) (T * L),
      IntegralForm φ (fun x => (y x - z x) / (2 * L : ℝ)) s t)
    (hQ : (∫ x in (-T * L)..(T * L), ‖y x - z x‖ ^ 2) ≤ (4 * T + 2) * ε ^ 2 / L) :
    ∀ t ∈ Icc (-T * L) (T * L), ‖φ t - φ 0‖ ≤ 2 * (T + 1) * ε / L := by
  have hzero : (0 : ℝ) ∈ Icc (-T * L) (T * L) :=
    ⟨by nlinarith only [mul_nonneg hT hL.le], mul_nonneg hT hL.le⟩
  have hg : ContinuousOn (fun x => (y x - z x) / (2 * L : ℝ)) (Icc (-T * L) (T * L)) :=
    (hy.sub hz).div_const _
  have hi : (∫ x in (-T * L)..(T * L), ‖(y x - z x) / (2 * L : ℝ)‖ ^ 2) =
      (1 / (4 * L ^ 2)) * ∫ x in (-T * L)..(T * L), ‖y x - z x‖ ^ 2 := by
    calc
      _ = ∫ x in (-T * L)..(T * L), (1 / (4 * L ^ 2)) * ‖y x - z x‖ ^ 2 := by
        apply intervalIntegral.integral_congr
        intro x hx
        change ‖(y x - z x) / (2 * L : ℝ)‖ ^ 2 =
          (1 / (4 * L ^ 2)) * ‖y x - z x‖ ^ 2
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (mul_pos (by norm_num) hL), div_pow]
        ring
      _ = _ := intervalIntegral.integral_const_mul _ _
  have hcoef : T * (2 * T + 1) ≤ (2 * (T + 1)) ^ 2 := by
    nlinarith only [sq_nonneg T, hT]
  intro t ht
  have hs := Observation.norm_sub_sq_le_window_of_integralForm hzero ht hg (hform 0 hzero t ht)
  rw [hi] at hs
  have hwindow : 0 ≤ T * L - -T * L := by nlinarith only [mul_nonneg hT hL.le]
  have hmul := mul_le_mul_of_nonneg_left hQ
    (mul_nonneg hwindow (show 0 ≤ 1 / (4 * L ^ 2) by positivity))
  have hs' : ‖φ t - φ 0‖ ^ 2 ≤ T * (2 * T + 1) * (ε / L) ^ 2 := by
    apply hs.trans
    convert hmul using 1
    all_goals field_simp
    all_goals ring
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have he := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (ε / L))
  exact hs'.trans (by convert he using 1; ring)

/-- [internal]
Central normalization and scalar increment control bound the outgoing
ratio by `5(T+1)/L`. The coefficient depends only on the window, uniformly
in the retained background and every scalar value. -/
theorem Observation.scalar_ratio_bound_of_boundary_increment
    {T L ε : ℝ} {φ φ₀ y H P : ℂ} (hT : 0 ≤ T) (hL : 0 < L) (hε : ε ≤ 1)
    (hP : ‖P‖ ≤ 1) (hφ₀ : φ₀ = H + P / (L : ℝ))
    (ha : ‖φ + y - H‖ ≤ ε / L) (hφ : ‖φ - φ₀‖ ≤ 2 * (T + 1) * ε / L) :
    ‖y‖ ≤ 5 * (T + 1) / L := by
  have halg : y = ((φ + y - H) - (φ - φ₀)) - P / (L : ℝ) := by rw [hφ₀]; ring
  have hnum : ε + 2 * (T + 1) * ε + 1 ≤ 5 * (T + 1) := by
    have he := mul_le_mul_of_nonneg_left hε (show 0 ≤ 2 * T + 3 by linarith)
    nlinarith only [he, hT]
  calc
    ‖y‖ = ‖((φ + y - H) - (φ - φ₀)) - P / (L : ℝ)‖ := congrArg norm halg
    _ ≤ ‖φ + y - H‖ + ‖φ - φ₀‖ + ‖P / (L : ℝ)‖ :=
      (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
    _ ≤ ε / L + 2 * (T + 1) * ε / L + 1 / L := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
      exact add_le_add (add_le_add ha hφ) (div_le_div_of_nonneg_right hP hL.le)
    _ = (ε + 2 * (T + 1) * ε + 1) / L := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hnum hL.le

/-- [internal]
The boundary scalar weight has squared integral at most
`1024(T+1)³/L`. The coefficient is uniform in the background, error,
outer radius and trace functions. It bounds both the scalar-modulus sum
needed for mass and the complex sum needed for Maxwell. -/
theorem Observation.boundary_weight_l2_of_ratio_bound
    {T L ε : ℝ} (y z : ℝ → ℂ) (hT : 0 ≤ T) (hL : 0 < L)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hy : ContinuousOn y (Icc (-T * L) (T * L)))
    (hz : ContinuousOn z (Icc (-T * L) (T * L)))
    (hY : ∀ t ∈ Icc (-T * L) (T * L), ‖y t‖ ≤ 5 * (T + 1) / L)
    (hQ : (∫ t in (-T * L)..(T * L), ‖y t - z t‖ ^ 2) ≤ (4 * T + 2) * ε ^ 2 / L) :
    (∫ t in (-T * L)..(T * L), (‖y t‖ + ‖z t‖) ^ 2) ≤ 1024 * (T + 1) ^ 3 / L := by
  have hab : -T * L ≤ T * L := by nlinarith only [mul_nonneg hT hL.le]
  let Y := 5 * (T + 1) / L
  have hY0 : 0 ≤ Y := by dsimp [Y]; positivity
  have hp (t : ℝ) (ht : t ∈ Icc (-T * L) (T * L)) :
      (‖y t‖ + ‖z t‖) ^ 2 ≤ 8 * Y ^ 2 + 2 * ‖y t - z t‖ ^ 2 := by
    have hzq : ‖z t‖ ≤ ‖y t‖ + ‖y t - z t‖ := by
      have he : z t = y t - (y t - z t) := by ring
      calc
        ‖z t‖ = ‖y t - (y t - z t)‖ := congrArg norm he
        _ ≤ _ := norm_sub_le (y t) (y t - z t)
    have hsum : ‖y t‖ + ‖z t‖ ≤ 2 * Y + ‖y t - z t‖ := by linarith [hY t ht]
    have hs := (sq_le_sq₀ (add_nonneg (norm_nonneg _) (norm_nonneg _))
      (by positivity : 0 ≤ 2 * Y + ‖y t - z t‖)).mpr hsum
    nlinarith only [hs, sq_nonneg (2 * Y - ‖y t - z t‖)]
  have iw := ((hy.norm.add hz.norm).pow 2).intervalIntegrable_of_Icc (μ := volume) hab
  have iq := ((hy.sub hz).norm.pow 2).intervalIntegrable_of_Icc (μ := volume) hab
  have hi := intervalIntegral.integral_mono_on hab iw
    (intervalIntegrable_const.add (iq.const_mul 2)) hp
  rw [intervalIntegral.integral_add intervalIntegrable_const (iq.const_mul 2),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul] at hi
  simp only [Pi.pow_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul] at hi
  have hεsq : ε ^ 2 ≤ 1 := by simpa using (sq_le_sq₀ hε0 (by norm_num)).mpr hε1
  have heps := mul_le_mul_of_nonneg_left hεsq (show 0 ≤ 4 * T + 2 by linarith)
  have hnum : 400 * T * (T + 1) ^ 2 + 2 * (4 * T + 2) * ε ^ 2 ≤
      1024 * (T + 1) ^ 3 := by
    nlinarith only [heps, pow_nonneg hT 2, pow_nonneg hT 3, hT]
  calc
    _ ≤ (T * L - -T * L) * (8 * Y ^ 2) + 2 * ((4 * T + 2) * ε ^ 2 / L) := by
      linarith only [hi, hQ]
    _ = (400 * T * (T + 1) ^ 2 + 2 * (4 * T + 2) * ε ^ 2) / L := by
      dsimp [Y]
      field_simp
      ring
    _ ≤ _ := div_le_div_of_nonneg_right hnum hL.le

private theorem mass_density_bound {u v : ℂ} {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    ‖g / 4 * (‖u‖ ^ 2 - ‖v‖ ^ 2)‖ ≤ (1 / 4 : ℝ) * ((‖u‖ + ‖v‖) * ‖u - v‖) := by
  have hn : |‖u‖ ^ 2 - ‖v‖ ^ 2| ≤ (‖u‖ + ‖v‖) * ‖u - v‖ := by
    rw [show ‖u‖ ^ 2 - ‖v‖ ^ 2 = (‖u‖ + ‖v‖) * (‖u‖ - ‖v‖) by ring,
      abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le u v)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hg0 (by norm_num))]
  calc
    _ ≤ (g / 4) * ((‖u‖ + ‖v‖) * ‖u - v‖) :=
      mul_le_mul_of_nonneg_left hn (div_nonneg hg0 (by norm_num))
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hg1 (by norm_num)) (by positivity)

/-- [internal]
The normalized mass clock equation obeys a product-energy estimate with
the exact universal coefficient `1/16`. The weight is the sum of the two
scalar moduli, so no choice of complex phase is made. -/
theorem Observation.mass_boundary_increment_sq_of_integralForm
    {a b : ℝ} (m g : ℝ → ℝ) (y z : ℝ → ℂ) (hab : a ≤ b)
    (hy : ContinuousOn y (Icc a b)) (hz : ContinuousOn z (Icc a b))
    (hg : ∀ t ∈ Icc a b, 0 ≤ g t ∧ g t ≤ 1)
    (hform : IntegralForm m (fun x => g x / 4 * (‖y x‖ ^ 2 - ‖z x‖ ^ 2)) a b) :
    (m b - m a) ^ 2 ≤ (1 / 16 : ℝ) *
      (∫ x in a..b, (‖y x‖ + ‖z x‖) ^ 2) * (∫ x in a..b, ‖y x - z x‖ ^ 2) := by
  let f : ℝ → ℝ := fun x => ‖y x‖ + ‖z x‖
  let q : ℝ → ℝ := fun x => ‖y x - z x‖
  have cf : ContinuousOn f (Icc a b) := hy.norm.add hz.norm
  have cq : ContinuousOn q (Icc a b) := (hy.sub hz).norm
  have hprod := (cf.mul cq).intervalIntegrable_of_Icc (μ := volume) hab
  have hp (x : ℝ) (hx : x ∈ Icc a b) :=
    mass_density_bound (u := y x) (v := z x) (hg x hx).1 (hg x hx).2
  have hbound := (intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := fun x => g x / 4 * (‖y x‖ ^ 2 - ‖z x‖ ^ 2)) hab).trans
    (intervalIntegral.integral_mono_on hab hform.1.norm (hprod.const_mul (1 / 4)) hp)
  rw [← hform.2, intervalIntegral.integral_const_mul] at hbound
  have hn : 0 ≤ ∫ x in a..b, f x * q x :=
    intervalIntegral.integral_nonneg hab (fun x hx => by dsimp [f, q]; positivity)
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) hn)).mpr hbound
  have hcs := Terminal.integral_cauchy_schwarz hab cf cq
  have he := mul_le_mul_of_nonneg_left hcs (show (0 : ℝ) ≤ 1 / 16 by norm_num)
  rw [Real.norm_eq_abs, sq_abs] at hs
  apply hs.trans
  convert he using 1 <;> dsimp [f, q] <;> ring

/-- [internal]
The mass product-energy estimate on any pair of points uses the full
window's two squared-density integrals. The universal coefficient is
exactly `1/16`, uniformly in the window and trace functions. -/
theorem Observation.mass_boundary_increment_sq_window_of_equations
    {a b : ℝ} (m g : ℝ → ℝ) (y z : ℝ → ℂ)
    (hy : ContinuousOn y (Icc a b)) (hz : ContinuousOn z (Icc a b))
    (hg : ∀ x ∈ Icc a b, 0 ≤ g x ∧ g x ≤ 1)
    (hform : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      IntegralForm m (fun x => g x / 4 * (‖y x‖ ^ 2 - ‖z x‖ ^ 2)) s t) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      (m t - m s) ^ 2 ≤ (1 / 16 : ℝ) *
        (∫ x in a..b, (‖y x‖ + ‖z x‖) ^ 2) * (∫ x in a..b, ‖y x - z x‖ ^ 2) := by
  intro s hs t ht
  have hab := hs.1.trans hs.2
  have iw := ((hy.norm.add hz.norm).pow 2).intervalIntegrable_of_Icc (μ := volume) hab
  have iq := ((hy.sub hz).norm.pow 2).intervalIntegrable_of_Icc (μ := volume) hab
  have hw0 : 0 ≤ ∫ x in a..b, (‖y x‖ + ‖z x‖) ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun _ _ => sq_nonneg _)
  have ordered {c d : ℝ} (hc : c ∈ Icc a b) (hd : d ∈ Icc a b) (hcd : c ≤ d) :
      (m d - m c) ^ 2 ≤ (1 / 16 : ℝ) *
        (∫ x in a..b, (‖y x‖ + ‖z x‖) ^ 2) * (∫ x in a..b, ‖y x - z x‖ ^ 2) := by
    have hsub := Icc_subset_Icc hc.1 hd.2
    have he := Observation.mass_boundary_increment_sq_of_integralForm m g y z hcd
      (hy.mono hsub) (hz.mono hsub) (fun x hx => hg x (hsub hx)) (hform c hc d hd)
    have hwi := intervalIntegral.integral_mono_interval hc.1 hcd hd.2
      (ae_of_all _ (fun _ => sq_nonneg _)) iw
    have hqi := intervalIntegral.integral_mono_interval hc.1 hcd hd.2
      (ae_of_all _ (fun _ => sq_nonneg _)) iq
    have hq0 : 0 ≤ ∫ x in c..d, ‖y x - z x‖ ^ 2 :=
      intervalIntegral.integral_nonneg hcd (fun _ _ => sq_nonneg _)
    have hp := mul_le_mul_of_nonneg_left (mul_le_mul hwi hqi hq0 hw0)
      (show (0 : ℝ) ≤ 1 / 16 by norm_num)
    exact he.trans (by simpa only [mul_assoc, Pi.pow_apply, Pi.add_apply, Pi.sub_apply] using! hp)
  rcases le_total s t with hst | hts
  · exact ordered hs ht hst
  · convert ordered ht hs hts using 1
    ring

/-- [internal]
The two boundary `L²` budgets give a mass increment bounded by
`64(T+1)² ε/L`. The coefficient depends only on the window parameter,
uniformly in all trace functions and the normalized radius. -/
theorem Observation.mass_boundary_close_of_l2_budgets
    {T L ε : ℝ} (m g : ℝ → ℝ) (y z : ℝ → ℂ)
    (hT : 0 ≤ T) (hL : 0 < L) (hε : 0 ≤ ε)
    (hy : ContinuousOn y (Icc (-T * L) (T * L)))
    (hz : ContinuousOn z (Icc (-T * L) (T * L)))
    (hg : ∀ t ∈ Icc (-T * L) (T * L), 0 ≤ g t ∧ g t ≤ 1)
    (hform : ∀ s ∈ Icc (-T * L) (T * L), ∀ t ∈ Icc (-T * L) (T * L),
      IntegralForm m (fun x => g x / 4 * (‖y x‖ ^ 2 - ‖z x‖ ^ 2)) s t)
    (hW : (∫ x in (-T * L)..(T * L), (‖y x‖ + ‖z x‖) ^ 2) ≤ 1024 * (T + 1) ^ 3 / L)
    (hQ : (∫ x in (-T * L)..(T * L), ‖y x - z x‖ ^ 2) ≤ (4 * T + 2) * ε ^ 2 / L) :
    ∀ t ∈ Icc (-T * L) (T * L), |m t - m 0| ≤ 64 * (T + 1) ^ 2 * ε / L := by
  have hab : -T * L ≤ T * L := by nlinarith only [mul_nonneg hT hL.le]
  have hzero : (0 : ℝ) ∈ Icc (-T * L) (T * L) :=
    ⟨by nlinarith only [mul_nonneg hT hL.le], mul_nonneg hT hL.le⟩
  have hq0 : 0 ≤ ∫ x in (-T * L)..(T * L), ‖y x - z x‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun _ _ => sq_nonneg _)
  have hp := mul_le_mul_of_nonneg_left
    (mul_le_mul hW hQ hq0 (show 0 ≤ 1024 * (T + 1) ^ 3 / L by positivity))
    (show (0 : ℝ) ≤ 1 / 16 by norm_num)
  have hcoef : (1 / 16 : ℝ) * 1024 * (T + 1) ^ 3 * (4 * T + 2) ≤
      (64 * (T + 1) ^ 2) ^ 2 := by
    nlinarith only [hT, pow_nonneg hT 2, pow_nonneg hT 3, pow_nonneg hT 4]
  have he := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (ε / L))
  intro t ht
  have hs := Observation.mass_boundary_increment_sq_window_of_equations
    m g y z hy hz hg hform 0 hzero t ht
  have hs' : (m t - m 0) ^ 2 ≤ (1 / 16 : ℝ) *
      (1024 * (T + 1) ^ 3 / L) * ((4 * T + 2) * ε ^ 2 / L) :=
    hs.trans (by simpa only [mul_assoc] using hp)
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs]
  exact hs'.trans (by convert he using 1 <;> field_simp)

/-- [internal]
The normalized scalar and mass boundary equations imply both source
boundary-closeness bounds, the mass upper bound two, the retained-background
scalar bound, and a common `L²` weight bound. `C` is chosen using only `T`
before all fields, background, radius and error are quantified. The two
integral-equation inputs are discharged by the internal project record tangent/FTC interface. -/
theorem co_boundary_close_of_boundary_equations {T : ℝ} (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (L ε M : ℝ) (H P : ℂ) (φ y z : ℝ → ℂ) (m g : ℝ → ℝ),
        1 ≤ L → 0 ≤ ε → ε ≤ 1 / C → ‖P‖ ≤ 1 → M ≤ 1 → m 0 = M →
        φ 0 = H + P / (L : ℝ) →
        ContinuousOn φ (Icc (-T * L) (T * L)) →
        ContinuousOn y (Icc (-T * L) (T * L)) →
        ContinuousOn z (Icc (-T * L) (T * L)) →
        (∀ t ∈ Icc (-T * L) (T * L), 0 ≤ g t ∧ g t ≤ 1) →
        (∀ t ∈ Icc (-T * L) (T * L), ‖φ t + y t - H‖ ≤ ε / L) →
        (∫ t in (-T * L)..(T * L), ‖φ t - H + z t‖ ^ 2) ≤ ε ^ 2 / L →
        (∀ s ∈ Icc (-T * L) (T * L), ∀ t ∈ Icc (-T * L) (T * L),
          IntegralForm φ (fun x => (y x - z x) / (2 * L : ℝ)) s t) →
        (∀ s ∈ Icc (-T * L) (T * L), ∀ t ∈ Icc (-T * L) (T * L),
          IntegralForm m (fun x => g x / 4 * (‖y x‖ ^ 2 - ‖z x‖ ^ 2)) s t) →
        (∀ t ∈ Icc (-T * L) (T * L),
          ‖φ t - H - P / (L : ℝ)‖ ≤ C * ε / L ∧ |m t - M| ≤ C * ε / L ∧
          m t ≤ 2 ∧ ‖φ t‖ ≤ ‖H‖ + 2 / L ∧ ‖y t + P / (L : ℝ)‖ ≤ C * ε / L) ∧
        (∫ t in (-T * L)..(T * L), (‖y t‖ + ‖z t‖) ^ 2) ≤ 1024 * (T + 1) ^ 3 / L := by
  let C := 64 * (T + 1) ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  have hC1 : 1 ≤ C := by dsimp [C]; nlinarith only [sq_nonneg T, hT]
  have hCφ : 2 * (T + 1) ≤ C := by dsimp [C]; nlinarith only [sq_nonneg T, hT]
  have hCy : 1 + 2 * (T + 1) ≤ C := by dsimp [C]; nlinarith only [sq_nonneg T, hT]
  refine ⟨C, hC, ?_⟩
  intro L ε M H P φ y z m g hL1 hε0 hεC hP hM hm0 hφ0 hφ hy hz hg ha hβ hφeq hmeq
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have hε1 : ε ≤ 1 := hεC.trans ((div_le_iff₀ hC).mpr (by simpa using hC1))
  have hCε : C * ε ≤ 1 := by simpa only [mul_comm] using (le_div_iff₀ hC).mp hεC
  have hQ := Observation.measured_boundary_l2_of_small_boundary φ y z H hT hL hε0 hφ hy hz ha hβ
  have hφinc := Observation.scalar_boundary_increment_of_l2 φ y z hT hL hε0 hy hz hφeq hQ
  have hY : ∀ t ∈ Icc (-T * L) (T * L), ‖y t‖ ≤ 5 * (T + 1) / L :=
    fun t ht => Observation.scalar_ratio_bound_of_boundary_increment hT hL hε1 hP hφ0
      (ha t ht) (hφinc t ht)
  have hW := Observation.boundary_weight_l2_of_ratio_bound y z hT hL hε0 hε1 hy hz hY hQ
  have hm := Observation.mass_boundary_close_of_l2_budgets m g y z hT hL hε0 hy hz hg hmeq hW hQ
  refine ⟨?_, hW⟩
  intro t ht
  have heφ : φ t - H - P / (L : ℝ) = φ t - φ 0 := by rw [hφ0]; ring
  have hδφ : ‖φ t - H - P / (L : ℝ)‖ ≤ 2 * (T + 1) * ε / L := by rw [heφ]; exact hφinc t ht
  have hφC : ‖φ t - H - P / (L : ℝ)‖ ≤ C * ε / L := hδφ.trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCφ hε0) hL.le)
  have hmC : |m t - M| ≤ C * ε / L := by simpa only [hm0] using hm t ht
  have hm2 : m t ≤ 2 := by
    have he : C * ε / L ≤ 1 := (div_le_iff₀ hL).mpr
      (by simpa only [one_mul] using hCε.trans hL1)
    linarith only [(le_abs_self (m t - M)).trans hmC, hM, he]
  have hφB : ‖φ t‖ ≤ ‖H‖ + 2 / L := by
    have he : φ t = (H + P / (L : ℝ)) + (φ t - H - P / (L : ℝ)) := by ring
    calc
      ‖φ t‖ = ‖(H + P / (L : ℝ)) + (φ t - H - P / (L : ℝ))‖ := congrArg norm he
      _ ≤ ‖H‖ + ‖P / (L : ℝ)‖ + ‖φ t - H - P / (L : ℝ)‖ :=
        (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
      _ ≤ ‖H‖ + 1 / L + C * ε / L := by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
        exact add_le_add (add_le_add_right (div_le_div_of_nonneg_right hP hL.le) _) hφC
      _ ≤ ‖H‖ + 1 / L + 1 / L :=
        add_le_add_right (div_le_div_of_nonneg_right hCε hL.le) _
      _ = _ := by ring
  have hyC : ‖y t + P / (L : ℝ)‖ ≤ C * ε / L := by
    have he : y t + P / (L : ℝ) = (φ t + y t - H) - (φ t - H - P / (L : ℝ)) := by ring
    calc
      _ = ‖(φ t + y t - H) - (φ t - H - P / (L : ℝ))‖ := congrArg norm he
      _ ≤ ‖φ t + y t - H‖ + ‖φ t - H - P / (L : ℝ)‖ := norm_sub_le _ _
      _ ≤ ε / L + 2 * (T + 1) * ε / L := add_le_add (ha t ht) hδφ
      _ = (1 + 2 * (T + 1)) * ε / L := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCy hε0) hL.le
  exact ⟨hφC, hmC, hm2, hφB, hyC⟩

/-- [internal]
The boundary Maxwell equation and the trace bounds derived above give
`|Q(t)-Q(0)| ≤ C η`, with `η=|e|L(1+‖H‖)`. The coefficient is fixed using
only `T`, before all fields, the coupling, background and radius. No
additive electric error or scalar translation is introduced. -/
theorem co_boundary_charge_of_trace_bounds {T : ℝ} (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (e L : ℝ) (H : ℂ) (Q : ℝ → ℝ) (φ y z : ℝ → ℂ), 1 ≤ L →
        ContinuousOn φ (Icc (-T * L) (T * L)) →
        ContinuousOn y (Icc (-T * L) (T * L)) →
        ContinuousOn z (Icc (-T * L) (T * L)) →
        (∀ t ∈ Icc (-T * L) (T * L), ‖φ t‖ ≤ ‖H‖ + 2 / L) →
        (∫ t in (-T * L)..(T * L), (‖y t‖ + ‖z t‖) ^ 2) ≤ 1024 * (T + 1) ^ 3 / L →
        (∀ s ∈ Icc (-T * L) (T * L), ∀ t ∈ Icc (-T * L) (T * L),
          IntegralForm Q (fun x => -(e * L / 2) *
            (starRingEnd ℂ (φ x) * (y x + z x)).im) s t) →
        ∀ t ∈ Icc (-T * L) (T * L),
          |Q t - Q 0| ≤ C * (|e| * L * (1 + ‖H‖)) := by
  let C := 64 * (T + 1) ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  have hcoef : 2048 * T * (T + 1) ^ 3 ≤ C ^ 2 := by
    dsimp [C]
    nlinarith only [hT, pow_nonneg hT 2, pow_nonneg hT 3, pow_nonneg hT 4]
  refine ⟨C, hC, ?_⟩
  intro e L H Q φ y z hL1 hφ hy hz hφB hW hform
  have hL : 0 < L := zero_lt_one.trans_le hL1
  let η := |e| * L * (1 + ‖H‖)
  let B := ‖H‖ + 2 / L
  let A := |e| * L / 2 * B
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hA0 : 0 ≤ A := mul_nonneg (by positivity) hB0
  have hη0 : 0 ≤ η := by dsimp [η]; positivity
  have hB : B ≤ 2 * (1 + ‖H‖) := by
    have he : 2 / L ≤ 2 := (div_le_iff₀ hL).mpr (by linarith only [hL1])
    dsimp [B]
    linarith only [he, norm_nonneg H]
  have hAη : A ≤ η := by
    calc
      _ ≤ (|e| * L / 2) * (2 * (1 + ‖H‖)) := mul_le_mul_of_nonneg_left hB (by positivity)
      _ = _ := by dsimp [η]; ring
  have hAsq := (sq_le_sq₀ hA0 hη0).mpr hAη
  let F : ℝ → ℝ := fun x => -(e * L / 2) *
    (starRingEnd ℂ (φ x) * (y x + z x)).im
  have hc : ContinuousOn F (Icc (-T * L) (T * L)) :=
    continuousOn_const.mul (continuous_im.comp_continuousOn (hφ.star.mul (hy.add hz)))
  have hab : -T * L ≤ T * L := by nlinarith only [mul_nonneg hT hL.le]
  have hzero : (0 : ℝ) ∈ Icc (-T * L) (T * L) :=
    ⟨by nlinarith only [mul_nonneg hT hL.le], mul_nonneg hT hL.le⟩
  have hp (x : ℝ) (hx : x ∈ Icc (-T * L) (T * L)) : ‖F x‖ ≤ A * (‖y x‖ + ‖z x‖) := by
    have hn : |-(e * L / 2)| = |e| * L / 2 := by
      rw [abs_neg, abs_div, abs_mul, abs_of_pos hL]
      norm_num
    dsimp [F]
    rw [abs_mul, hn]
    have he := Complex.abs_im_le_norm (starRingEnd ℂ (φ x) * (y x + z x))
    simp only [norm_mul, starRingEnd_apply, norm_star] at he
    have hm := he.trans (mul_le_mul (hφB x hx) (norm_add_le (y x) (z x))
      (norm_nonneg _) hB0)
    have hb := mul_le_mul_of_nonneg_left hm (show 0 ≤ |e| * L / 2 by positivity)
    simpa only [A, B, starRingEnd_apply, mul_assoc] using! hb
  have ips : ∀ x ∈ Icc (-T * L) (T * L), ‖F x‖ ^ 2 ≤ A ^ 2 * (‖y x‖ + ‖z x‖) ^ 2 := by
    intro x hx
    have he := (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hA0 (add_nonneg (norm_nonneg _) (norm_nonneg _)))).mpr (hp x hx)
    simpa only [mul_pow] using he
  have iw := ((hy.norm.add hz.norm).pow 2).intervalIntegrable_of_Icc (μ := volume) hab
  have hi := intervalIntegral.integral_mono_on hab
    ((hc.norm.pow 2).intervalIntegrable_of_Icc hab) (iw.const_mul (A ^ 2)) ips
  rw [intervalIntegral.integral_const_mul] at hi
  have hW0 : 0 ≤ ∫ x in (-T * L)..(T * L), (‖y x‖ + ‖z x‖) ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun _ _ => sq_nonneg _)
  have hI : (∫ x in (-T * L)..(T * L), ‖F x‖ ^ 2) ≤
      η ^ 2 * (1024 * (T + 1) ^ 3 / L) := by
    apply hi.trans
    exact mul_le_mul hAsq hW hW0 (sq_nonneg η)
  intro t ht
  have hs := Observation.norm_sub_sq_le_window_of_integralForm hzero ht hc (hform 0 hzero t ht)
  have hw : 0 ≤ T * L - -T * L := by nlinarith only [mul_nonneg hT hL.le]
  have he := mul_le_mul_of_nonneg_left hI hw
  have hs' : (Q t - Q 0) ^ 2 ≤ (2048 * T * (T + 1) ^ 3) * η ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs] at hs
    apply hs.trans
    convert he using 1
    field_simp
    ring
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hC.le hη0)).mp
  rw [sq_abs, mul_pow]
  exact hs'.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg η))

end EmcsfAcExtension.Global
