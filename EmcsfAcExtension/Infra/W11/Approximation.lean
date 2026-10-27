module

public import EmcsfAcExtension.Infra.W11.Distance
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# C¹ approximation in the representative W¹¹ distance

Approximate the L¹ derivative by continuous functions and integrate from the
vertex, keeping its value exact. The variation error tends to zero, so variation
and the two-input datum distance converge. The estimates use coefficient one,
uniformly in the datum and interval. This implements the margin choice in
internal project record (internal project record), for `charged_SF_new_version.tex:L5531–L5541` and
`charged_SF_new_version.tex:L6350–L6371`.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace EmcsfAcExtension.W11

/-- A C¹ approximation can preserve the vertex exactly with arbitrarily small
variation error. The tolerance is arbitrary and all coefficients are universal. -/
theorem exists_contDiff_vertex_variation_le {T ε : ℝ} {h : ℝ → ℂ}
    (hT : 0 < T) (hac : AbsolutelyContinuousOnInterval h 0 T) (hε : 0 < ε) :
    ∃ k : ℝ → ℂ, ContDiff ℝ 1 k ∧ k 0 = h 0 ∧ datumVar (k - h) T ≤ ε := by
  have hd := hac.intervalIntegrable_deriv_complex
  have hdi : Integrable (deriv h) (volume.restrict (Ioc 0 T)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).1 hd
  obtain ⟨g, _, herr, hgc, _⟩ := hdi.exists_hasCompactSupport_integral_sub_le hε
  let k : ℝ → ℂ := fun x => h 0 + ∫ t in 0..x, g t
  have hk0 : k 0 = h 0 := by simp [k]
  have hkD x : HasDerivAt k (g x) x :=
    (intervalIntegral.integral_hasDerivAt_right (hgc.intervalIntegrable 0 x)
      (hgc.stronglyMeasurableAtFilter volume (𝓝 x)) hgc.continuousAt).const_add (h 0)
  have hk : ContDiff ℝ 1 k := by
    apply contDiff_one_iff_deriv.2
    refine ⟨fun x => (hkD x).differentiableAt, ?_⟩
    convert hgc using 1
    ext x
    exact (hkD x).deriv
  have hv : eVariationOn (k - h) (Icc 0 T) =
      ENNReal.ofReal (∫ x in 0..T, ‖g x - deriv h x‖) := by
    apply ((hgc.intervalIntegrable 0 T).sub hd
      ).eVariationOn_eq_integral_norm_of_eq_integral hT.le
    intro x hx
    have hsub : uIcc 0 x ⊆ uIcc 0 T := by
      rw [uIcc_of_le hx.1, uIcc_of_le hT.le]
      exact Icc_subset_Icc le_rfl hx.2
    rw [Pi.sub_apply, Pi.sub_apply, hk0, sub_self, zero_add,
      intervalIntegral.integral_sub (hgc.intervalIntegrable 0 x) (hd.mono_set hsub),
      (hac.mono hsub).integral_deriv_eq_sub_complex]
    dsimp only [k]
    abel
  refine ⟨k, hk, hk0, ?_⟩
  unfold datumVar
  rw [hv, ENNReal.toReal_ofReal
    (intervalIntegral.integral_nonneg hT.le (fun _ _ => norm_nonneg _)),
    intervalIntegral.integral_of_le hT.le]
  simpa only [norm_sub_rev] using herr

/-- AC data admit global C¹ approximants with exact vertex and variation error at
most `1/(n+1)`. No constant depends on the datum or interval. -/
theorem exists_contDiff_approximation {T : ℝ} {h : ℝ → ℂ} (hT : 0 < T)
    (hac : AbsolutelyContinuousOnInterval h 0 T) :
    ∃ hn : ℕ → ℝ → ℂ, (∀ n, ContDiff ℝ 1 (hn n)) ∧ (∀ n, hn n 0 = h 0) ∧
      (∀ n, datumVar (hn n - h) T ≤ 1 / ((n : ℝ) + 1)) ∧
      Tendsto (fun n => datumVar (hn n - h) T) atTop (𝓝 0) := by
  have hex (n : ℕ) : ∃ k : ℝ → ℂ, ContDiff ℝ 1 k ∧ k 0 = h 0 ∧
      datumVar (k - h) T ≤ 1 / ((n : ℝ) + 1) :=
    exists_contDiff_vertex_variation_le hT hac (by positivity)
  choose hn hns hnv hne using hex
  refine ⟨hn, hns, hnv, hne, ?_⟩
  exact squeeze_zero (fun _ => ENNReal.toReal_nonneg) hne
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- Convergence of variation errors implies convergence of the variations.
The coefficient in the comparison estimate is one, uniformly in the curves. -/
theorem tendsto_variation_of_sub {a b : ℝ} {F : ℕ → ℝ → ℂ} {f : ℝ → ℂ}
    (hF : ∀ n, BoundedVariationOn (F n) (Icc a b))
    (hf : BoundedVariationOn f (Icc a b))
    (hlim : Tendsto (fun n => (eVariationOn (F n - f) (Icc a b)).toReal) atTop (𝓝 0)) :
    Tendsto (fun n => (eVariationOn (F n) (Icc a b)).toReal) atTop
      (𝓝 (eVariationOn f (Icc a b)).toReal) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => by simpa only [Real.norm_eq_abs] using abs_variation_sub_le (hF n) hf) hlim

/-- Every positive variation margin is eventually satisfied by approximating BV
curves. The coefficient one is uniform in the datum, interval, and margin. -/
theorem eventually_variation_le_add {a b η : ℝ} {F : ℕ → ℝ → ℂ} {f : ℝ → ℂ}
    (hF : ∀ n, BoundedVariationOn (F n) (Icc a b))
    (hf : BoundedVariationOn f (Icc a b))
    (hlim : Tendsto (fun n => (eVariationOn (F n - f) (Icc a b)).toReal) atTop (𝓝 0))
    (hη : 0 < η) :
    ∀ᶠ n in atTop, (eVariationOn (F n) (Icc a b)).toReal ≤
      (eVariationOn f (Icc a b)).toReal + η := by
  exact ((tendsto_order.1 (tendsto_variation_of_sub hF hf hlim)).2 _
    (lt_add_of_pos_right _ hη)).mono fun _ h => h.le

/-- The representative datum distance is continuous when both inputs converge
in that distance. No vertex equality is required for this general continuity result. -/
theorem tendsto_intervalDist {a b : ℝ} {F G : ℕ → ℝ → ℂ} {f g : ℝ → ℂ}
    (hF : ∀ n, BoundedVariationOn (F n) (Icc a b))
    (hG : ∀ n, BoundedVariationOn (G n) (Icc a b))
    (hf : BoundedVariationOn f (Icc a b)) (hg : BoundedVariationOn g (Icc a b))
    (hFlim : Tendsto (fun n => intervalDist a b (F n) f) atTop (𝓝 0))
    (hGlim : Tendsto (fun n => intervalDist a b (G n) g) atTop (𝓝 0)) :
    Tendsto (fun n => intervalDist a b (F n) (G n)) atTop (𝓝 (intervalDist a b f g)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => by simpa only [Real.norm_eq_abs] using
      abs_intervalDist_sub_le hf hg (hF n) (hG n))
  simpa only [zero_add] using hFlim.add hGlim

/-- Exact vertex preservation identifies variation convergence with convergence
in the representative distance, with universal coefficient one. -/
theorem tendsto_intervalDist_of_vertex_eq {a b : ℝ} {F : ℕ → ℝ → ℂ} {f : ℝ → ℂ}
    (hv : ∀ n, F n a = f a)
    (hlim : Tendsto (fun n => (eVariationOn (F n - f) (Icc a b)).toReal) atTop (𝓝 0)) :
    Tendsto (fun n => intervalDist a b (F n) f) atTop (𝓝 0) := by
  simpa only [intervalDist_def, hv, sub_self, norm_zero, zero_add] using! hlim

/-- The paper's `Δ₀` converges under vertex-preserving variation approximation
of both inputs. The comparison has universal coefficient one. -/
theorem tendsto_datum_distance_of_vertex_eq {T : ℝ}
    {F G : ℕ → ℝ → ℂ} {f g : ℝ → ℂ}
    (hF : ∀ n, BoundedVariationOn (F n) (Icc 0 T))
    (hG : ∀ n, BoundedVariationOn (G n) (Icc 0 T))
    (hf : BoundedVariationOn f (Icc 0 T)) (hg : BoundedVariationOn g (Icc 0 T))
    (hvF : ∀ n, F n 0 = f 0) (hvG : ∀ n, G n 0 = g 0)
    (hFlim : Tendsto (fun n => datumVar (F n - f) T) atTop (𝓝 0))
    (hGlim : Tendsto (fun n => datumVar (G n - g) T) atTop (𝓝 0)) :
    Tendsto (fun n => ‖F n 0 - G n 0‖ + datumVar (F n - G n) T) atTop
      (𝓝 (‖f 0 - g 0‖ + datumVar (f - g) T)) := by
  simpa only [intervalDist_zero] using tendsto_intervalDist hF hG hf hg
    (tendsto_intervalDist_of_vertex_eq hvF hFlim)
    (tendsto_intervalDist_of_vertex_eq hvG hGlim)

end EmcsfAcExtension.W11

namespace EmcsfAcExtension.Local.Null

/-- [internal]
C¹ data approximate AC data with exact vertex and variation error `≤ 1/(n+1)`.
The tolerance and coefficient one are uniform in the datum and interval. -/
theorem smallness_preserving_smooth_data {T : ℝ} {h : ℝ → ℂ} (hT : 0 < T)
    (hac : AbsolutelyContinuousOnInterval h 0 T) :
    ∃ hn : ℕ → ℝ → ℂ, (∀ n, ContDiffOn ℝ 1 (hn n) (Icc 0 T)) ∧
      (∀ n, hn n 0 = h 0) ∧
      (∀ n, datumVar (hn n - h) T ≤ 1 / ((n : ℝ) + 1)) ∧
      Tendsto (fun n => datumVar (hn n - h) T) atTop (𝓝 0) := by
  obtain ⟨hn, hs, hv, he, ht⟩ := W11.exists_contDiff_approximation hT hac
  exact ⟨hn, fun n => (hs n).contDiffOn, hv, he, ht⟩

end EmcsfAcExtension.Local.Null

namespace EmcsfAcExtension.Local.Stab

/-- [internal]
C¹ approximants preserve the vertex, converge in variation, and satisfy every
positive variation margin eventually. All coefficients are universal. -/
theorem smooth_data_approximation_choice {T : ℝ} {h : ℝ → ℂ} (hT : 0 < T)
    (hac : AbsolutelyContinuousOnInterval h 0 T) :
    ∃ hn : ℕ → ℝ → ℂ, (∀ n, ContDiffOn ℝ 1 (hn n) (Icc 0 T)) ∧
      (∀ n, hn n 0 = h 0) ∧
      Tendsto (fun n => datumVar (hn n - h) T) atTop (𝓝 0) ∧
      Tendsto (fun n => datumVar (hn n) T) atTop (𝓝 (datumVar h T)) ∧
      (∀ η > (0 : ℝ), ∀ᶠ n in atTop, datumVar (hn n) T ≤ datumVar h T + η) := by
  obtain ⟨hn, hs, hv, _, ht⟩ := W11.exists_contDiff_approximation hT hac
  have hb n : BoundedVariationOn (hn n) (Icc 0 T) :=
    ((hs n).contDiffOn.absolutelyContinuousOnInterval).boundedVariationOn_Icc hT.le
  exact ⟨hn, fun n => (hs n).contDiffOn, hv, ht,
    W11.tendsto_variation_of_sub hb (hac.boundedVariationOn_Icc hT.le) ht,
    fun _ hη => W11.eventually_variation_le_add hb (hac.boundedVariationOn_Icc hT.le) ht hη⟩

end EmcsfAcExtension.Local.Stab
