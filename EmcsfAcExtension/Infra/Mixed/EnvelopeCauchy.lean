module

public import EmcsfAcExtension.Infra.W11.Completeness

/-!
# Uniform AC limits over families of intervals

Auxiliary analysis A1 of internal project record, with the endpoint
uniformity ruling internal project record. Completeness is the existing single-interval W¹¹
completeness theorem, applied to sections with zero initial value. No common
null set for the derivatives of different sections is required.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace EmcsfAcExtension.Mixed

/-- A1: uniformly L¹-Cauchy derivatives have densities with uniform L¹ error.
The estimate is uniform in the section labels and endpoints; its coefficient is one.
No convergence of the original endpoint values is required. -/
theorem exists_density_of_uniform_derivative_cauchy {ι : Type*}
    {s t : ι → ℝ} {F : ℕ → ι → ℝ → ℂ}
    (hst : ∀ i, s i ≤ t i)
    (hF : ∀ n i, AbsolutelyContinuousOnInterval (F n i) (s i) (t i))
    (hC : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, ∀ i,
      (∫ x in s i..t i, ‖deriv (F n i) x - deriv (F m i) x‖) < ε) :
    ∃ q : ι → ℝ → ℂ,
      (∀ i, IntervalIntegrable (q i) volume (s i) (t i)) ∧
      (∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ i,
        (∫ x in s i..t i, ‖deriv (F n i) x - q i x‖) < ε) := by
  let H : ℕ → ι → ℝ → ℂ := fun n i x => F n i x - F n i (s i)
  have hH n i : AbsolutelyContinuousOnInterval (H n i) (s i) (t i) :=
    (hF n i).sub (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  have hHd n i : deriv (H n i) = deriv (F n i) := by
    ext x
    simp only [H, deriv_sub_const]
  have hdist n m i : W11.intervalDist (s i) (t i) (H n i) (H m i) =
      ∫ x in s i..t i, ‖deriv (F n i) x - deriv (F m i) x‖ := by
    rw [W11.intervalDist_def]
    simp only [H, sub_self, norm_zero, zero_add]
    change (eVariationOn (H n i - H m i) _).toReal = _
    rw [W11.variation_sub_eq_integral (hst i) (hH n i) (hH m i), hHd, hHd]
  have hex i := W11.exists_ac_limit_of_cauchy (hst i) (fun n => hH n i) (by
    intro ε hε
    obtain ⟨N, hN⟩ := hC ε hε
    exact ⟨N, fun n hn m hm => by rw [hdist]; exact hN n hn m hm i⟩)
  choose g hg hlim hunif hvar using hex
  refine ⟨fun i => deriv (g i), fun i => (hg i).intervalIntegrable_deriv_complex, ?_⟩
  have hbound : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ i,
      W11.intervalDist (s i) (t i) (H n i) (g i) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hC (ε / 2) (half_pos hε)
    refine ⟨N, fun n hn i => ?_⟩
    obtain ⟨m, hmN, hm⟩ := ((eventually_ge_atTop N).and
      ((tendsto_order.1 (hlim i)).2 (ε / 2) (half_pos hε))).exists
    have ht := W11.intervalDist_triangle ((hH n i).boundedVariationOn_Icc (hst i))
      ((hH m i).boundedVariationOn_Icc (hst i)) ((hg i).boundedVariationOn_Icc (hst i))
    rw [hdist] at ht
    linarith [hN n hn m hmN i]
  intro ε hε
  obtain ⟨N, hN⟩ := hbound ε hε
  refine ⟨N, fun n hn i => lt_of_le_of_lt ?_ (hN n hn i)⟩
  change _ ≤ ‖H n i (s i) - g i (s i)‖ +
    (eVariationOn (H n i - g i) (Icc (s i) (t i))).toReal
  rw [W11.variation_sub_eq_integral (hst i) (hH n i) (hg i), hHd]
  exact le_add_of_nonneg_left (norm_nonneg _)

/-- A1: the error of an AC primitive is at most its initial-value error plus its
L¹ density error. Both coefficients are one, independent of all data and endpoints. -/
theorem norm_sub_primitive_le {a b x : ℝ} {f q : ℝ → ℂ} {z : ℂ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hq : IntervalIntegrable q volume a b) (hx : x ∈ Icc a b) :
    ‖f x - (z + ∫ y in a..x, q y)‖ ≤
      ‖f a - z‖ + ∫ y in a..b, ‖deriv f y - q y‖ := by
  have hsub : uIcc a x ⊆ uIcc a b := by
    rw [uIcc_of_le hx.1, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl hx.2
  have hd := hf.intervalIntegrable_deriv_complex
  have hrep : f x - (z + ∫ y in a..x, q y) =
      (f a - z) + ∫ y in a..x, deriv f y - q y := by
    rw [intervalIntegral.integral_sub (hd.mono_set hsub) (hq.mono_set hsub),
      (hf.mono hsub).integral_deriv_eq_sub_complex]
    abel
  rw [hrep]
  apply (norm_add_le _ _).trans
  apply add_le_add le_rfl
  apply (intervalIntegral.norm_integral_le_integral_norm hx.1).trans
  exact intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2
    (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) (hd.sub hq).norm

/-- A1 family form: uniform initial-value and L¹ density convergence imply
uniform primitive convergence on the union of the labeled closed intervals.
The primitive estimate has coefficients one, with no dependence on their lengths. -/
theorem tendstoUniformlyOn_primitive_of_uniform_density {ι : Type*}
    {s t : ι → ℝ} {F : ℕ → ι → ℝ → ℂ} {q : ι → ℝ → ℂ} {z : ι → ℂ}
    (hst : ∀ i, s i ≤ t i)
    (hF : ∀ n i, AbsolutelyContinuousOnInterval (F n i) (s i) (t i))
    (hq : ∀ i, IntervalIntegrable (q i) volume (s i) (t i))
    (hD : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ i,
      (∫ x in s i..t i, ‖deriv (F n i) x - q i x‖) < ε)
    (hz : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ i, ‖F n i (s i) - z i‖ < ε) :
    TendstoUniformlyOn (fun n (p : ι × ℝ) => F n p.1 p.2)
      (fun p => z p.1 + ∫ x in s p.1..p.2, q p.1 x) atTop
      {p | p.2 ∈ Icc (s p.1) (t p.1)} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨ND, hND⟩ := hD (ε / 2) (half_pos hε)
  obtain ⟨Nz, hNz⟩ := hz (ε / 2) (half_pos hε)
  filter_upwards [eventually_ge_atTop (max ND Nz)] with n hn p hp
  rw [dist_comm, dist_eq_norm]
  have h := norm_sub_primitive_le (z := z p.1) (hst p.1) (hF n p.1) (hq p.1) hp
  have hd := hND n ((le_max_left _ _).trans hn) p.1
  have hv := hNz n ((le_max_right _ _).trans hn) p.1
  exact h.trans_lt (by linarith)

/-- A1 with uniform endpoints: construct the family of AC primitive limits,
including their a.e. density identities and uniform convergence. The pointwise
error coefficients are exactly one, independent of the family and interval lengths. -/
theorem exists_ac_family_limit_of_uniform_derivative_cauchy {ι : Type*}
    {s t : ι → ℝ} {F : ℕ → ι → ℝ → ℂ} {z : ι → ℂ}
    (hst : ∀ i, s i ≤ t i)
    (hF : ∀ n i, AbsolutelyContinuousOnInterval (F n i) (s i) (t i))
    (hC : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, ∀ i,
      (∫ x in s i..t i, ‖deriv (F n i) x - deriv (F m i) x‖) < ε)
    (hz : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ i, ‖F n i (s i) - z i‖ < ε) :
    ∃ q : ι → ℝ → ℂ,
      (∀ i, IntervalIntegrable (q i) volume (s i) (t i)) ∧
      (∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ i,
        (∫ x in s i..t i, ‖deriv (F n i) x - q i x‖) < ε) ∧
      (∀ i, AbsolutelyContinuousOnInterval
        (fun x => z i + ∫ y in s i..x, q i y) (s i) (t i)) ∧
      (∀ i, ∀ᵐ x ∂volume.restrict (Icc (s i) (t i)),
        deriv (fun x => z i + ∫ y in s i..x, q i y) x = q i x) ∧
      (∀ n i x, x ∈ Icc (s i) (t i) →
        ‖F n i x - (z i + ∫ y in s i..x, q i y)‖ ≤
          ‖F n i (s i) - z i‖ + ∫ y in s i..t i, ‖deriv (F n i) y - q i y‖) ∧
      TendstoUniformlyOn (fun n (p : ι × ℝ) => F n p.1 p.2)
        (fun p => z p.1 + ∫ x in s p.1..p.2, q p.1 x) atTop
        {p | p.2 ∈ Icc (s p.1) (t p.1)} := by
  obtain ⟨q, hq, hD⟩ := exists_density_of_uniform_derivative_cauchy hst hF hC
  refine ⟨q, hq, hD, ?_, ?_, ?_,
    tendstoUniformlyOn_primitive_of_uniform_density hst hF hq hD hz⟩
  · intro i
    exact ((LipschitzWith.const (z i)).lipschitzOnWith.absolutelyContinuousOnInterval).fun_add
      ((hq i).absolutelyContinuousOnInterval_intervalIntegral_normed left_mem_uIcc)
  · intro i
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [(hq i).ae_hasDerivAt_integral] with x hx hmem
    simpa only [Pi.add_apply, zero_add] using! ((hasDerivAt_const x (z i)).add
      (hx (Icc_subset_uIcc hmem) (s i) left_mem_uIcc)).deriv
  · intro n i x hx
    exact norm_sub_primitive_le (hst i) (hF n i) (hq i) hx

end EmcsfAcExtension.Mixed
