module

public import EmcsfAcExtension.Local.Stability.W11Family
public import EmcsfAcExtension.Infra.AC.Primitive

/-! # Real characteristic primitive limits

Uniform L¹ completeness is applied to prescribed real densities, then
their primitives pass through both endpoints of every section.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace EmcsfAcExtension.Local

/-- Real section primitives have uniform AC limits when their densities
are uniformly L¹-Cauchy and their initial values converge uniformly.
Every coefficient in the error estimate is exactly one, independent of
labels, interval lengths and all density or derivative bounds.
-/
theorem stab_real_ac_family_of_density_cauchy {ι : Type*}
    {a b : ι → ℝ} {F D : ℕ → ι → ℝ → ℝ} {z : ι → ℝ}
    (hab : ∀ i, a i ≤ b i)
    (hD : ∀ n i, Integrable (D n i) (volume.restrict (Icc (a i) (b i))))
    (hC : ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, ∀ i,
      (∫⁻ x in Icc (a i) (b i), ‖D n i x - D m i x‖ₑ) < ENNReal.ofReal δ)
    (hprimitive : ∀ n i x, x ∈ Icc (a i) (b i) →
      F n i x = F n i (a i) + ∫ t in a i..x, D n i t)
    (hz : ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ i, |F n i (a i) - z i| < δ) :
    ∃ q : ι → ℝ → ℝ,
      (∀ i, Integrable (q i) (volume.restrict (Icc (a i) (b i)))) ∧
      (∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ i,
        (∫ t in Icc (a i) (b i), |D n i t - q i t|) < δ) ∧
      (∀ i, AbsolutelyContinuousOnInterval
        (fun x => z i + ∫ t in a i..x, q i t) (a i) (b i)) ∧
      (∀ i, ∀ᵐ x ∂volume.restrict (Icc (a i) (b i)),
        deriv (fun x => z i + ∫ t in a i..x, q i t) x = q i x) ∧
      (∀ n i x, x ∈ Icc (a i) (b i) →
        |F n i x - (z i + ∫ t in a i..x, q i t)| ≤ |F n i (a i) - z i| +
          ∫ t in Icc (a i) (b i), |D n i t - q i t|) ∧
      TendstoUniformlyOn (fun n (p : ι × ℝ) => F n p.1 p.2)
        (fun p => z p.1 + ∫ t in a p.1..p.2, q p.1 t) atTop
        {p | p.2 ∈ Icc (a p.1) (b p.1)} := by
  obtain ⟨q, hq, hlim⟩ := stab_family_L1_limit_of_uniform_cauchy hD hC
  have hiq i : IntervalIntegrable (q i) volume (a i) (b i) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (hab i)).2 (hq i)
  have hiD n i : IntervalIntegrable (D n i) volume (a i) (b i) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (hab i)).2 (hD n i)
  have hpoint n i x (hx : x ∈ Icc (a i) (b i)) :
      |F n i x - (z i + ∫ t in a i..x, q i t)| ≤ |F n i (a i) - z i| +
        ∫ t in Icc (a i) (b i), |D n i t - q i t| := by
    have hsub : uIcc (a i) x ⊆ uIcc (a i) (b i) := by
      rw [uIcc_of_le hx.1, uIcc_of_le (hab i)]
      exact Icc_subset_Icc le_rfl hx.2
    have heq : F n i x - (z i + ∫ t in a i..x, q i t) =
        (F n i (a i) - z i) + ∫ t in a i..x, D n i t - q i t := by
      rw [intervalIntegral.integral_sub ((hiD n i).mono_set hsub) ((hiq i).mono_set hsub),
        hprimitive n i x hx]
      ring
    rw [heq]
    apply (abs_add_le _ _).trans
    apply add_le_add le_rfl
    have hn := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
      (f := fun t => D n i t - q i t) hx.1
    rw [Real.norm_eq_abs] at hn
    simp only [Real.norm_eq_abs] at hn
    apply hn.trans
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (hab i)]
    exact intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2
      (ae_of_all _ (fun _ => abs_nonneg _)) ((hiD n i).sub (hiq i)).abs
  refine ⟨q, hq, hlim, ?_, ?_, hpoint, ?_⟩
  · intro i
    exact ((LipschitzWith.const (z i)).lipschitzOnWith.absolutelyContinuousOnInterval).fun_add
      ((hiq i).absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)
  · intro i
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [(hiq i).ae_hasDerivAt_integral] with x hx hmem
    simpa only [Pi.add_apply, zero_add] using! ((hasDerivAt_const x (z i)).add
      (hx (Icc_subset_uIcc hmem) (a i) left_mem_uIcc)).deriv
  · rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    obtain ⟨Nd, hNd⟩ := hlim (δ / 2) (half_pos hδ)
    obtain ⟨Nz, hNz⟩ := hz (δ / 2) (half_pos hδ)
    filter_upwards [eventually_ge_atTop (max Nd Nz)] with n hn p hp
    rw [dist_comm, Real.dist_eq]
    exact (hpoint n p.1 p.2 hp).trans_lt (add_lt_add
      (hNz n ((le_max_right _ _).trans hn) p.1)
      (hNd n ((le_max_left _ _).trans hn) p.1) |>.trans_eq (by ring))

end EmcsfAcExtension.Local
