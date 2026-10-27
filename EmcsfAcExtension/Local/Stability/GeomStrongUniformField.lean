module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeomStrongValueLimit
import Mathlib.Topology.UniformSpace.UniformApproximation

/-! # Uniform completion of real fields on the closed triangle

The zero extension is used solely to select a complete real function
space. Continuity is passed on the actual closed triangle, including
all characteristic endpoints.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace EmcsfAcExtension.Local

/-- Continuous real fields whose triangle sup-distances are Cauchy
have a continuous uniform triangle limit. No finite-derivative bound,
radius cutoff, data size or estimate constant is an assumption. -/
theorem stab_real_field_limit_of_supDist_cauchy {T : ℝ} {F : ℕ → ℝ → ℝ → ℝ}
    (hc : ∀ n, ContinuousOn (Function.uncurry (F n)) (triangle 0 T))
    (hC : ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      supDist T (F n) (F m) < ENNReal.ofReal δ) :
    ∃ f : ℝ → ℝ → ℝ,
      ContinuousOn (Function.uncurry f) (triangle 0 T) ∧
      ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ u v,
        (u, v) ∈ triangle 0 T → |F n u v - f u v| < δ := by
  classical
  let Z := fun n => (triangle 0 T).indicator (Function.uncurry (F n))
  have hz : ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, ∀ p, |Z n p - Z m p| < δ := by
    intro δ hδ
    obtain ⟨N, hN⟩ := hC δ hδ
    refine ⟨N, fun n hn m hm p => ?_⟩
    by_cases hp : p ∈ triangle 0 T
    · dsimp only [Z]
      rw [indicator_of_mem hp, indicator_of_mem hp]
      have hh : ENNReal.ofReal |F n p.1 p.2 - F m p.1 p.2| < ENNReal.ofReal δ := by
        rw [← Real.norm_eq_abs, ofReal_norm]
        exact (le_iSup₂_of_le p hp le_rfl).trans_lt (hN n hn m hm)
      exact (ENNReal.ofReal_lt_ofReal_iff hδ).mp hh
    · simp only [Z, indicator_of_notMem hp, sub_self, abs_zero]
      exact hδ
  obtain ⟨f, hf⟩ := stab_real_uniform_limit_of_uniform_cauchy hz
  have hvalue : ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ u v,
      (u, v) ∈ triangle 0 T → |F n u v - f (u, v)| < δ := by
    intro δ hδ
    obtain ⟨N, hN⟩ := hf δ hδ
    refine ⟨N, fun n hn u v hp => ?_⟩
    have hh := hN n hn (u, v)
    simpa only [Z, indicator_of_mem hp, Function.uncurry_def] using! hh
  have hu : TendstoUniformlyOn (fun n => Function.uncurry (F n)) f atTop (triangle 0 T) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    obtain ⟨N, hN⟩ := hvalue δ hδ
    filter_upwards [eventually_ge_atTop N] with n hn p hp
    simpa only [Real.dist_eq, abs_sub_comm, Function.uncurry_def] using! hN n hn p.1 p.2 hp
  exact ⟨fun u v => f (u, v), hu.continuousOn (Eventually.frequently (Filter.Eventually.of_forall
      hc)), hvalue⟩

end EmcsfAcExtension.Local
