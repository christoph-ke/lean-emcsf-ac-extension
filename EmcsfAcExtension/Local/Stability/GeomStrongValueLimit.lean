module

public import EmcsfAcExtension.Local.Stability.GeomStrongFamily
import Mathlib.Topology.MetricSpace.Cauchy

/-! # Prescribed uniform limits of strong real characteristic families

A uniform value limit and uniform L¹-Cauchy densities identify the
same primitive on every complete section. This fixes all endpoints
before absolute continuity is transported to the prescribed field.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace EmcsfAcExtension.Local

/-- A uniformly Cauchy real family has a uniform real limit. There is
no compactness, boundedness, radius or estimate-constant premise. -/
theorem stab_real_uniform_limit_of_uniform_cauchy {ι : Type*} {F : ℕ → ι → ℝ}
    (hC : ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, ∀ i, |F n i - F m i| < δ) :
    ∃ f : ι → ℝ, ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ i, |F n i - f i| < δ := by
  have hc : UniformCauchySeqOn F atTop univ := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro δ hδ
    obtain ⟨N, hN⟩ := hC δ hδ
    exact ⟨N, fun n hn m hm i _ => by simpa only [Real.dist_eq] using hN n hn m hm i⟩
  choose f hf using fun i => cauchySeq_tendsto_of_complete (hc.cauchySeq (mem_univ i))
  have hu := hc.tendstoUniformlyOn_of_tendsto (fun i _ => hf i)
  refine ⟨f, ?_⟩
  intro δ hδ
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.1 hu) δ hδ)
  exact ⟨N, fun n hn i => by simpa only [Real.dist_eq, abs_sub_comm] using hN n hn i (mem_univ i)⟩

/-- A prescribed uniform value limit is AC on every section when the
classical densities are uniformly L¹-Cauchy and satisfy FTC. Genuine
integrable limiting densities converge uniformly in the section L¹
norm and recover every endpoint of the limiting field. All primitive
error coefficients are one; no derivative or interval bound is hidden.
-/
theorem stab_real_ac_limit_of_uniform_and_density_cauchy {ι : Type*}
    {a b : ι → ℝ} {F D : ℕ → ι → ℝ → ℝ} {f : ι → ℝ → ℝ}
    (hab : ∀ i, a i ≤ b i)
    (hD : ∀ n i, Integrable (D n i) (volume.restrict (Icc (a i) (b i))))
    (hC : ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, ∀ i,
      (∫⁻ x in Icc (a i) (b i), ‖D n i x - D m i x‖ₑ) < ENNReal.ofReal δ)
    (hprimitive : ∀ n i x, x ∈ Icc (a i) (b i) →
      F n i x = F n i (a i) + ∫ t in a i..x, D n i t)
    (hvalue : ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ i, ∀ x ∈ Icc (a i) (b i),
      |F n i x - f i x| < δ) :
    ∃ q : ι → ℝ → ℝ,
      (∀ i, Integrable (q i) (volume.restrict (Icc (a i) (b i)))) ∧
      (∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ i,
        (∫ t in Icc (a i) (b i), |D n i t - q i t|) < δ) ∧
      (∀ i, AbsolutelyContinuousOnInterval (f i) (a i) (b i)) ∧
      ∀ i x, x ∈ Icc (a i) (b i) →
        f i x = f i (a i) + ∫ t in a i..x, q i t := by
  obtain ⟨q, hq, hDensity, hAC, hDeriv, hPoint, hUniform⟩ :=
    stab_real_ac_family_of_density_cauchy hab hD hC hprimitive (z := fun i => f i (a i)) (by
      intro δ hδ
      obtain ⟨N, hN⟩ := hvalue δ hδ
      exact ⟨N, fun n hn i => hN n hn i (a i) ⟨le_rfl, hab i⟩⟩)
  have heq i x (hx : x ∈ Icc (a i) (b i)) :
      f i x = f i (a i) + ∫ t in a i..x, q i t := by
    by_contra hne
    let δ := |f i x - (f i (a i) + ∫ t in a i..x, q i t)|
    have hδ : 0 < δ := abs_pos.mpr (sub_ne_zero.mpr hne)
    obtain ⟨Nf, hNf⟩ := hvalue (δ / 2) (half_pos hδ)
    obtain ⟨Np, hNp⟩ := eventually_atTop.1
      ((Metric.tendstoUniformlyOn_iff.1 hUniform) (δ / 2) (half_pos hδ))
    let n := max Nf Np
    have hf := hNf n (le_max_left _ _) i x hx
    have hp := hNp n (le_max_right _ _) (i, x) hx
    have hp' : |F n i x - (f i (a i) + ∫ t in a i..x, q i t)| < δ / 2 := by
      simpa only [Real.dist_eq, abs_sub_comm] using hp
    have hh : δ < δ := calc
      _ ≤ |f i x - F n i x| + |F n i x - (f i (a i) + ∫ t in a i..x, q i t)| :=
        abs_sub_le _ _ _
      _ < δ / 2 + δ / 2 := add_lt_add (by rwa [abs_sub_comm]) hp'
      _ = _ := by ring
    exact (lt_irrefl δ) hh
  refine ⟨q, hq, hDensity, ?_, heq⟩
  intro i
  exact (hAC i).congr (fun x hx => (heq i x (by rwa [uIcc_of_le (hab i)] at hx)).symm)

end EmcsfAcExtension.Local
