module

public import EmcsfAcExtension.Local.Defs.Limit

/-! # Classical tails of constructed-limit witnesses

internal project record's analytic helpers require every approximant to be classical, while
the architecture's construction predicate requires eventual classicality.
A single tail discharges that distinction without changing any limit.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

private theorem uniform_reindex {E : Type*} [UniformSpace E]
    {F : ℕ → (ℝ × ℝ) → E} {f : (ℝ × ℝ) → E} {D : Set (ℝ × ℝ)}
    {ns : ℕ → ℕ} (hF : TendstoUniformlyOn F f atTop D)
    (hns : Tendsto ns atTop atTop) :
    TendstoUniformlyOn (fun n => F (ns n)) f atTop D :=
  fun U hU => hns.eventually (hF U hU)

/-- Reindex an existing strong limit along any map tending to infinity.
The limiting fields and all error envelopes are retained by composition;
no constant, estimate, or additional regularity is selected. This is an
internal strong-limit transport helper, with no graph closure claim. -/
theorem StrongLimit.reindex_of_tendsto {e T : ℝ} {Sn : ℕ → Fields} {S : Fields}
    {ns : ℕ → ℕ} (hlim : StrongLimit e T Sn S) (hns : Tendsto ns atTop atTop) :
    StrongLimit e T (fun n => Sn (ns n)) S := by
  refine ⟨uniform_reindex hlim.unif_r hns, uniform_reindex hlim.unif_lam hns,
    uniform_reindex hlim.unif_nu hns, uniform_reindex hlim.unif_m hns,
    uniform_reindex hlim.unif_Q hns, uniform_reindex hlim.unif_phi hns,
    uniform_reindex hlim.unif_A hns, uniform_reindex hlim.unif_theta hns,
    uniform_reindex hlim.unif_xi hns, ?_, ?_⟩
  · obtain ⟨D, hm, ht, hb⟩ := hlim.env_j
    exact ⟨fun n => D (ns n), fun n => hm _, ht.comp hns, fun n => hb _⟩
  · obtain ⟨D, hm, ht, hb⟩ := hlim.env_k
    exact ⟨fun n => D (ns n), fun n => hm _, ht.comp hns, fun n => hb _⟩

/-- An arbitrary constructed-limit witness has an all-classical tail with
the same vertex values and the same actual strong limit. This discharges
eventual classicality when invoking internal project record's all-classical helpers; it does
not assert construction of a strong limit from Cauchy data. -/
theorem IsConstructedLimit.exists_classical_sequence {e T : ℝ} {h : ℝ → ℂ} {S : Fields}
    (hlim : IsConstructedLimit e T h S) :
    ∃ (Sn : ℕ → Fields) (hn : ℕ → ℝ → ℂ), (∀ n, hn n 0 = h 0) ∧
      Tendsto (fun n => eVariationOn (hn n - h) (Icc 0 T)) atTop (𝓝 0) ∧
      (∀ n, IsC1Solution e (Sn n) (triangle 0 T) ∧ IsRestartData (Sn n) (hn n) T) ∧
      StrongLimit e T Sn S := by
  obtain ⟨Sn, hn, hv, ht, hc, hs⟩ := hlim
  obtain ⟨N, hN⟩ := eventually_atTop.1 hc
  exact ⟨fun n => Sn (n + N), fun n => hn (n + N), fun n => hv _,
    ht.comp (tendsto_add_atTop_nat N), fun n => hN _ (Nat.le_add_left _ _),
    hs.reindex_of_tendsto (tendsto_add_atTop_nat N)⟩

end EmcsfAcExtension.Local
