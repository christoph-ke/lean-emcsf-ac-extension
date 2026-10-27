module

public import EmcsfAcExtension.Local.Defs.Setting

/-! # Passing quantitative pair bounds to uniform Cauchy estimates

A single Cauchy index controls all labels when the comparison constant
is fixed before the fields and section labels.
-/

public section

open Set
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- A uniform pair bound `X≤Cδ₀` and Cauchy data give a uniform positive
Cauchy index for every label. The explicit constant `C>0` is fixed
before the sequence and labels; no other parameter enters. -/
theorem stab_uniform_cauchy_of_pair_bound {ι : Type*} {C : ℝ}
    {d : ℕ → ℕ → ℝ} {X : ℕ → ℕ → ι → ℝ≥0∞} (hC : 0 < C)
    (hd : ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, d n m < δ)
    (hbound : ∀ n m i, X n m i ≤ ENNReal.ofReal (C * d n m)) :
    ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, ∀ i, X n m i < ENNReal.ofReal δ := by
  intro δ hδ
  obtain ⟨N, hN⟩ := hd (δ / C) (div_pos hδ hC)
  refine ⟨N, fun n hn m hm i => ?_⟩
  apply (hbound n m i).trans_lt
  apply (ENNReal.ofReal_lt_ofReal_iff hδ).mpr
  simpa only [mul_comm] using (lt_div_iff₀ hC).mp (hN n hn m hm)

end EmcsfAcExtension.Local
