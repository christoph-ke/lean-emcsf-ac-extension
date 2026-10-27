module

public import EmcsfAcExtension.Infra.BV.Semicontinuity
public import EmcsfAcExtension.Infra.W11.Approximation
import EmcsfAcExtension.Infra.W11.Completeness

/-!
# Passing sums of section suprema to a limit

Auxiliary analysis A2 of internal project record. The two partition sums
are passed to the limit together, preserving the coefficient one in front of
their sum. Empty section families and infinite variation are allowed.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace EmcsfAcExtension.Mixed

/-- Sums of suprema retain a common bound under pointwise limits. The coefficient
one is uniform in the two index types, and empty types are allowed. -/
theorem iSup_add_iSup_le_of_tendsto {η ι κ : Type*} {p : Filter η} [NeBot p]
    {A : η → ι → ℝ≥0∞} {B : η → κ → ℝ≥0∞} {a : ι → ℝ≥0∞} {b : κ → ℝ≥0∞}
    {L : η → ℝ≥0∞} {l : ℝ≥0∞}
    (hA : ∀ i, Tendsto (fun n => A n i) p (𝓝 (a i)))
    (hB : ∀ j, Tendsto (fun n => B n j) p (𝓝 (b j)))
    (hL : Tendsto L p (𝓝 l))
    (hbound : ∀ᶠ n in p, (⨆ i, A n i) + (⨆ j, B n j) ≤ L n) :
    (⨆ i, a i) + (⨆ j, b j) ≤ l := by
  cases isEmpty_or_nonempty ι
  · simp only [iSup_of_empty, bot_eq_zero, zero_add] at hbound ⊢
    apply iSup_le
    intro j
    exact le_of_tendsto_of_tendsto (hB j) hL
      (hbound.mono fun n hn => (le_iSup (B n) j).trans hn)
  · cases isEmpty_or_nonempty κ
    · simp only [iSup_of_empty, bot_eq_zero, add_zero] at hbound ⊢
      apply iSup_le
      intro i
      exact le_of_tendsto_of_tendsto (hA i) hL
        (hbound.mono fun n hn => (le_iSup (A n) i).trans hn)
    · apply ENNReal.iSup_add_iSup_le
      intro i j
      exact le_of_tendsto_of_tendsto ((hA i).add (hB j)) hL
        (hbound.mono fun n hn => (add_le_add (le_iSup (A n) i)
          (le_iSup (B n) j)).trans hn)

/-- A2 sum form: the sum of the two section-variation suprema passes to a
pointwise limit with coefficient one, without finiteness assumptions.
The section sets, linearly ordered domains, and target spaces may differ. -/
theorem iSup_eVariationOn_add_le_of_tendsto {η ι κ α β E H : Type*}
    [LinearOrder α] [LinearOrder β] [PseudoEMetricSpace E] [PseudoEMetricSpace H]
    {p : Filter η} [NeBot p]
    {F : η → ι → α → E} {G : η → κ → β → H} {f : ι → α → E} {g : κ → β → H}
    {s : ι → Set α} {t : κ → Set β} {L : η → ℝ≥0∞} {l : ℝ≥0∞}
    (hF : ∀ i x, x ∈ s i → Tendsto (fun n => F n i x) p (𝓝 (f i x)))
    (hG : ∀ j x, x ∈ t j → Tendsto (fun n => G n j x) p (𝓝 (g j x)))
    (hL : Tendsto L p (𝓝 l))
    (hbound : ∀ᶠ n in p,
      (⨆ i, eVariationOn (F n i) (s i)) + (⨆ j, eVariationOn (G n j) (t j)) ≤ L n) :
    (⨆ i, eVariationOn (f i) (s i)) + (⨆ j, eVariationOn (g j) (t j)) ≤ l := by
  classical
  let P := (i : ι) × ℕ × {u : ℕ → α // Monotone u ∧ ∀ k, u k ∈ s i}
  let Q := (j : κ) × ℕ × {u : ℕ → β // Monotone u ∧ ∀ k, u k ∈ t j}
  let A (n : η) (z : P) :=
    ∑ k ∈ Finset.range z.2.1, edist (F n z.1 (z.2.2.1 (k + 1))) (F n z.1 (z.2.2.1 k))
  let B (n : η) (z : Q) :=
    ∑ k ∈ Finset.range z.2.1, edist (G n z.1 (z.2.2.1 (k + 1))) (G n z.1 (z.2.2.1 k))
  let a (z : P) :=
    ∑ k ∈ Finset.range z.2.1, edist (f z.1 (z.2.2.1 (k + 1))) (f z.1 (z.2.2.1 k))
  let b (z : Q) :=
    ∑ k ∈ Finset.range z.2.1, edist (g z.1 (z.2.2.1 (k + 1))) (g z.1 (z.2.2.1 k))
  have hA z : Tendsto (fun n => A n z) p (𝓝 (a z)) := by
    apply tendsto_finsetSum
    intro k hk
    exact (hF z.1 _ (z.2.2.property.2 _)).edist (hF z.1 _ (z.2.2.property.2 _))
  have hB z : Tendsto (fun n => B n z) p (𝓝 (b z)) := by
    apply tendsto_finsetSum
    intro k hk
    exact (hG z.1 _ (z.2.2.property.2 _)).edist (hG z.1 _ (z.2.2.property.2 _))
  have h := iSup_add_iSup_le_of_tendsto hA hB hL (hbound.mono fun n hn => by
    apply le_trans _ hn
    apply add_le_add <;> apply iSup_le
    · intro z
      exact (eVariationOn.sum_le z.2.2.property.1 z.2.2.property.2).trans
        (le_iSup (fun i => eVariationOn (F n i) (s i)) z.1)
    · intro z
      exact (eVariationOn.sum_le z.2.2.property.1 z.2.2.property.2).trans
        (le_iSup (fun j => eVariationOn (G n j) (t j)) z.1))
  simpa only [a, b, eVariationOn, iSup_sigma, P, Q] using h

end EmcsfAcExtension.Mixed
