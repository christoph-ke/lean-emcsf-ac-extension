module

public import Mathlib

/-!
# Algebra and interval gluing for bounded variation

The estimates use extended variation, so they hold even when a variation is infinite.
All constants are explicit and uniform in the functions and the underlying set.
-/

public section

open Set

variable {α E : Type*} [LinearOrder α] [NormedAddCommGroup E]
  {f g : α → E} {s : Set α}

namespace eVariationOn

/-- Variation is subadditive under pointwise addition. -/
theorem add_le (f g : α → E) (s : Set α) :
    eVariationOn (fun x => f x + g x) s ≤ eVariationOn f s + eVariationOn g s := by
  apply iSup_le
  rintro ⟨n, u, hu, hs⟩
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        (edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i))) :=
      Finset.sum_le_sum fun _ _ => edist_add_add_le _ _ _ _
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (sum_le hu hs) (sum_le hu hs)

/-- Negation preserves extended variation. -/
theorem neg (f : α → E) (s : Set α) :
    eVariationOn (fun x => -f x) s = eVariationOn f s := by
  simp only [eVariationOn, edist_neg_neg]

/-- Variation is subadditive under pointwise subtraction. -/
theorem sub_le (f g : α → E) (s : Set α) :
    eVariationOn (fun x => f x - g x) s ≤ eVariationOn f s + eVariationOn g s := by
  simpa only [sub_eq_add_neg, neg] using add_le f (fun x => -g x) s

/-- Variation on consecutive closed intervals is additive, including infinite values. -/
theorem Icc_eq_add {M : Type*} [PseudoEMetricSpace M] (f : α → M)
    {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) :
    eVariationOn f (Icc a c) = eVariationOn f (Icc a b) + eVariationOn f (Icc b c) := by
  simpa only [univ_inter] using (Icc_add_Icc f hab hbc (mem_univ b)).symm

end eVariationOn

namespace BoundedVariationOn

/-- The sum of two functions of bounded variation has bounded variation. -/
theorem add (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (fun x => f x + g x) s :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf, hg⟩) (eVariationOn.add_le f g s)

/-- The negative of a function of bounded variation has bounded variation. -/
theorem neg (hf : BoundedVariationOn f s) : BoundedVariationOn (fun x => -f x) s := by
  unfold BoundedVariationOn
  rwa [eVariationOn.neg]

/-- The difference of two functions of bounded variation has bounded variation. -/
theorem sub (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (fun x => f x - g x) s :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf, hg⟩) (eVariationOn.sub_le f g s)

/-- A fixed scalar preserves bounded variation. -/
theorem const_smul {𝕜 : Type*} [SeminormedRing 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E]
    (hf : BoundedVariationOn f s) (c : 𝕜) :
    BoundedVariationOn (fun x => c • f x) s :=
  (lipschitzWith_smul c).comp_boundedVariationOn hf

/-- Bounded variation glues across the shared endpoint of consecutive closed intervals. -/
theorem trans_Icc {M : Type*} [PseudoEMetricSpace M] {f : α → M} {a b c : α}
    (hf : BoundedVariationOn f (Icc a b)) (hg : BoundedVariationOn f (Icc b c))
    (hab : a ≤ b) (hbc : b ≤ c) : BoundedVariationOn f (Icc a c) := by
  unfold BoundedVariationOn at *
  rw [eVariationOn.Icc_eq_add f hab hbc]
  exact ENNReal.add_ne_top.mpr ⟨hf, hg⟩

end BoundedVariationOn
