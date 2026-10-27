/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Global.Api.Integrals

/-! # Explicit bridges from finite extended integrals to real values

Every use of `toReal` below has a prior finiteness proof. In particular a
uniform finite bound on proper truncations proves finiteness of the limit
before any real-valued conversion.
-/

public section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace EmcsfAcExtension.Global

/-- [internal] A nonnegative measurable section is integrable if its extended
integral is finite. The finite premise is checked before the real-value bridge. -/
theorem integrableOn_of_lintegral_ofReal_ne_top {f : ℝ → ℝ} {s : Set ℝ}
    (hm : AEStronglyMeasurable f (volume.restrict s))
    (hn : ∀ᵐ x ∂volume.restrict s, 0 ≤ f x)
    (hf : (∫⁻ x in s, ENNReal.ofReal (f x)) ≠ ⊤) : IntegrableOn f s := by
  refine ⟨hm, ?_⟩
  change (∫⁻ x in s, ‖f x‖ₑ) < ⊤
  have he : (fun x => ‖f x‖ₑ) =ᵐ[volume.restrict s]
      (fun x => ENNReal.ofReal (f x)) := hn.mono fun x hx => by
    change ‖f x‖ₑ = ENNReal.ofReal (f x)
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hx]
  rw [lintegral_congr_ae he]
  exact hf.lt_top

/-- [internal] A uniform real bound on proper nonnegative truncation integrals
proves finiteness of the entire extended integral. The supplied bound is uniform
in the truncation index; no constant is selected from the data. -/
theorem lintegral_ofReal_Ico_ne_top_of_intervalIntegral_bounds
    {f : ℝ → ℝ} {a b C : ℝ} {v : ℕ → ℝ}
    (hm : Monotone v) (hv : ∀ n, v n < b) (ht : Tendsto v atTop (𝓝 b))
    (ha : ∀ n, a ≤ v n) (hi : ∀ n, IntervalIntegrable f volume a (v n))
    (hn : ∀ x ∈ Ico a b, 0 ≤ f x)
    (hC : ∀ n, (∫ x in a..v n, f x) ≤ C) :
    (∫⁻ x in Ico a b, ENNReal.ofReal (f x)) ≠ ⊤ := by
  rw [lintegral_ofReal_Ico_eq_iSup_intervalIntegral hm (fun n => (hv n).le) ht ha hi hn]
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (iSup_le fun n => ENNReal.ofReal_le_ofReal (hC n))

end EmcsfAcExtension.Global
