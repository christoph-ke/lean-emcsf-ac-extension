module

public import EmcsfAcExtension.Local.Defs.Limit
public import EmcsfAcExtension.Local.Defs.Bounds
import EmcsfAcExtension.Infra.BV.Semicontinuity
import EmcsfAcExtension.Local.Limit.StabilityPointwise

/-! # Characteristic geometric variation in the primary limit

Variation lower semicontinuity retains the exact smooth constants and the
original limiting datum variation, in both null directions.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

private theorem variation_le_limit {E : Type*} [NormedAddCommGroup E]
    {F : ℕ → ℝ → E} {f : ℝ → E} {K : Set ℝ} {Bn : ℕ → ℝ≥0∞} {B : ℝ≥0∞}
    (hF : ∀ x ∈ K, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hB : Tendsto Bn atTop (𝓝 B)) (hb : ∀ n, eVariationOn (F n) K ≤ Bn n) :
    eVariationOn f K ≤ B := by
  apply (eVariationOn.le_liminf_of_tendsto hF).trans
  rw [← hB.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall hb) (by isBoundedDefault) (by isBoundedDefault)

/-- Pass the four geometric variation bounds in both null directions to a
primary strong limit. `C` is unchanged from the smooth bounds, uniformly in
the datum and approximation. The actual frozen mass ratio and Omega² are
used, with their limiting denominators explicitly identified. -/
theorem StrongLimit.geometry_variation_of_smoothBounds {C e T d : ℝ}
    {Sn : ℕ → Fields} {dn : ℕ → ℝ} {Mn : ℕ → ℝ} {S : Fields}
    (hlim : StrongLimit e T Sn S)
    (hmu : ∀ p ∈ triangle 0 T, Tendsto (fun n => (Sn n).mu p.1 p.2) atTop (𝓝 (S.mu p.1 p.2)))
    (hg : ∀ p ∈ triangle 0 T, 1 - S.mu p.1 p.2 ≠ 0)
    (hd : Tendsto dn atTop (𝓝 d))
    (hb : ∀ n, SmoothBounds C e T (dn n) (Mn n) (Sn n)) :
    (∀ u ∈ Icc 0 T,
      eVariationOn (S.lam u) (Icc u T) ≤ ENNReal.ofReal (C * d ^ 2) ∧
      eVariationOn (S.nu u) (Icc u T) ≤ ENNReal.ofReal (C * d ^ 2) ∧
      eVariationOn (S.mu u) (Icc u T) ≤ ENNReal.ofReal (C * d ^ 2) ∧
      eVariationOn (S.Omega2 u) (Icc u T) ≤ ENNReal.ofReal (C * d ^ 2)) ∧
    (∀ v ∈ Icc 0 T,
      eVariationOn (fun u => S.lam u v) (Icc 0 v) ≤ ENNReal.ofReal (C * d ^ 2) ∧
      eVariationOn (fun u => S.nu u v) (Icc 0 v) ≤ ENNReal.ofReal (C * d ^ 2) ∧
      eVariationOn (fun u => S.mu u v) (Icc 0 v) ≤ ENNReal.ofReal (C * d ^ 2) ∧
      eVariationOn (fun u => S.Omega2 u v) (Icc 0 v) ≤ ENNReal.ofReal (C * d ^ 2)) := by
  have hbound : Tendsto (fun n => ENNReal.ofReal (C * dn n ^ 2)) atTop
      (𝓝 (ENNReal.ofReal (C * d ^ 2))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hd.pow 2).const_mul C)
  have hO p (hp : p ∈ triangle 0 T) :
      Tendsto (fun n => (Sn n).Omega2 p.1 p.2) atTop (𝓝 (S.Omega2 p.1 p.2)) :=
    (((hlim.unif_nu.tendsto_at hp).const_mul (-4)).mul (hlim.unif_lam.tendsto_at hp)).div
      ((hmu p hp).const_sub 1) (hg p hp)
  constructor
  · intro u hu
    have hp v (hv : v ∈ Icc u T) : (u, v) ∈ triangle 0 T := ⟨hu.1, hv.1, hv.2⟩
    have hs n := (hb n).geomTV_out u hu
    exact ⟨variation_le_limit (fun v hv => hlim.unif_lam.tendsto_at (hp v hv)) hbound
        (fun n => le_self_add.trans (le_self_add.trans (le_self_add.trans (hs n)))),
      variation_le_limit (fun v hv => hlim.unif_nu.tendsto_at (hp v hv)) hbound
        (fun n => le_add_self.trans (le_self_add.trans (le_self_add.trans (hs n)))),
      variation_le_limit (fun v hv => hmu _ (hp v hv)) hbound
        (fun n => le_add_self.trans (le_self_add.trans (hs n))),
      variation_le_limit (fun v hv => hO _ (hp v hv)) hbound
        (fun n => le_add_self.trans (hs n))⟩
  · intro v hv
    have hp u (hu : u ∈ Icc 0 v) : (u, v) ∈ triangle 0 T := ⟨hu.1, hu.2, hv.2⟩
    have hs n := (hb n).geomTV_in v hv
    exact ⟨variation_le_limit (fun u hu => hlim.unif_lam.tendsto_at (hp u hu)) hbound
        (fun n => le_self_add.trans (le_self_add.trans (le_self_add.trans (hs n)))),
      variation_le_limit (fun u hu => hlim.unif_nu.tendsto_at (hp u hu)) hbound
        (fun n => le_add_self.trans (le_self_add.trans (le_self_add.trans (hs n)))),
      variation_le_limit (fun u hu => hmu _ (hp u hu)) hbound
        (fun n => le_add_self.trans (le_self_add.trans (hs n))),
      variation_le_limit (fun u hu => hO _ (hp u hu)) hbound
        (fun n => le_add_self.trans (hs n))⟩

/-- The actual incoming ordinary scalar variation and the two transverse
scalar variations pass to the strong limit. Constants are inherited unchanged
from the smooth family, uniformly in section labels and in all datum sizes. -/
theorem StrongLimit.scalar_variation_of_smoothBounds {C e T d : ℝ}
    {Sn : ℕ → Fields} {dn Mn : ℕ → ℝ} {S : Fields}
    (hlim : StrongLimit e T Sn S)
    (hl : ∀ p ∈ triangle 0 T, S.lam p.1 p.2 ≠ 0)
    (hn : ∀ p ∈ triangle 0 T, S.nu p.1 p.2 ≠ 0)
    (hd : Tendsto dn atTop (𝓝 d))
    (hb : ∀ n, SmoothBounds C e T (dn n) (Mn n) (Sn n)) :
    (∀ v ∈ Icc 0 T, eVariationOn (fun u => S.b u v) (Icc 0 v) ≤ ENNReal.ofReal (C * d)) ∧
    (∀ v ∈ Icc 0 T, eVariationOn (fun u => S.a u v) (Icc 0 v) ≤ ENNReal.ofReal C) ∧
    (∀ u ∈ Icc 0 T, eVariationOn (S.b u) (Icc u T) ≤ ENNReal.ofReal C) := by
  have hbound : Tendsto (fun n => ENNReal.ofReal (C * dn n)) atTop (𝓝 (ENNReal.ofReal (C * d))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hd.const_mul C)
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    exact variation_le_limit
      (fun u hu => hlim.tendsto_b_of_nu_ne_zero (p := (u, v)) ⟨hu.1, hu.2, hv.2⟩ (hn (u, v) ⟨hu.1,
          hu.2, hv.2⟩))
      hbound (fun n => (hb n).tv_in v hv)
  · intro v hv
    exact variation_le_limit
      (fun u hu => hlim.tendsto_a_of_lam_ne_zero (p := (u, v)) ⟨hu.1, hu.2, hv.2⟩ (hl (u, v) ⟨hu.1,
          hu.2, hv.2⟩))
      tendsto_const_nhds (fun n => (hb n).crossTV.1 v hv)
  · intro u hu
    exact variation_le_limit
      (fun v hv => hlim.tendsto_b_of_nu_ne_zero (p := (u, v)) ⟨hu.1, hv.1, hv.2⟩ (hn (u, v) ⟨hu.1,
          hv.1, hv.2⟩))
      tendsto_const_nhds (fun n => (hb n).crossTV.2 u hu)

end EmcsfAcExtension.Local
