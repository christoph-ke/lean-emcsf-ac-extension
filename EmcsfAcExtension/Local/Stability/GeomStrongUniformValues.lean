module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeomStrongUniformField
import EmcsfAcExtension.Local.Stability.GeomStrongCauchy
import EmcsfAcExtension.Local.Stability.ExtendedExtras
import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Uniform continuous limits of the geometric fields

The common-label main estimate controls the expansions directly. The
normalized mass Volterra comparison supplies the remaining real field.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace EmcsfAcExtension.Local

/-- Expansion sup-distances are each bounded by the common geometric
distance, with universal coefficient one on the fixed stability box.
No smallness or minimum-radius hypothesis is added. -/
theorem stab_expansion_sup_dist_le_geomDist_c1
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) :
    supDist T S₁.lam S₂.lam ≤ geomDist T S₁ S₂ ∧
      supDist T S₁.nu S₂.nu ≤ geomDist T S₁ S₂ := by
  have hp u v (hpt : (u, v) ∈ triangle 0 T) :
      |S₁.lam u v - S₂.lam u v| ≤ (geomDist T S₁ S₂).toReal ∧
      |S₁.nu u v - S₂.nu u v| ≤ (geomDist T S₁ S₂).toReal := by
    have hg := stab_geom_sum_le h₁s h₂s hpt
    have hr : 0 ≤ S₁.r u v :=
      (div_nonneg (sub_nonneg.mpr hpt.2.1) (by norm_num : (0 : ℝ) ≤ 4)).trans
        (stab_radius_bounds h₁s hpt.1 hpt.2.1 hpt.2.2).1
    have hR := div_nonneg (abs_nonneg (S₁.r u v - S₂.r u v)) hr
    constructor <;> linarith only [hg, hR, abs_nonneg (S₁.lam u v - S₂.lam u v),
      abs_nonneg (S₁.nu u v - S₂.nu u v)]
  constructor
  · apply iSup₂_le
    rintro ⟨u, v⟩ hpt
    rw [← ofReal_norm, Real.norm_eq_abs]
    exact (ENNReal.ofReal_le_ofReal (hp u v hpt).1).trans_eq
      (ENNReal.ofReal_toReal (stab_geomDist_ne_top h₁s h₂s))
  · apply iSup₂_le
    rintro ⟨u, v⟩ hpt
    rw [← ofReal_norm, Real.norm_eq_abs]
    exact (ENNReal.ofReal_le_ofReal (hp u v hpt).2).trans_eq
      (ENNReal.ofReal_toReal (stab_geomDist_ne_top h₁s h₂s))

/-- The expansions and normalized mass have continuous uniform limits
on the complete triangle. The threshold depends only on `A` and its
uniform main constant `C₀`, before all sequence parameters, data,
derivative bounds and minimum radii. The pending main estimate is an
explicit input and the mass limit is proved from Volterra comparison. -/
theorem stab_geometric_uniform_values_of_main_lipschitz_c1
    (A C₀ : ℝ) (hA : 0 < A) (hC₀ : 0 < C₀) :
    ∃ η : ℝ, 0 < η ∧ ∀ (T e ε M : ℝ) (Sn : ℕ → Fields) (hn : ℕ → ℝ → ℂ),
      (∀ n, StabSetting e T ε M A (Sn n) (hn n)) →
      ε ^ 2 + sigma e M T ≤ η →
      (∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, dataDist (hn n) (hn m) T < δ) →
      (∀ n m, jDist T (Sn n) (Sn m) + kDist e T (Sn n) (Sn m) +
        geomDist T (Sn n) (Sn m) ≤ ENNReal.ofReal (C₀ * dataDist (hn n) (hn m) T)) →
      ∃ l n mu : ℝ → ℝ → ℝ,
        ContinuousOn (Function.uncurry l) (triangle 0 T) ∧
        ContinuousOn (Function.uncurry n) (triangle 0 T) ∧
        ContinuousOn (Function.uncurry mu) (triangle 0 T) ∧
        (∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ k ≥ N, ∀ u v, (u, v) ∈ triangle 0 T →
          |(Sn k).lam u v - l u v| < δ) ∧
        (∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ k ≥ N, ∀ u v, (u, v) ∈ triangle 0 T →
          |(Sn k).nu u v - n u v| < δ) ∧
        (∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ k ≥ N, ∀ u v, (u, v) ∈ triangle 0 T →
          |(Sn k).mu u v - mu u v| < δ) := by
  obtain ⟨η, C, hη, hC, hExtra⟩ := stab_extra_fields_of_main_lipschitz A C₀ hA hC₀
  refine ⟨η, hη, ?_⟩
  intro T e ε M Sn hn hset hsmall hdata hmain
  have hg k j := (le_add_of_nonneg_left bot_le).trans (hmain k j)
  have hbL k j := (stab_expansion_sup_dist_le_geomDist_c1 (hset k) (hset j)).1.trans (hg k j)
  have hbN k j := (stab_expansion_sup_dist_le_geomDist_c1 (hset k) (hset j)).2.trans (hg k j)
  have hbM k j := (hExtra T e ε M (Sn k) (Sn j) (hn k) (hn j)
    (hset k) (hset j) hsmall (hmain k j)).1
  have cL := stab_uniform_cauchy_of_pair_bound (ι := Unit) hC₀ hdata (fun k j _ => hbL k j)
  have cN := stab_uniform_cauchy_of_pair_bound (ι := Unit) hC₀ hdata (fun k j _ => hbN k j)
  have cM := stab_uniform_cauchy_of_pair_bound (ι := Unit) hC hdata (fun k j _ => hbM k j)
  have dropUnit {X : ℕ → ℕ → ℝ≥0∞}
      (hc : ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ k ≥ N, ∀ j ≥ N, ∀ _ : Unit, X k j < ENNReal.ofReal δ) :
      ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ k ≥ N, ∀ j ≥ N, X k j < ENNReal.ofReal δ := by
    intro δ hδ
    obtain ⟨N, hN⟩ := hc δ hδ
    exact ⟨N, fun k hk j hj => hN k hk j hj ()⟩
  obtain ⟨l, hl, hlimL⟩ := stab_real_field_limit_of_supDist_cauchy
    (fun k => (hset k).c1.c1_lam.continuousOn) (dropUnit cL)
  obtain ⟨n, hn, hlimN⟩ := stab_real_field_limit_of_supDist_cauchy
    (fun k => (hset k).c1.c1_nu.continuousOn) (dropUnit cN)
  obtain ⟨mu, hmu, hlimM⟩ := stab_real_field_limit_of_supDist_cauchy
    (fun k => continuousOn_mu_aux (hset k).pos (hset k).c1) (dropUnit cM)
  exact ⟨l, n, mu, hl, hn, hmu, hlimL, hlimN, hlimM⟩

end EmcsfAcExtension.Local
