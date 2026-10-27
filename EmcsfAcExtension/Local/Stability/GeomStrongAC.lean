module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Frozen.Fields.Omega2
import EmcsfAcExtension.Local.Stability.GeomStrongUniformValues
import EmcsfAcExtension.Local.Stability.GeomStrongOmegaLimit
import EmcsfAcExtension.Local.Stability.GeomStrongACSections
import EmcsfAcExtension.Local.Stability.GeomStrongCauchy
import EmcsfAcExtension.Local.Stability.GeomStrongPure
import EmcsfAcExtension.Local.Stability.GeomStrongCross
import EmcsfAcExtension.Local.Stability.GeomStrongMassDerivatives
import EmcsfAcExtension.Local.Stability.GeomStrongSectionC1
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassRegularity

/-! # Absolute continuity of the geometric limits

Uniform geometric values and strong complete-section derivative
comparison identify one limiting field in both characteristic
orientations. The positive mass gap is retained before forming Ω².
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace EmcsfAcExtension.Local

/-- [internal]
The expansions, mass ratio and metric coefficient have uniform limits
with AC representatives on every complete characteristic section,
charged_SF_new_version.tex:L5449–5451. The main Lipschitz conclusion is the explicit
pending internal project record input. The threshold depends only on `A` and its
uniform constant `C₀`, before all fields, data, coupling, scale,
background and derivative bounds, uniformly in minimum radii. -/
theorem Stab.geometric_ac_limit_of_main_lipschitz_c1
    (A C₀ : ℝ) (hA : 0 < A) (hC₀ : 0 < C₀) :
    ∃ η : ℝ, 0 < η ∧ ∀ (T e ε M : ℝ) (Sn : ℕ → Fields) (hn : ℕ → ℝ → ℂ),
      (∀ k, StabSetting e T ε M A (Sn k) (hn k)) →
      ε ^ 2 + sigma e M T ≤ η →
      (∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ k ≥ N, ∀ j ≥ N, dataDist (hn k) (hn j) T < δ) →
      (∀ k j, jDist T (Sn k) (Sn j) + kDist e T (Sn k) (Sn j) +
        geomDist T (Sn k) (Sn j) ≤ ENNReal.ofReal (C₀ * dataDist (hn k) (hn j) T)) →
      ∃ l n mu : ℝ → ℝ → ℝ,
        ContinuousOn (Function.uncurry l) (triangle 0 T) ∧
        ContinuousOn (Function.uncurry n) (triangle 0 T) ∧
        ContinuousOn (Function.uncurry mu) (triangle 0 T) ∧
        (∀ u v, (u, v) ∈ triangle 0 T → 1 / 4 ≤ 1 - mu u v) ∧
        (∀ u ∈ Icc 0 T,
          AbsolutelyContinuousOnInterval (l u) u T ∧
          AbsolutelyContinuousOnInterval (n u) u T ∧
          AbsolutelyContinuousOnInterval (mu u) u T ∧
          AbsolutelyContinuousOnInterval (fun v => -4 * n u v * l u v / (1 - mu u v)) u T) ∧
        (∀ v ∈ Icc 0 T,
          AbsolutelyContinuousOnInterval (fun u => l u v) 0 v ∧
          AbsolutelyContinuousOnInterval (fun u => n u v) 0 v ∧
          AbsolutelyContinuousOnInterval (fun u => mu u v) 0 v ∧
          AbsolutelyContinuousOnInterval (fun u => -4 * n u v * l u v / (1 - mu u v)) 0 v) ∧
        (∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ k ≥ N, ∀ u v, (u, v) ∈ triangle 0 T →
          |(Sn k).lam u v - l u v| < δ) ∧
        (∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ k ≥ N, ∀ u v, (u, v) ∈ triangle 0 T →
          |(Sn k).nu u v - n u v| < δ) ∧
        (∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ k ≥ N, ∀ u v, (u, v) ∈ triangle 0 T →
          |(Sn k).mu u v - mu u v| < δ) ∧
        (∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ k ≥ N, ∀ u v, (u, v) ∈ triangle 0 T →
          |(Sn k).Omega2 u v - (-4 * n u v * l u v / (1 - mu u v))| < δ) := by
  obtain ⟨ηv, hηv, hValues⟩ := stab_geometric_uniform_values_of_main_lipschitz_c1 A C₀ hA hC₀
  obtain ⟨ηp, Cp, hηp, hCp, hPure⟩ := stab_pure_geometric_derivatives_of_main_lipschitz_c1 A C₀ hA
      hC₀
  obtain ⟨ηc, Cc, hηc, hCc, hCross⟩ :=
    Stab.cross_geometric_derivatives_difference_of_main_lipschitz_c1 A C₀ hA hC₀
  obtain ⟨ηm, Cm, hηm, hCm, hMass⟩ := Stab.mass_derivatives_strong_of_main_lipschitz_c1 A C₀ hA hC₀
  refine ⟨min ηv (min ηp (min ηc ηm)), lt_min hηv (lt_min hηp (lt_min hηc hηm)), ?_⟩
  intro T e ε M Sn hn hset hsmall hdata hmain
  let I := Icc (0 : ℝ) T
  have hs1 := hsmall.trans (min_le_right _ _)
  have hs2 := hs1.trans (min_le_right _ _)
  obtain ⟨l, n, mu, hl, hnC, hmu, hVL, hVN, hVM⟩ :=
    hValues T e ε M Sn hn hset (hsmall.trans (min_le_left _ _)) hdata hmain
  have hp k j := hPure T e ε M (Sn k) (Sn j) (hn k) (hn j)
    (hset k) (hset j) (hs1.trans (min_le_left _ _)) (hmain k j)
  have hc k j := hCross T e ε M (Sn k) (Sn j) (hn k) (hn j)
    (hset k) (hset j) (hs2.trans (min_le_left _ _)) (hmain k j)
  have hm k j := hMass T e ε M (Sn k) (Sn j) (hn k) (hn j)
    (hset k) (hset j) (hs2.trans (min_le_right _ _)) (hmain k j)
  have cLo := stab_uniform_cauchy_of_pair_bound hCp hdata (fun k j (u : I) =>
    (le_iSup₂_of_le u.val u.property le_rfl).trans ((le_add_of_nonneg_right bot_le).trans (hp k j)))
  have cLi := stab_uniform_cauchy_of_pair_bound hCc hdata (fun k j (v : I) =>
    (le_iSup₂_of_le v.val v.property le_rfl).trans ((le_add_of_nonneg_left bot_le).trans (hc k j)))
  have cNo := stab_uniform_cauchy_of_pair_bound hCc hdata (fun k j (u : I) =>
    (le_iSup₂_of_le u.val u.property le_rfl).trans ((le_add_of_nonneg_right bot_le).trans (hc k j)))
  have cNi := stab_uniform_cauchy_of_pair_bound hCp hdata (fun k j (v : I) =>
    (le_iSup₂_of_le v.val v.property le_rfl).trans ((le_add_of_nonneg_left bot_le).trans (hp k j)))
  have cMo := stab_uniform_cauchy_of_pair_bound hCm hdata (fun k j (u : I) =>
    (le_iSup₂_of_le u.val u.property le_rfl).trans ((le_add_of_nonneg_right bot_le).trans (hm k j)))
  have cMi := stab_uniform_cauchy_of_pair_bound hCm hdata (fun k j (v : I) =>
    (le_iSup₂_of_le v.val v.property le_rfl).trans ((le_add_of_nonneg_left bot_le).trans (hm k j)))
  have dropLabels {X : ℕ → ℕ → ℝ → ℝ≥0∞}
      (hC : ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ k ≥ N, ∀ j ≥ N, ∀ i : I, X k j i.val < ENNReal.ofReal δ) :
      ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ k ≥ N, ∀ j ≥ N, ∀ i ∈ Icc 0 T, X k j i < ENNReal.ofReal δ := by
    intro δ hδ
    obtain ⟨N, hN⟩ := hC δ hδ
    exact ⟨N, fun k hk j hj i hi => hN k hk j hj ⟨i, hi⟩⟩
  have hL := stab_bicharacteristic_ac_of_strong_density_cauchy
    (F := fun k => (Sn k).lam)
    (Do := fun k => pdV (triangle 0 T) (Sn k).lam)
    (Di := fun k => pdU (triangle 0 T) (Sn k).lam)
    (fun k u hu => (stab_out_real_partial_primitive_c1 (hset k).pos (hset k).c1.c1_lam hu).1)
    (fun k v hv => (stab_in_real_partial_primitive_c1 (hset k).pos (hset k).c1.c1_lam hv).1)
    (fun k u hu => (stab_out_real_partial_primitive_c1 (hset k).pos (hset k).c1.c1_lam hu).2)
    (fun k v hv => (stab_in_real_partial_primitive_c1 (hset k).pos (hset k).c1.c1_lam hv).2)
    (dropLabels cLo) (dropLabels cLi) hVL
  have hN := stab_bicharacteristic_ac_of_strong_density_cauchy
    (F := fun k => (Sn k).nu)
    (Do := fun k => pdV (triangle 0 T) (Sn k).nu)
    (Di := fun k => pdU (triangle 0 T) (Sn k).nu)
    (fun k u hu => (stab_out_real_partial_primitive_c1 (hset k).pos (hset k).c1.c1_nu hu).1)
    (fun k v hv => (stab_in_real_partial_primitive_c1 (hset k).pos (hset k).c1.c1_nu hv).1)
    (fun k u hu => (stab_out_real_partial_primitive_c1 (hset k).pos (hset k).c1.c1_nu hu).2)
    (fun k v hv => (stab_in_real_partial_primitive_c1 (hset k).pos (hset k).c1.c1_nu hv).2)
    (dropLabels cNo) (dropLabels cNi) hVN
  have hM := stab_bicharacteristic_ac_of_strong_density_cauchy
    (F := fun k => (Sn k).mu)
    (Do := fun k u => deriv ((Sn k).mu u))
    (Di := fun k u v => deriv (fun s => (Sn k).mu s v) u)
    (fun k u hu => (stab_real_ac_section_primitive hu.2
      (stab_mu_out_ac (hset k) hu.1 hu.2 le_rfl)).1)
    (fun k v hv => (stab_real_ac_section_primitive hv.1
      (stab_mu_in_ac (hset k) le_rfl hv.1 hv.2)).1)
    (fun k u hu => (stab_real_ac_section_primitive hu.2
      (stab_mu_out_ac (hset k) hu.1 hu.2 le_rfl)).2)
    (fun k v hv => (stab_real_ac_section_primitive hv.1
      (stab_mu_in_ac (hset k) le_rfl hv.1 hv.2)).2)
    (dropLabels cMo) (dropLabels cMi) hVM
  have hbox := stab_geometric_limit_box_c1 hset hVL hVN hVM
  refine ⟨l, n, mu, hl, hnC, hmu, fun u v hp => (hbox u v hp).2.2, ?_, ?_,
    hVL, hVN, hVM, stab_omega_uniform_of_geometric_uniform_c1 hset hVL hVN hVM⟩
  · intro u hu
    refine ⟨hL.1 u hu, hN.1 u hu, hM.1 u hu,
      stab_omega_ac_of_components (hL.1 u hu) (hN.1 u hu) (hM.1 u hu) ?_⟩
    intro v hv
    rw [uIcc_of_le hu.2] at hv
    exact (hbox u v ⟨hu.1, hv.1, hv.2⟩).2.2
  · intro v hv
    refine ⟨hL.2 v hv, hN.2 v hv, hM.2 v hv,
      stab_omega_ac_of_components (hL.2 v hv) (hN.2 v hv) (hM.2 v hv) ?_⟩
    intro u hu
    rw [uIcc_of_le hv.1] at hu
    exact (hbox u v ⟨hu.1, hu.2, hv.2⟩).2.2

end EmcsfAcExtension.Local
