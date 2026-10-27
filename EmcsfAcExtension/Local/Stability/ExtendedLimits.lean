module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Frozen.Fields.Omega2
import EmcsfAcExtension.Local.Stability.MainLipschitz
import EmcsfAcExtension.Local.Stability.GeomStrongPureLimit
import EmcsfAcExtension.Local.Stability.GeomStrongCrossLimit
import EmcsfAcExtension.Local.Stability.GeomStrongAC
import EmcsfAcExtension.Local.Stability.W11FluxStrong

/-! # Unconditional geometric and quadratic-flux strong limit nodes

The density limits and complete-section AC representatives are built
from Cauchy normalized data with no assumed main comparison conclusion.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace EmcsfAcExtension.Local

/-- [node restart-sec-bv-stability-independent#pure-geometric-derivatives-strong]
The complete smooth approximation limit node. The positive threshold
depends only on `A` and the fixed box, before every datum and field,
coupling, time and background, uniformly in higher initial derivatives
and minimum radii. Limits hold on every complete indicated section.
-/
theorem Stab.pure_geometric_derivatives_strong
    (A : ℝ) (hA : 0 < A) :
    ∃ η : ℝ, 0 < η ∧ ∀ (T e ε M : ℝ) (Sn : ℕ → Fields) (hn : ℕ → ℝ → ℂ),
      (∀ n, StabSetting e T ε M A (Sn n) (hn n)) →
      ε ^ 2 + sigma e M T ≤ η →
      (∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, dataDist (hn n) (hn m) T < δ) →
      ∃ qL qN : Icc (0 : ℝ) T → ℝ → ℝ,
        (∀ u, Integrable (qL u) (volume.restrict (Icc u.val T))) ∧
        (∀ v, Integrable (qN v) (volume.restrict (Icc 0 v.val))) ∧
        ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N,
          (∀ u, (∫ t in Icc u.val T,
            |pdV (triangle 0 T) (Sn n).lam u.val t - qL u t|) < δ) ∧
          (∀ v, (∫ t in Icc 0 v.val,
            |pdU (triangle 0 T) (Sn n).nu t v.val - qN v t|) < δ) := by
  obtain ⟨ηm, C₀, hηm, hC₀, hMain⟩ := stab_main_lipschitz A hA
  obtain ⟨η, hη, hLimit⟩ := Stab.pure_geometric_strong_limit_of_main_lipschitz_c1 A C₀ hA hC₀
  refine ⟨min ηm η, lt_min hηm hη, ?_⟩
  intro T e ε M Sn hn hset hsmall hdata
  apply hLimit T e ε M Sn hn hset (hsmall.trans (min_le_right _ _)) hdata
  intro n m
  have hm := hMain T e ε M (Sn n) (Sn m) (hn n) (hn m)
    (hset n) (hset m) (hsmall.trans (min_le_left _ _))
  exact (le_add_of_nonneg_right bot_le).trans ((le_add_of_nonneg_right bot_le).trans
      ((le_add_of_nonneg_right bot_le).trans hm))

/-- [node restart-sec-bv-stability-independent#cross-geometric-derivatives-strong]
The complete smooth approximation limit node. The positive threshold
depends only on `A` and the fixed box, before every datum and field,
coupling, time and background, uniformly in higher initial derivatives
and minimum radii. Limits hold on every complete indicated section.
-/
theorem Stab.cross_geometric_derivatives_strong
    (A : ℝ) (hA : 0 < A) :
    ∃ η : ℝ, 0 < η ∧ ∀ (T e ε M : ℝ) (Sn : ℕ → Fields) (hn : ℕ → ℝ → ℂ),
      (∀ n, StabSetting e T ε M A (Sn n) (hn n)) →
      ε ^ 2 + sigma e M T ≤ η →
      (∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, dataDist (hn n) (hn m) T < δ) →
      ∃ qL qN : Icc (0 : ℝ) T → ℝ → ℝ,
        (∀ v, Integrable (qL v) (volume.restrict (Icc 0 v.val))) ∧
        (∀ u, Integrable (qN u) (volume.restrict (Icc u.val T))) ∧
        (∀ v, AbsolutelyContinuousOnInterval
          (fun u => 1 / 2 + ∫ s in 0..u, qL v s) 0 v.val) ∧
        (∀ u, AbsolutelyContinuousOnInterval
          (fun v => -(1 / 2 + ∫ s in 0..u.val, qL u s) + ∫ s in u.val..v, qN u s)
          u.val T) ∧
        (∀ v, ∀ᵐ u ∂volume.restrict (Icc 0 v.val),
          deriv (fun u => 1 / 2 + ∫ s in 0..u, qL v s) u = qL v u) ∧
        (∀ u, ∀ᵐ v ∂volume.restrict (Icc u.val T),
          deriv (fun v => -(1 / 2 + ∫ s in 0..u.val, qL u s) +
            ∫ s in u.val..v, qN u s) v = qN u v) ∧
        ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N,
          (∀ v, (∫ s in Icc 0 v.val,
            |pdU (triangle 0 T) (Sn n).lam s v.val - qL v s|) < δ) ∧
          (∀ u, (∫ s in Icc u.val T,
            |pdV (triangle 0 T) (Sn n).nu u.val s - qN u s|) < δ) ∧
          (∀ v, ∀ u ∈ Icc 0 v.val,
            |(Sn n).lam u v.val - (1 / 2 + ∫ s in 0..u, qL v s)| < δ) ∧
          (∀ u, ∀ v ∈ Icc u.val T,
            |(Sn n).nu u.val v - (-(1 / 2 + ∫ s in 0..u.val, qL u s) +
              ∫ s in u.val..v, qN u s)| < δ) := by
  obtain ⟨ηm, C₀, hηm, hC₀, hMain⟩ := stab_main_lipschitz A hA
  obtain ⟨η, hη, hLimit⟩ := Stab.cross_geometric_strong_ac_of_main_lipschitz_c1 A C₀ hA hC₀
  refine ⟨min ηm η, lt_min hηm hη, ?_⟩
  intro T e ε M Sn hn hset hsmall hdata
  apply hLimit T e ε M Sn hn hset (hsmall.trans (min_le_right _ _)) hdata
  intro n m
  have hm := hMain T e ε M (Sn n) (Sn m) (hn n) (hn m)
    (hset n) (hset m) (hsmall.trans (min_le_left _ _))
  exact (le_add_of_nonneg_right bot_le).trans ((le_add_of_nonneg_right bot_le).trans
      ((le_add_of_nonneg_right bot_le).trans hm))

/-- [node restart-sec-bv-stability-independent#geometric-AC-limit]
The complete smooth approximation limit node. The positive threshold
depends only on `A` and the fixed box, before every datum and field,
coupling, time and background, uniformly in higher initial derivatives
and minimum radii. Limits hold on every complete indicated section.
-/
theorem Stab.geometric_ac_limit
    (A : ℝ) (hA : 0 < A) :
    ∃ η : ℝ, 0 < η ∧ ∀ (T e ε M : ℝ) (Sn : ℕ → Fields) (hn : ℕ → ℝ → ℂ),
      (∀ k, StabSetting e T ε M A (Sn k) (hn k)) →
      ε ^ 2 + sigma e M T ≤ η →
      (∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ k ≥ N, ∀ j ≥ N, dataDist (hn k) (hn j) T < δ) →
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
  obtain ⟨ηm, C₀, hηm, hC₀, hMain⟩ := stab_main_lipschitz A hA
  obtain ⟨η, hη, hLimit⟩ := Stab.geometric_ac_limit_of_main_lipschitz_c1 A C₀ hA hC₀
  refine ⟨min ηm η, lt_min hηm hη, ?_⟩
  intro T e ε M Sn hn hset hsmall hdata
  apply hLimit T e ε M Sn hn hset (hsmall.trans (min_le_right _ _)) hdata
  intro n m
  have hm := hMain T e ε M (Sn n) (Sn m) (hn n) (hn m)
    (hset n) (hset m) (hsmall.trans (min_le_left _ _))
  exact (le_add_of_nonneg_right bot_le).trans ((le_add_of_nonneg_right bot_le).trans
      ((le_add_of_nonneg_right bot_le).trans hm))

/-- [node restart-sec-bv-stability-independent#weighted-quadratic-flux-strong-limit]
The complete smooth approximation limit node. The positive threshold
depends only on `A` and the fixed box, before every datum and field,
coupling, time and background, uniformly in higher initial derivatives
and minimum radii. Limits hold on every complete indicated section.
-/
theorem Stab.weighted_quadratic_flux_strong_limit
    (A : ℝ) (hA : 0 < A) :
    ∃ η : ℝ, 0 < η ∧
      ∀ (T e ε M : ℝ) (Sn : ℕ → Fields) (hn : ℕ → ℝ → ℂ),
        (∀ n, StabSetting e T ε M A (Sn n) (hn n)) →
        ε ^ 2 + sigma e M T ≤ η →
        (∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
          dataDist (hn n) (hn m) T < δ) →
  
        ∃ qOut qIn : Icc (0 : ℝ) T → ℝ → ℝ,
          (∀ u, Integrable (qOut u) (volume.restrict (Icc u.val T))) ∧
          (∀ v, Integrable (qIn v) (volume.restrict (Icc 0 v.val))) ∧
          ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N,
            (∀ u, (∫ s in Icc u.val T,
              |(Sn n).lam u.val s / (Sn n).r u.val s *
                ‖(Sn n).theta u.val s / ((Sn n).lam u.val s : ℂ)‖ ^ 2 - qOut u s|) < δ) ∧
            (∀ v, (∫ s in Icc 0 v.val,
              |(-(Sn n).nu s v.val) / (Sn n).r s v.val *
                ‖(Sn n).xi s v.val / ((Sn n).nu s v.val : ℂ)‖ ^ 2 - qIn v s|) < δ) := by
  obtain ⟨ηm, C₀, hηm, hC₀, hMain⟩ := stab_main_lipschitz A hA
  obtain ⟨η, hη, hLimit⟩ := Stab.weighted_quadratic_flux_strong_limit_of_main_lipschitz A C₀ hA hC₀
  refine ⟨min ηm η, lt_min hηm hη, ?_⟩
  intro T e ε M Sn hn hset hsmall hdata
  apply hLimit T e ε M Sn hn hset (hsmall.trans (min_le_right _ _)) hdata
  intro n m
  have hm := hMain T e ε M (Sn n) (Sn m) (hn n) (hn m)
    (hset n) (hset m) (hsmall.trans (min_le_left _ _))
  exact (le_add_of_nonneg_right bot_le).trans ((le_add_of_nonneg_right bot_le).trans
      ((le_add_of_nonneg_right bot_le).trans hm))

end EmcsfAcExtension.Local
