module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeomStrongPure
import EmcsfAcExtension.Local.Stability.GeomStrongSectionC1
import EmcsfAcExtension.Local.Stability.W11Family

/-! # Strong same-direction geometric derivative limits

Uniform L¹ completeness supplies genuine derivative densities on every
complete section. There is no exceptional set of characteristic labels.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace EmcsfAcExtension.Local

/-- [internal]
Pure geometric derivatives converge strongly in L¹, uniformly on all
null sections, charged_SF_new_version.tex:L5436–5439. The main Lipschitz conclusion
is the explicit pending internal project record input. The threshold depends only on
`A` and its uniform main constant `C₀`, before all fields, scales,
coupling, data, derivative bounds and minimum radii. -/
theorem Stab.pure_geometric_strong_limit_of_main_lipschitz_c1
    (A C₀ : ℝ) (hA : 0 < A) (hC₀ : 0 < C₀) :
    ∃ η : ℝ, 0 < η ∧ ∀ (T e ε M : ℝ) (Sn : ℕ → Fields) (hn : ℕ → ℝ → ℂ),
      (∀ n, StabSetting e T ε M A (Sn n) (hn n)) →
      ε ^ 2 + sigma e M T ≤ η →
      (∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, dataDist (hn n) (hn m) T < δ) →
      (∀ n m, jDist T (Sn n) (Sn m) + kDist e T (Sn n) (Sn m) +
        geomDist T (Sn n) (Sn m) ≤ ENNReal.ofReal (C₀ * dataDist (hn n) (hn m) T)) →
      ∃ qL qN : Icc (0 : ℝ) T → ℝ → ℝ,
        (∀ u, Integrable (qL u) (volume.restrict (Icc u.val T))) ∧
        (∀ v, Integrable (qN v) (volume.restrict (Icc 0 v.val))) ∧
        ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N,
          (∀ u, (∫ t in Icc u.val T,
            |pdV (triangle 0 T) (Sn n).lam u.val t - qL u t|) < δ) ∧
          (∀ v, (∫ t in Icc 0 v.val,
            |pdU (triangle 0 T) (Sn n).nu t v.val - qN v t|) < δ) := by
  obtain ⟨η, C, hη, hC, hPair⟩ := stab_pure_geometric_derivatives_of_main_lipschitz_c1 A C₀ hA hC₀
  refine ⟨η, hη, ?_⟩
  intro T e ε M Sn hn hset hsmall hdata hmain
  let I := Icc (0 : ℝ) T
  let DL := fun n (u : I) t => pdV (triangle 0 T) (Sn n).lam u.val t
  let DN := fun n (v : I) t => pdU (triangle 0 T) (Sn n).nu t v.val
  have hDL n (u : I) : Integrable (DL n u) (volume.restrict (Icc u.val T)) :=
    (stab_out_real_partial_primitive_c1 (hset n).pos (hset n).c1.c1_lam u.property).1
  have hDN n (v : I) : Integrable (DN n v) (volume.restrict (Icc 0 v.val)) :=
    (stab_in_real_partial_primitive_c1 (hset n).pos (hset n).c1.c1_nu v.property).1
  have hpair : ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      (∀ u : I, (∫⁻ t in Icc u.val T, ‖DL n u t - DL m u t‖ₑ) < ENNReal.ofReal δ) ∧
      (∀ v : I, (∫⁻ t in Icc 0 v.val, ‖DN n v t - DN m v t‖ₑ) < ENNReal.ofReal δ) := by
    intro δ hδ
    obtain ⟨N, hN⟩ := hdata (δ / C) (div_pos hδ hC)
    refine ⟨N, fun n hnN m hmN => ?_⟩
    have hb := hPair T e ε M (Sn n) (Sn m) (hn n) (hn m)
      (hset n) (hset m) hsmall (hmain n m)
    have hc : C * dataDist (hn n) (hn m) T < δ := by
      simpa only [mul_comm] using (lt_div_iff₀ hC).mp (hN n hnN m hmN)
    have he := (ENNReal.ofReal_lt_ofReal_iff hδ).mpr hc
    exact ⟨fun u => ((le_iSup₂_of_le u.val u.property le_rfl).trans
      ((le_add_of_nonneg_right bot_le).trans hb)).trans_lt he,
      fun v => ((le_iSup₂_of_le v.val v.property le_rfl).trans
        ((le_add_of_nonneg_left bot_le).trans hb)).trans_lt he⟩
  obtain ⟨qL, hqL, hlimL⟩ := stab_family_L1_limit_of_uniform_cauchy hDL (by
    intro δ hδ
    obtain ⟨N, hN⟩ := hpair δ hδ
    exact ⟨N, fun n hn m hm => (hN n hn m hm).1⟩)
  obtain ⟨qN, hqN, hlimN⟩ := stab_family_L1_limit_of_uniform_cauchy hDN (by
    intro δ hδ
    obtain ⟨N, hN⟩ := hpair δ hδ
    exact ⟨N, fun n hn m hm => (hN n hn m hm).2⟩)
  refine ⟨qL, qN, hqL, hqN, ?_⟩
  intro δ hδ
  obtain ⟨NL, hNL⟩ := hlimL δ hδ
  obtain ⟨NN, hNN⟩ := hlimN δ hδ
  exact ⟨max NL NN, fun n hnN =>
    ⟨hNL n ((le_max_left _ _).trans hnN), hNN n ((le_max_right _ _).trans hnN)⟩⟩

end EmcsfAcExtension.Local
