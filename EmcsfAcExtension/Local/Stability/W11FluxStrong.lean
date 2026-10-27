module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.FluxDifferenceCloseOut
import EmcsfAcExtension.Local.Stability.FluxDifferenceCloseIn
import EmcsfAcExtension.Local.Stability.FluxDifferenceRegularity
import EmcsfAcExtension.Infra.Mixed.FiberCauchy
import EmcsfAcExtension.Local.Stability.W11Family

/-! # Strong weighted quadratic-flux limits

The proved absolute weighted differences give uniform L¹-Cauchy
families on both characteristic orientations. Completeness is applied
to these densities themselves, so their limits contain no flux defect.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace EmcsfAcExtension.Local

/-- Weighted quadratic-flux pair comparison conditional on the first
three main Lipschitz clauses. Constants depend only on `A` and its
uniform main constant `C₀`, before all field parameters, data, pairs,
derivative suprema and minimum radii. -/
theorem Stab.quadratic_flux_difference_of_main_lipschitz
    (A C₀ : ℝ) (hA : 0 < A) (hC₀ : 0 < C₀) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        jDist T S₁ S₂ + kDist e T S₁ S₂ + geomDist T S₁ S₂ ≤
          ENNReal.ofReal (C₀ * dataDist h₁ h₂ T) →
        (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T, ENNReal.ofReal
          |S₁.lam u v / S₁.r u v * ‖S₁.theta u v / (S₁.lam u v : ℂ)‖ ^ 2 -
            S₂.lam u v / S₂.r u v * ‖S₂.theta u v / (S₂.lam u v : ℂ)‖ ^ 2|) +
        (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v, ENNReal.ofReal
          |(-S₁.nu u v) / S₁.r u v * ‖S₁.xi u v / (S₁.nu u v : ℂ)‖ ^ 2 -
            (-S₂.nu u v) / S₂.r u v * ‖S₂.xi u v / (S₂.nu u v : ℂ)‖ ^ 2|) ≤
          ENNReal.ofReal (C * dataDist h₁ h₂ T) := by
  obtain ⟨ηo, Co, hηo, hCo, hOut⟩ := Stab.outgoing_quadratic_flux_difference A hA
  obtain ⟨ηi, Ci, hηi, hCi, hIn⟩ := Stab.incoming_quadratic_flux_difference A hA
  let C := 2 * Co * C₀ + Ci * (4 * C₀ + 1)
  refine ⟨min ηo (min ηi (1 / 4)), C, lt_min hηo (lt_min hηi (by norm_num)),
    by dsimp only [C]; positivity, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall hmain
  let Δ := dataDist h₁ h₂ T
  let B := C₀ * Δ
  have hΔ : 0 ≤ Δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hB : 0 ≤ B := mul_nonneg hC₀.le hΔ
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hσ : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hs : ε ^ 2 + sigma e M T ≤ 1 / 4 :=
    hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hε1 : ε ≤ 1 := by nlinarith only [hs, hσ, sq_nonneg (ε - 1)]
  have hεsq : ε ^ 2 ≤ 1 := by linarith only [hs, hσ]
  have hσ1 : sigma e M T ≤ 1 := by linarith only [hs, sq_nonneg ε]
  have hb {X : ℝ≥0∞} (hX : X ≤ ENNReal.ofReal B) : X.toReal ≤ B := by
    simpa only [ENNReal.toReal_ofReal hB] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hX
  have hJ : (jDist T S₁ S₂).toReal ≤ B := hb
    ((le_add_of_nonneg_right bot_le).trans ((le_add_of_nonneg_right bot_le).trans hmain))
  have hK : (kDist e T S₁ S₂).toReal ≤ B := hb
    ((le_add_of_nonneg_left bot_le).trans ((le_add_of_nonneg_right bot_le).trans hmain))
  have hG : (geomDist T S₁ S₂).toReal ≤ B := hb ((le_add_of_nonneg_left bot_le).trans hmain)
  have ho := hOut T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hsmall.trans (min_le_left _ _))
  have hi := hIn T e ε M S₁ S₂ h₁ h₂ h₁s h₂s
    (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
  apply (add_le_add ho hi).trans
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ Co * 1 * B + Co * 1 * B +
        (Ci * 1 * B + Ci * 1 * B + Ci * 1 * 1 * (B + 1 * Δ + 1 * B)) := by gcongr
    _ = _ := by dsimp only [B, C]; ring

/-- [internal]
Weighted Raychaudhuri fluxes have genuine L¹ limits, uniformly over both
families of characteristic sections. The main Lipschitz record is the
only pending internal project record input. The threshold is chosen from `A` and the
fixed box before all data, solutions and derivative bounds; `C₀` is the
uniform main constant. This is the smooth local form of the weighted
quadratic-flux strong-limit node. -/
theorem Stab.weighted_quadratic_flux_strong_limit_of_main_lipschitz
    (A C₀ : ℝ) (hA : 0 < A) (hC₀ : 0 < C₀) :
    ∃ η : ℝ, 0 < η ∧
      ∀ (T e ε M : ℝ) (Sn : ℕ → Fields) (hn : ℕ → ℝ → ℂ),
        (∀ n, StabSetting e T ε M A (Sn n) (hn n)) →
        ε ^ 2 + sigma e M T ≤ η →
        (∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
          dataDist (hn n) (hn m) T < δ) →
        (∀ n m, jDist T (Sn n) (Sn m) + kDist e T (Sn n) (Sn m) +
          geomDist T (Sn n) (Sn m) ≤ ENNReal.ofReal (C₀ * dataDist (hn n) (hn m) T)) →
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
  obtain ⟨η, C, hη, hC, hPair⟩ :=
    Stab.quadratic_flux_difference_of_main_lipschitz A C₀ hA hC₀
  refine ⟨η, hη, ?_⟩
  intro T e ε M Sn hn hset hsmall hdata hmain
  let I := Icc (0 : ℝ) T
  let Fo := fun n (u : I) s => (Sn n).lam u.val s / (Sn n).r u.val s *
    ‖(Sn n).theta u.val s / ((Sn n).lam u.val s : ℂ)‖ ^ 2
  let Fi := fun n (v : I) s => (-(Sn n).nu s v.val) / (Sn n).r s v.val *
    ‖(Sn n).xi s v.val / ((Sn n).nu s v.val : ℂ)‖ ^ 2
  have hFo n (u : I) : Integrable (Fo n u) (volume.restrict (Icc u.val T)) := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le u.property.2).1
    apply ContinuousOn.intervalIntegrable_of_Icc u.property.2
    exact (stab_out_quadratic_flux_continuous (hset n)).comp
      (continuous_const.prodMk continuous_id).continuousOn
        (fun s hs => ⟨u.property.1, hs.1, hs.2⟩)
  have hFi n (v : I) : Integrable (Fi n v) (volume.restrict (Icc 0 v.val)) := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le v.property.1).1
    apply ContinuousOn.intervalIntegrable_of_Icc v.property.1
    exact (stab_in_quadratic_flux_continuous (hset n)).comp
      (continuous_id.prodMk continuous_const).continuousOn
        (fun s hs => ⟨hs.1, hs.2, v.property.2⟩)
  have hpair : ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      ((∀ u : I, (∫⁻ s in Icc u.val T, ‖Fo n u s - Fo m u s‖ₑ) < ENNReal.ofReal δ) ∧
      (∀ v : I, (∫⁻ s in Icc 0 v.val, ‖Fi n v s - Fi m v s‖ₑ) < ENNReal.ofReal δ)) := by
    intro δ hδ
    obtain ⟨N, hN⟩ := hdata (δ / C) (div_pos hδ hC)
    refine ⟨N, fun n hnN m hmN => ?_⟩
    have hb := hPair T e ε M (Sn n) (Sn m) (hn n) (hn m)
      (hset n) (hset m) hsmall (hmain n m)
    have hc : C * dataDist (hn n) (hn m) T < δ := by
      simpa only [mul_comm] using (lt_div_iff₀ hC).mp (hN n hnN m hmN)
    have he := (ENNReal.ofReal_lt_ofReal_iff hδ).mpr hc
    constructor
    · intro u
      rw [show (fun s => ‖Fo n u s - Fo m u s‖ₑ) =
        (fun s => ENNReal.ofReal |Fo n u s - Fo m u s|) from by
          funext s; rw [← ofReal_norm, Real.norm_eq_abs]]
      exact ((le_iSup₂_of_le u.val u.property le_rfl).trans
        ((le_add_of_nonneg_right bot_le).trans hb)).trans_lt he
    · intro v
      rw [show (fun s => ‖Fi n v s - Fi m v s‖ₑ) =
        (fun s => ENNReal.ofReal |Fi n v s - Fi m v s|) from by
          funext s; rw [← ofReal_norm, Real.norm_eq_abs]]
      exact ((le_iSup₂_of_le v.val v.property le_rfl).trans
        ((le_add_of_nonneg_left bot_le).trans hb)).trans_lt he
  obtain ⟨qo, hqo, hlo⟩ := stab_family_L1_limit_of_uniform_cauchy hFo (by
    intro δ hδ
    obtain ⟨N, hN⟩ := hpair δ hδ
    exact ⟨N, fun n hn m hm => (hN n hn m hm).1⟩)
  obtain ⟨qi, hqi, hli⟩ := stab_family_L1_limit_of_uniform_cauchy hFi (by
    intro δ hδ
    obtain ⟨N, hN⟩ := hpair δ hδ
    exact ⟨N, fun n hn m hm => (hN n hn m hm).2⟩)
  refine ⟨qo, qi, hqo, hqi, ?_⟩
  intro δ hδ
  obtain ⟨No, hNo⟩ := hlo δ hδ
  obtain ⟨Ni, hNi⟩ := hli δ hδ
  exact ⟨max No Ni, fun n hn =>
    ⟨hNo n ((le_max_left _ _).trans hn), hNi n ((le_max_right _ _).trans hn)⟩⟩

end EmcsfAcExtension.Local
