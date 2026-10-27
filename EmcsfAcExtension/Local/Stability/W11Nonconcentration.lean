module

public import EmcsfAcExtension.Local.Stability.W11FluxLocal
public import EmcsfAcExtension.Local.Stability.W11EnvelopeUI
import EmcsfAcExtension.Local.Stability.MomentsFieldMeasurable
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Uniform quadratic-flux nonconcentration at the axis

Local Hardy estimates retain the actual short interval. Uniform
integrability of the mixed Cauchy envelopes makes their right sides
small uniformly over the approximation index and both section labels.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace EmcsfAcExtension.Local

private theorem ui_small_interval_aux {T : ℝ} {E : ℕ → ℝ → ℝ≥0∞}
    (hE : ∀ n, AEMeasurable (E n) (volume.restrict (Icc 0 T)))
    (hfin : ∀ n x, x ∈ Icc 0 T → E n x ≠ ⊤)
    (hui : UnifIntegrable (fun n x => (E n x).toReal) 1 (volume.restrict (Icc 0 T)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ ∀ n u v, 0 ≤ u → u ≤ v → v ≤ T → v - u ≤ d →
      (∫⁻ s in Icc u v, E n s) ≤ ENNReal.ofReal ε := by
  obtain ⟨θ, hθ, hbound⟩ := (unifIntegrable_iff.mp hui)
    (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
  obtain ⟨d, _, hd, hdθ⟩ := ENNReal.lt_iff_exists_real_btwn.mp hθ
  refine ⟨d, ENNReal.ofReal_pos.mp hd, ?_⟩
  intro n u v hu huv hvT hgap
  have hsub : Icc u v ⊆ Icc (0 : ℝ) T := Icc_subset_Icc hu hvT
  have hmeasure : (volume.restrict (Icc (0 : ℝ) T)) (Icc u v) ≤ θ := by
    calc
      _ ≤ volume (Icc u v) := Measure.restrict_le_self _
      _ = ENNReal.ofReal (v - u) := Real.volume_Icc
      _ ≤ ENNReal.ofReal d := ENNReal.ofReal_le_ofReal hgap
      _ ≤ θ := hdθ.le
  have hh := hbound n (Icc u v) hmeasure
  rw [eLpNorm_one_eq_lintegral_enorm ((hE n).ennreal_toReal.aestronglyMeasurable).restrict,
    Measure.restrict_restrict_of_subset hsub] at hh
  apply le_trans ?_ hh
  apply le_of_eq
  apply setLIntegral_congr_fun measurableSet_Icc
  intro s hs
  dsimp only
  rw [Real.enorm_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hfin n s (hsub hs))]

/-- [internal]
The weighted outgoing and incoming quadratic fluxes are uniformly
nonconcentrating at their regular-axis endpoints when the classical
mixed-envelope differences are Cauchy. The same positive width works
for the entire sequence and both orientations. No derivative supremum
or minimum radius enters the estimate. This is the local C¹ form of
`restart-sec-bv-stability-independent#quadratic-flux-nonconcentration`. -/
theorem Stab.quadratic_flux_nonconcentration_of_mixed_cauchy_c1
    {e T ε M A : ℝ} {Sn : ℕ → Fields} {hn : ℕ → ℝ → ℂ}
    (hset : ∀ n, StabSetting e T ε M A (Sn n) (hn n))
    (hε : ε ^ 2 ≤ 1 / 4)
    (hj : ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      jDist T (Sn n) (Sn m) < ENNReal.ofReal δ)
    (hk : ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      kDist e T (Sn n) (Sn m) < ENNReal.ofReal δ) :
    ∀ δ > (0 : ℝ), ∃ d : ℝ, 0 < d ∧
      ∀ n u v, 0 ≤ u → u ≤ v → v ≤ T → v - u ≤ d →
        (∫⁻ s in Icc u v, ENNReal.ofReal
          ((Sn n).lam u s / (Sn n).r u s *
            ‖(Sn n).theta u s / ((Sn n).lam u s : ℂ)‖ ^ 2)) +
        (∫⁻ s in Icc u v, ENNReal.ofReal
          (-(Sn n).nu s v / (Sn n).r s v *
            ‖(Sn n).xi s v / ((Sn n).nu s v : ℂ)‖ ^ 2)) ≤ ENNReal.ofReal δ := by
  have hT := (hset 0).pos
  have hUiJ := stab_out_envelope_uniform_integrability_c1 hT (fun n => (hset n).c1) hj
  have hUiK := stab_in_envelope_uniform_integrability_c1 hT (fun n => (hset n).c1) hk
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg ((Sn 0).xi 0 0 / ((Sn 0).nu 0 0 : ℂ)))).trans
      ((hset 0).box.2 (0, 0) ⟨le_rfl, le_rfl, hT.le⟩).2.2.2.2.2.1)
  have hε1 : ε ≤ 1 := by nlinarith only [hε, sq_nonneg (ε - 1)]
  intro δ hδ
  obtain ⟨dj, hdj, hJ⟩ := ui_small_interval_aux
    (fun n => stab_outEnv_aemeasurable (hset n))
    (fun n _ hv => outEnv_ne_top_of_continuousOn (continuousOn_jC1_aux hT (hset n).c1) hv)
    hUiJ (show 0 < δ / 16 by positivity)
  obtain ⟨dk, hdk, hK⟩ := ui_small_interval_aux
    (fun n => stab_inEnv_aemeasurable (hset n))
    (fun n _ hu => inEnv_ne_top_of_continuousOn (continuousOn_kC1_aux hT (hset n).c1) hu)
    hUiK (show 0 < δ / 16 by positivity)
  refine ⟨min dj dk, lt_min hdj hdk, ?_⟩
  intro n u v hu huv hvT hgap
  have hout := Stab.quadratic_flux_out_local_c1 (hset n) hε hu huv hvT
  have hin := Stab.quadratic_flux_in_local_c1 (hset n) hε hu huv hvT
  have hJb := hJ n u v hu huv hvT (hgap.trans (min_le_left _ _))
  have hKb := hK n u v hu huv hvT (hgap.trans (min_le_right _ _))
  have hco : ENNReal.ofReal ((16 / 3) * ε) ≤ ENNReal.ofReal (16 / 3 : ℝ) :=
    ENNReal.ofReal_le_ofReal (by linarith only [hε1])
  apply ((add_le_add hout hin).trans
    (add_le_add (mul_le_mul' hco hJb) (mul_le_mul' hco hKb))).trans
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16 / 3),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  linarith only [hδ]

/-- [internal]
The quadratic nonconcentration conclusion under Cauchy normalized data
and the explicit main Lipschitz record from internal project record. No envelope
uniform-integrability conclusion is assumed. The main constant `C₀`
is fixed before all data and solutions; the width is uniform over the
entire sequence and both characteristic families. -/
theorem Stab.quadratic_flux_nonconcentration_of_main_lipschitz
    (C₀ : ℝ) (hC₀ : 0 < C₀)
    {e T ε M A : ℝ} {Sn : ℕ → Fields} {hn : ℕ → ℝ → ℂ}
    (hset : ∀ n, StabSetting e T ε M A (Sn n) (hn n))
    (hε : ε ^ 2 ≤ 1 / 4)
    (hdata : ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      dataDist (hn n) (hn m) T < δ)
    (hmain : ∀ n m, jDist T (Sn n) (Sn m) + kDist e T (Sn n) (Sn m) +
      geomDist T (Sn n) (Sn m) ≤ ENNReal.ofReal (C₀ * dataDist (hn n) (hn m) T)) :
    ∀ δ > (0 : ℝ), ∃ d : ℝ, 0 < d ∧
      ∀ n u v, 0 ≤ u → u ≤ v → v ≤ T → v - u ≤ d →
        (∫⁻ s in Icc u v, ENNReal.ofReal
          ((Sn n).lam u s / (Sn n).r u s *
            ‖(Sn n).theta u s / ((Sn n).lam u s : ℂ)‖ ^ 2)) +
        (∫⁻ s in Icc u v, ENNReal.ofReal
          (-(Sn n).nu s v / (Sn n).r s v *
            ‖(Sn n).xi s v / ((Sn n).nu s v : ℂ)‖ ^ 2)) ≤ ENNReal.ofReal δ := by
  have hJK : ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      jDist T (Sn n) (Sn m) < ENNReal.ofReal δ ∧
      kDist e T (Sn n) (Sn m) < ENNReal.ofReal δ := by
    intro δ hδ
    obtain ⟨N, hN⟩ := hdata (δ / C₀) (div_pos hδ hC₀)
    refine ⟨N, fun n hnN m hmN => ?_⟩
    have hb : C₀ * dataDist (hn n) (hn m) T < δ := by
      have hh := (lt_div_iff₀ hC₀).mp (hN n hnN m hmN)
      simpa only [mul_comm] using hh
    have he : ENNReal.ofReal (C₀ * dataDist (hn n) (hn m) T) < ENNReal.ofReal δ :=
      (ENNReal.ofReal_lt_ofReal_iff hδ).mpr hb
    have hj : jDist T (Sn n) (Sn m) ≤
        jDist T (Sn n) (Sn m) + kDist e T (Sn n) (Sn m) + geomDist T (Sn n) (Sn m) :=
      (le_add_of_nonneg_right bot_le).trans (le_add_of_nonneg_right bot_le)
    have hk : kDist e T (Sn n) (Sn m) ≤
        jDist T (Sn n) (Sn m) + kDist e T (Sn n) (Sn m) + geomDist T (Sn n) (Sn m) :=
      (le_add_of_nonneg_left bot_le).trans (le_add_of_nonneg_right bot_le)
    exact ⟨(hj.trans (hmain n m)).trans_lt he, (hk.trans (hmain n m)).trans_lt he⟩
  apply Stab.quadratic_flux_nonconcentration_of_mixed_cauchy_c1 hset hε
  · intro δ hδ
    obtain ⟨N, hN⟩ := hJK δ hδ
    exact ⟨N, fun n hn m hm => (hN n hn m hm).1⟩
  · intro δ hδ
    obtain ⟨N, hN⟩ := hJK δ hδ
    exact ⟨N, fun n hn m hm => (hN n hn m hm).2⟩

end EmcsfAcExtension.Local
