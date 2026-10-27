module

public import EmcsfAcExtension.Local.Stability.PotentialSource
public import EmcsfAcExtension.Local.Defs.Bounds
import EmcsfAcExtension.Local.Stability.PotentialArea
import EmcsfAcExtension.Local.Stability.PotentialSourcePoint
import EmcsfAcExtension.Local.Stability.PotentialHardyArea
import EmcsfAcExtension.Local.Stability.PotentialTriangle
import EmcsfAcExtension.Local.Stability.GeomStrongIndividualEnvelope
import EmcsfAcExtension.Local.Stability.GeomStrongRegularity
import EmcsfAcExtension.Local.Stability.MomentsSections

/-! # Closing the incoming potential source in area norm

The six A11p terms are integrated against their own positive budgets.
Cubic charge Hardy control and incoming scalar-ratio area control are
used before any uniform field distance replaces a local difference.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem scaled_area_aux {F : ℝ × ℝ → ℝ≥0∞} {T b B D : ℝ}
    (hb : 0 ≤ b) (h : (∫⁻ p in triangle 0 T, F p) ≤ ENNReal.ofReal B)
    (hD : b * B ≤ D) :
    (∫⁻ p in triangle 0 T, ENNReal.ofReal b * F p) ≤ ENNReal.ofReal D := by
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply (mul_le_mul' le_rfl h).trans
  rw [← ENNReal.ofReal_mul hb]
  exact ENNReal.ofReal_le_ofReal hD

/-- The true continuous incoming potential-source representatives have
area difference `K |e| M T Δ₀`. The positive constant `K` depends only
on the envelope constant `A` and the extended-record constant `C`, fixed
before fields, data, time, coupling and background. It is uniform in
minimum radii and all higher derivative suprema. The conclusion record
is assumed only in this explicitly named `_of_stab_bounds` helper. -/
theorem stab_potential_source_area_of_stab_bounds_c1
    (A C : ℝ) (hA : 0 < A) (hC : 0 < C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ)
      (H₁ H₂ : ℝ → ℝ → ℝ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      ε ^ 2 + sigma e M T ≤ 1 / 4 → StabBounds C e T M (dataDist h₁ h₂ T) S₁ S₂ →
      (∀ u v, 0 ≤ u → u < v → v ≤ T → H₁ u v = potentialIncomingSource e (triangle 0 T) S₁ u v) →
      (∀ u v, 0 ≤ u → u < v → v ≤ T → H₂ u v = potentialIncomingSource e (triangle 0 T) S₂ u v) →
      (∫⁻ p in triangle 0 T, ‖H₁ p.1 p.2 - H₂ p.1 p.2‖ₑ) ≤
        ENNReal.ofReal (K * |e| * M * T * dataDist h₁ h₂ T) := by
  obtain ⟨Kq, hKq, hQdiff⟩ := stab_charge_cubic_difference_area_of_stab_bounds_c1 A C hA hC
  let Ci := 512 * A + 3 * (4096 * A ^ 2 + 800)
  let K := 40 * C + 384 * C * Ci + 16 * Kq + 29184 * C * A
  refine ⟨K, by dsimp only [K, Ci]; positivity, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ H₁ H₂ h₁s h₂s hsmall hb heq₁ heq₂
  let Δ := dataDist h₁ h₂ T
  let E := |e| * M
  let dN := fun u v => geomN (triangle 0 T) S₁ u v - geomN (triangle 0 T) S₂ u v
  let N₂ := geomN (triangle 0 T) S₂
  let qd := fun p : ℝ × ℝ => |S₁.Q p.1 p.2 - S₂.Q p.1 p.2| / S₁.r p.1 p.2 ^ 3
  let q₂ := fun p : ℝ × ℝ => |S₂.Q p.1 p.2| / S₂.r p.1 p.2 ^ 3
  let xd := fun p : ℝ × ℝ => ‖S₁.xi p.1 p.2 / (S₁.nu p.1 p.2 : ℂ) -
    S₂.xi p.1 p.2 / (S₂.nu p.1 p.2 : ℂ)‖ / (p.2 - p.1)
  let x₂ := fun p : ℝ × ℝ => ‖S₂.xi p.1 p.2 / (S₂.nu p.1 p.2 : ℂ)‖ / (p.2 - p.1)
  have hΔ : 0 ≤ Δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans h₁s.box.1
  have hE : 0 ≤ E := mul_nonneg (abs_nonneg _) hM
  have hT : 0 ≤ T := h₁s.pos.le
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, hT⟩).2.2.2.2.2.1)
  have hσ0 : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hεsq : ε ^ 2 ≤ 1 / 4 := by linarith only [hsmall, hσ0]
  have hσ : sigma e M T ≤ 1 := by linarith only [hsmall, sq_nonneg ε]
  have hε1 : ε ≤ 1 := by nlinarith only [hεsq, sq_nonneg (ε - 1)]
  have hεsq1 : ε ^ 2 ≤ 1 := hεsq.trans (by norm_num)
  have hCi : 0 ≤ Ci := by dsimp only [Ci]; positivity
  have cN₁ := stab_geomN_continuous_c1 h₁s
  have cN₂ := stab_geomN_continuous_c1 h₂s
  have cdN : ContinuousOn (Function.uncurry dN) (triangle 0 T) := by
    simpa only [Function.uncurry_def, Pi.sub_apply, dN] using! cN₁.sub cN₂
  have hdN : (∫⁻ p in triangle 0 T, ‖dN p.1 p.2‖ₑ) ≤ ENNReal.ofReal (C * T * Δ) := by
    apply (stab_triangle_norm_area_le_incoming_envelope hT cdN).trans
    apply (mul_le_mul' le_rfl ((le_add_of_nonneg_left bot_le).trans hb.geomEnvDiff)).trans_eq
    rw [← ENNReal.ofReal_mul hT]
    congr 1
    ring
  have hN₂ : (∫⁻ p in triangle 0 T, ‖N₂ p.1 p.2‖ₑ) ≤ ENNReal.ofReal (Ci * T * ε ^ 2) := by
    apply (stab_triangle_norm_area_le_incoming_envelope hT cN₂).trans
    apply (mul_le_mul' le_rfl ((le_add_of_nonneg_left bot_le).trans
      (stab_geometric_envelope_budget_c1 h₂s hA.le hεsq hσ))).trans_eq
    rw [← ENNReal.ofReal_mul hT]
    congr 1
    ring
  have hqd : (∫⁻ p in triangle 0 T, ENNReal.ofReal (qd p)) ≤ ENNReal.ofReal (Kq * E * T * Δ) := by
    simpa only [qd, E, mul_assoc] using! hQdiff T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hεsq hb
  have hq₂ : (∫⁻ p in triangle 0 T, ENNReal.ofReal (q₂ p)) ≤ ENNReal.ofReal (16 * A * E * T * ε) :=
      by
    simpa only [q₂, E, mul_assoc] using! stab_charge_cubic_area_le_c1 h₂s hA.le hεsq
  have hxd : (∫⁻ p in triangle 0 T, ENNReal.ofReal (xd p)) ≤ ENNReal.ofReal (C * T * Δ) :=
      hb.xiRatioArea
  have hx₂ : (∫⁻ p in triangle 0 T, ENNReal.ofReal (x₂ p)) ≤ ENNReal.ofReal (32 * A * T * ε) := by
    have henv := (le_add_of_nonneg_left bot_le).trans h₂s.env
    apply ((Stab.potential_incoming_triangle_bound h₂s hεsq (v := T) ⟨hT, le_rfl⟩).trans
      (mul_le_mul' le_rfl henv)).trans
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hn : 0 ≤ A * T * ε := by positivity
    nlinarith only [hn]
  have h₁ := scaled_area_aux (b := 8 * E * ε) (by positivity) hdN
    (D := 8 * C * E * T * Δ) (by calc
      _ ≤ (8 * E * 1) * (C * T * Δ) := by gcongr
      _ = _ := by ring)
  have h₂ := scaled_area_aux (b := 384 * C * E * Δ) (by positivity) hN₂
    (D := 384 * C * Ci * E * T * Δ) (by calc
      _ ≤ (384 * C * E * Δ) * (Ci * T * 1) := by gcongr
      _ = _ := by ring)
  have h₃ := scaled_area_aux (b := 16) (by norm_num) hqd
    (D := 16 * Kq * E * T * Δ) (by ring_nf; exact le_rfl)
  have h₄ := scaled_area_aux (b := 864 * C * Δ) (by positivity) hq₂
    (D := 13824 * C * A * E * T * Δ) (by calc
      _ ≤ (864 * C * Δ) * (16 * A * E * T * 1) := by gcongr
      _ = _ := by ring)
  have h₅ := scaled_area_aux (b := 32 * E) (by positivity) hxd
    (D := 32 * C * E * T * Δ) (by ring_nf; exact le_rfl)
  have h₆ := scaled_area_aux (b := 480 * C * E * Δ) (by positivity) hx₂
    (D := 15360 * C * A * E * T * Δ) (by calc
      _ ≤ (480 * C * E * Δ) * (32 * A * T * 1) := by gcongr
      _ = _ := by ring)
  have aQ₁ := h₁s.c1.c1_Q.continuousOn.aemeasurable (μ := volume) (measurableSet_triangle 0 T)
  have aQ₂ := h₂s.c1.c1_Q.continuousOn.aemeasurable (μ := volume) (measurableSet_triangle 0 T)
  have aR₁ := h₁s.c1.c1_r.continuousOn.aemeasurable (μ := volume) (measurableSet_triangle 0 T)
  have aR₂ := h₂s.c1.c1_r.continuousOn.aemeasurable (μ := volume) (measurableSet_triangle 0 T)
  have aqd : AEMeasurable (fun p => ENNReal.ofReal (qd p)) (volume.restrict (triangle 0 T)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((aQ₁.sub aQ₂).abs.div (aR₁.pow_const 3))
  have aq₂ : AEMeasurable (fun p => ENNReal.ofReal (q₂ p)) (volume.restrict (triangle 0 T)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (aQ₂.abs.div (aR₂.pow_const 3))
  have axd : AEMeasurable (fun p => ENNReal.ofReal (xd p)) (volume.restrict (triangle 0 T)) := by
    have ay₁ := (stab_in_ratio_c1 h₁s.c1).continuousOn.aemeasurable (μ := volume)
        (measurableSet_triangle 0 T)
    have ay₂ := (stab_in_ratio_c1 h₂s.c1).continuousOn.aemeasurable (μ := volume)
        (measurableSet_triangle 0 T)
    exact ENNReal.measurable_ofReal.comp_aemeasurable ((ay₁.sub ay₂).norm.div
      (measurable_snd.sub measurable_fst).aemeasurable.restrict)
  have m₁ := (aemeasurable_const (b := ENNReal.ofReal (8 * E * ε))).mul
    (cdN.enorm.aemeasurable (μ := volume) (measurableSet_triangle 0 T))
  have m₂ := (aemeasurable_const (b := ENNReal.ofReal (384 * C * E * Δ))).mul
    (cN₂.enorm.aemeasurable (μ := volume) (measurableSet_triangle 0 T))
  have hp : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)).restrict (triangle 0 T),
      ‖H₁ p.1 p.2 - H₂ p.1 p.2‖ₑ ≤
        ENNReal.ofReal (8 * E * ε) * ‖dN p.1 p.2‖ₑ +
        ENNReal.ofReal (384 * C * E * Δ) * ‖N₂ p.1 p.2‖ₑ +
        ENNReal.ofReal 16 * ENNReal.ofReal (qd p) +
        ENNReal.ofReal (864 * C * Δ) * ENNReal.ofReal (q₂ p) +
        ENNReal.ofReal (32 * E) * ENNReal.ofReal (xd p) +
        ENNReal.ofReal (480 * C * E * Δ) * ENNReal.ofReal (x₂ p) := by
    filter_upwards [ae_restrict_mem (measurableSet_triangle 0 T), stab_triangle_ae_off_axis T] with
        p hp hoff
    have hr₁ := (h₁s.c1.r_pos p hp hoff).le
    have hr₂ := (h₂s.c1.r_pos p hp hoff).le
    rw [← ofReal_norm, Real.norm_eq_abs, heq₁ p.1 p.2 hp.1 hoff hp.2.2,
      heq₂ p.1 p.2 hp.1 hoff hp.2.2]
    have hh := stab_six_positive_ofReal_le (by positivity : 0 ≤ 8 * E * ε)
      (by positivity : 0 ≤ 384 * C * E * Δ) (by norm_num : (0 : ℝ) ≤ 16)
      (by positivity : 0 ≤ 864 * C * Δ) (by positivity : 0 ≤ 32 * E)
      (by positivity : 0 ≤ 480 * C * E * Δ)
      (abs_nonneg _) (abs_nonneg _)
      (div_nonneg (abs_nonneg _) (pow_nonneg hr₁ 3))
      (div_nonneg (abs_nonneg _) (pow_nonneg hr₂ 3))
      (div_nonneg (norm_nonneg _) (sub_nonneg.mpr hoff.le))
      (div_nonneg (norm_nonneg _) (sub_nonneg.mpr hoff.le))
      (stab_potential_source_sub_le_of_stab_bounds_c1 hC h₁s h₂s hε1 hb hp.1 hoff hp.2.2)
    simpa only [← Real.norm_eq_abs, ofReal_norm, dN, N₂, E, Δ, qd, q₂, xd, x₂] using! hh
  apply (stab_six_lintegral_le_of_majorants m₁ m₂ (aemeasurable_const.mul aqd)
    (aemeasurable_const.mul aq₂) (aemeasurable_const.mul axd) hp h₁ h₂ h₃ h₄ h₅ h₆).trans_eq
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  dsimp only [K, E]
  ring

end EmcsfAcExtension.Local
