module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Defs.Bounds
import EmcsfAcExtension.Local.Stability.PotentialDifferenceForcing
import EmcsfAcExtension.Local.Stability.PotentialC1

/-! # Uniform factors in the incoming potential source

Only already proved fields of the extended pair record are projected.
The explicit background and time factors remain outside constants.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The geometric, mass and scalar uniform real distances are bounded
by the record's own `CΔ₀`. This algebraic projection has universal
coefficient one and assumes a conclusion record only as an `_of_` helper.
-/
theorem stab_real_distances_of_stab_bounds
    {C e T M Δ₀ : ℝ} {S₁ S₂ : Fields} (hCΔ : 0 ≤ C * Δ₀)
    (hb : StabBounds C e T M Δ₀ S₁ S₂) :
    (geomDist T S₁ S₂).toReal ≤ C * Δ₀ ∧
      (supDist T S₁.mu S₂.mu).toReal ≤ C * Δ₀ ∧
      (supDist T S₁.phi S₂.phi).toReal ≤ C * Δ₀ := by
  have rb {X : ℝ≥0∞} (hX : X ≤ ENNReal.ofReal (C * Δ₀)) : X.toReal ≤ C * Δ₀ := by
    simpa only [ENNReal.toReal_ofReal hCΔ] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hX
  have hmain3 : jDist T S₁ S₂ + kDist e T S₁ S₂ + geomDist T S₁ S₂ ≤ ENNReal.ofReal (C * Δ₀) :=
    (le_add_of_nonneg_right bot_le).trans ((le_add_of_nonneg_right bot_le).trans
      ((le_add_of_nonneg_right bot_le).trans hb.main))
  exact ⟨rb ((le_add_of_nonneg_left bot_le).trans hmain3), rb hb.extra_mu,
    rb ((le_add_of_nonneg_left bot_le).trans hb.main)⟩

/-- The scalar pointwise difference is bounded by the record's `CΔ₀`,
with universal coefficient one and no continuity premise. -/
theorem stab_phi_sub_le_of_stab_bounds
    {C e T M Δ₀ : ℝ} {S₁ S₂ : Fields} (hCΔ : 0 ≤ C * Δ₀)
    (hb : StabBounds C e T M Δ₀ S₁ S₂) {u v : ℝ} (hp : (u, v) ∈ triangle 0 T) :
    ‖S₁.phi u v - S₂.phi u v‖ ≤ C * Δ₀ := by
  have hh : ENNReal.ofReal ‖S₁.phi u v - S₂.phi u v‖ ≤ ENNReal.ofReal (C * Δ₀) := by
    rw [ofReal_norm]
    exact (le_iSup₂_of_le (u, v) hp le_rfl).trans
      ((le_add_of_nonneg_left bot_le).trans hb.main)
  exact (ENNReal.ofReal_le_ofReal_iff hCΔ).mp hh

/-- An individual classical potential density has bound `8|e|Mε`,
with universal coefficient eight, uniformly in all fields, data,
derivative bounds and minimum radii. -/
theorem stab_potential_constraint_abs_le_c1
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    |S.AV u v| ≤ 8 * |e| * M * ε := by
  have hh := stab_potential_partial_le_c1 hset hu huv hvT
  rwa [(hset.c1.eq_v (u, v) ⟨hu, huv.le, hvT⟩ huv).2.2.2.2.1] at hh

/-- The potential density difference has bound `384 C |e|MΔ₀` from
an extended pair record. The literal coefficient is universal; `C`
is fixed before all field, coupling, scale, background and data inputs.
No minimum-radius or higher-derivative bound enters. -/
theorem stab_potential_constraint_sub_le_of_stab_bounds_c1
    {C e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (hC : 0 < C) (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hε : ε ≤ 1)
    (hb : StabBounds C e T M (dataDist h₁ h₂ T) S₁ S₂)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    |S₁.AV u v - S₂.AV u v| ≤ 384 * C * |e| * M * dataDist h₁ h₂ T := by
  let Δ := dataDist h₁ h₂ T
  have hΔ : 0 ≤ Δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans h₁s.box.1
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi u v / (S₂.nu u v : ℂ)))).trans
      (h₂s.box.2 (u, v) hp).2.2.2.2.2.1)
  obtain ⟨hG, hU, hΦ⟩ := stab_real_distances_of_stab_bounds (mul_nonneg hC.le hΔ) hb
  have hh := stab_potential_partial_sub_le_of_charge h₁s h₂s hu huv hvT (hb.extra_Q (u, v) hp huv)
  rw [(h₁s.c1.eq_v (u, v) hp huv).2.2.2.2.1,
    (h₂s.c1.eq_v (u, v) hp huv).2.2.2.2.1] at hh
  apply hh.trans
  calc
    _ ≤ 128 * (C * |e| * M * Δ + (|e| * M * 1) * (C * Δ + C * Δ)) := by gcongr
    _ = _ := by ring

end EmcsfAcExtension.Local
