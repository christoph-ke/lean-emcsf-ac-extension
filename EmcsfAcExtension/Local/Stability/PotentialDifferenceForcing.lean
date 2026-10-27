module

public import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux
import EmcsfAcExtension.Local.Stability.PotentialDifferenceAlgebra
import EmcsfAcExtension.Local.Stability.ChargeDifferenceIndividual
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Difference of the potential constraint densities

The conditional charge input is pointwise and is discharged by the
closed charge node in the potential comparison. No conclusion bundle
or assumed geometric comparison is used.
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- A pointwise normalized charge comparison bounds the potential
partial difference with coefficient `128`, universal in all parameters,
the pair and minimum radius. The mass feedback remains explicit. -/
theorem stab_potential_partial_sub_le_of_charge
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂)
    {u v D : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T)
    (hD : |S₁.Q u v - S₂.Q u v| / S₁.r u v ^ 2 ≤ D) :
    |pdV (triangle 0 T) S₁.A u v - pdV (triangle 0 T) S₂.A u v| ≤
      128 * (D + (|e| * M * ε) *
        ((geomDist T S₁ S₂).toReal + (supDist T S₁.mu S₂.mu).toReal)) := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  let B₁ := 2 * S₁.nu u v * S₁.lam u v / (1 - S₁.mu u v)
  let B₂ := 2 * S₂.nu u v * S₂.lam u v / (1 - S₂.mu u v)
  have hr₁ := h₁s.c1.r_pos (u, v) hp huv
  have hr₂ := h₂s.c1.r_pos (u, v) hp huv
  have hg₁ := h₁s.c1.one_sub_mu_pos (u, v) hp
  have hg₂ := h₂s.c1.one_sub_mu_pos (u, v) hp
  have hl₁ : |S₁.lam u v| ≤ 1 := by
    rw [abs_of_pos (h₁s.c1.lam_pos (u, v) hp)]
    exact (h₁s.box.2 (u, v) hp).2.1
  have hl₂ : |S₂.lam u v| ≤ 1 := by
    rw [abs_of_pos (h₂s.c1.lam_pos (u, v) hp)]
    exact (h₂s.box.2 (u, v) hp).2.1
  have hn₁ : |S₁.nu u v| ≤ 1 := by
    rw [abs_of_neg (h₁s.c1.nu_neg (u, v) hp)]
    exact (h₁s.box.2 (u, v) hp).2.2.2.1
  have hn₂ : |S₂.nu u v| ≤ 1 := by
    rw [abs_of_neg (h₂s.c1.nu_neg (u, v) hp)]
    exact (h₂s.box.2 (u, v) hp).2.2.2.1
  have hgeom := stab_geom_sum_le h₁s h₂s hp
  have hrr0 := div_nonneg (abs_nonneg (S₁.r u v - S₂.r u v)) hr₁.le
  have hsum : |S₁.nu u v - S₂.nu u v| + |S₁.lam u v - S₂.lam u v| ≤
      (geomDist T S₁ S₂).toReal := by linarith only [hgeom, hrr0]
  have hrr : |S₁.r u v - S₂.r u v| / S₁.r u v ≤ (geomDist T S₁ S₂).toReal := by
    linarith only [hgeom, abs_nonneg (S₁.lam u v - S₂.lam u v),
      abs_nonneg (S₁.nu u v - S₂.nu u v)]
  have hB₁ : |B₁| ≤ 8 := stab_potential_coefficient_abs_le hn₁ hl₁
    (h₁s.box.2 (u, v) hp).2.2.2.2.1
  have hB : |B₁ - B₂| ≤
      40 * ((geomDist T S₁ S₂).toReal + (supDist T S₁.mu S₂.mu).toReal) :=
    stab_potential_coefficient_sub_le hl₁ hl₂ hn₂
      (h₁s.box.2 (u, v) hp).2.2.2.2.1 (h₂s.box.2 (u, v) hp).2.2.2.2.1
      hsum (stab_mu_sub_le h₁s h₂s hp)
  have hAV₁ : pdV (triangle 0 T) S₁.A u v = B₁ * (S₁.Q u v / S₁.r u v ^ 2) := by
    rw [(h₁s.c1.eq_v (u, v) hp huv).2.2.2.2.1, Fields.AV]
    dsimp only [B₁]
    field_simp
  have hAV₂ : pdV (triangle 0 T) S₂.A u v = B₂ * (S₂.Q u v / S₂.r u v ^ 2) := by
    rw [(h₂s.c1.eq_v (u, v) hp huv).2.2.2.2.1, Fields.AV]
    dsimp only [B₂]
    field_simp
  rw [hAV₁, hAV₂]
  exact stab_potential_density_sub_le hr₁ hr₂ (stab_radius_compare h₁s h₂s hu huv.le hvT).2
    hrr ENNReal.toReal_nonneg hD (stab_charge_ratio_le h₂s hu huv hvT) hB₁ hB

end EmcsfAcExtension.Local
