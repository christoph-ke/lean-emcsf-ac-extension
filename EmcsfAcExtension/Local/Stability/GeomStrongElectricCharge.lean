module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.ChargeDifference
import EmcsfAcExtension.Local.Stability.ChargeDifferenceIndividual
import EmcsfAcExtension.Local.Stability.PotentialDifferenceAlgebra
import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux

/-! # Common-label normalized charge differences

The inverse-square radius error is retained and bounded relatively,
before the electric curvature primitives are compared.
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- The two own-radius normalized charges have difference
`C |e| M (Δj+εΔ₀+εG)`. The threshold and constant depend only on
`A` and the fixed box before all fields, coupling, scale and background,
uniformly in minimum radii and derivative suprema. -/
theorem stab_normalized_charge_difference_c1 (A : ℝ) (hA : 0 < A) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ T →
        |S₁.Q u v / S₁.r u v ^ 2 - S₂.Q u v / S₂.r u v ^ 2| ≤
          |e| * M * (C * ((jDist T S₁ S₂).toReal + ε * dataDist h₁ h₂ T +
            ε * (geomDist T S₁ S₂).toReal)) := by
  obtain ⟨η, Cq, hη, hCq, hCharge⟩ := stab_charge_difference A hA
  refine ⟨η, Cq + 5, hη, by positivity, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall u v hu huv hvT
  let J := (jDist T S₁ S₂).toReal
  let G := (geomDist T S₁ S₂).toReal
  let Δ := dataDist h₁ h₂ T
  let H := J + ε * Δ + ε * G
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans h₁s.box.1
  have hJ : 0 ≤ J := ENNReal.toReal_nonneg
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hΔ : 0 ≤ Δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi u v / (S₂.nu u v : ℂ)))).trans
      (h₂s.box.2 (u, v) hp).2.2.2.2.2.1)
  have hgeo := stab_geom_sum_le h₁s h₂s hp
  have hrel : |S₁.r u v - S₂.r u v| / S₁.r u v ≤ G := by
    linarith only [hgeo, abs_nonneg (S₁.lam u v - S₂.lam u v), abs_nonneg (S₁.nu u v - S₂.nu u v)]
  have hq := stab_normalized_charge_sub_le
    (q₁ := S₁.Q u v) (q₂ := S₂.Q u v)
    (h₁s.c1.r_pos (u, v) hp huv) (h₂s.c1.r_pos (u, v) hp huv)
    (stab_radius_compare h₁s h₂s hu huv.le hvT).2 hrel
  apply hq.trans
  have hc := hCharge T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall u v hu huv hvT
  have hi := stab_charge_ratio_le h₂s hu huv hvT
  calc
    _ ≤ Cq * |e| * (M * J + ε * Δ + M * ε * G) +
        5 * (|e| * M * ε) * G := add_le_add hc
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi (by norm_num)) hG)
    _ ≤ Cq * |e| * (M * J + M * (ε * Δ) + M * ε * G) +
        5 * (|e| * M * ε) * G := by
      have hh := mul_le_mul_of_nonneg_right h₁s.box.1 (mul_nonneg hε hΔ)
      have hb : M * J + ε * Δ + M * ε * G ≤
          M * J + M * (ε * Δ) + M * ε * G :=
        add_le_add (add_le_add le_rfl (by simpa only [one_mul] using hh)) le_rfl
      exact add_le_add (mul_le_mul_of_nonneg_left hb (mul_nonneg hCq.le (abs_nonneg e))) le_rfl
    _ ≤ |e| * M * ((Cq + 5) * H) := by
      apply sub_nonneg.mp
      convert (show 0 ≤ 5 * |e| * M * (J + ε * Δ) by positivity) using 1;
        dsimp only [H]; ring

end EmcsfAcExtension.Local
