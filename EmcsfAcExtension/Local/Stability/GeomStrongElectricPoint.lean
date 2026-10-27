module

public import EmcsfAcExtension.Local.Stability.GeomStrongElectricSource

/-! # Nonsingular electric geometric-source comparison

The cubic primitive cost and the explicit charge-square error are
combined before the time area is used to produce the charged scale.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

private theorem electric_budget_aux {a b c d f : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hf : 0 ≤ f) :
    (512 * (3 * a + b + 11 * c + d) + 8192 * (c + f)) / 3 +
      (32 * a + 80 * (c + f)) ≤ 20000 * (a + b + c + d + f) := by
  linarith only [ha, hb, hc, hd, hf]

/-- The electric geometric-source difference has a nonsingular local
bound with universal coefficient `20000`. Every local input error and
the finite uniform mass/geometric feedback remain explicit. The
coefficient is uniform in fields, scales and minimum radii. -/
theorem stab_geometric_electric_source_sub_le_c1
    {e T ε M A D X Φ : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T)
    (hD : 0 ≤ D) (hX : 0 ≤ X) (hΦ : 0 ≤ Φ)
    (hq : ∀ t ∈ Ioc u v,
      |S₁.Q u t / S₁.r u t ^ 2 - S₂.Q u t / S₂.r u t ^ 2| ≤ |e| * M * D)
    (hθ : ∀ t ∈ Ioc u v, ‖S₁.theta u t - S₂.theta u t‖ ≤ X)
    (hφ : ∀ t ∈ Ioc u v, ‖S₁.phi u t - S₂.phi u t‖ ≤ Φ) :
    ‖geometricElectricSource e S₁ u v - geometricElectricSource e S₂ u v‖ ≤
      20000 * (|e| * M) ^ 2 *
        (ε * D + ε * X + ε ^ 2 * ((geomDist T S₁ S₂).toReal +
          (supDist T S₁.mu S₂.mu).toReal + Φ)) := by
  let G := (geomDist T S₁ S₂).toReal
  let U := (supDist T S₁.mu S₂.mu).toReal
  let W (S : Fields) : ℂ := (2 * S.nu u v * S.lam u v /
    ((1 - S.mu u v) * S.r u v ^ 3) : ℝ)
  let P (S : Fields) : ℂ := W S * ∫ t in u..v, electricCurvatureIntegrand e S u t
  let Q (S : Fields) : ℝ := 2 * (2 * S.nu u v * S.lam u v / (1 - S.mu u v)) *
    (S.Q u v / S.r u v ^ 2) ^ 2
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi u v / (S₂.nu u v : ℂ)))).trans
      (h₂s.box.2 (u, v) hp).2.2.2.2.2.1)
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hU : 0 ≤ U := ENNReal.toReal_nonneg
  have hP := stab_geometric_electric_primitive_sub_le_c1 h₁s h₂s hu huv hvT hD hX hΦ hq hθ hφ
  have hQ := stab_electric_charge_square_sub_le_c1 h₁s h₂s hu huv hvT hD (hq v ⟨huv, le_rfl⟩)
  have heq : geometricElectricSource e S₁ u v - geometricElectricSource e S₂ u v =
      (P S₁ - P S₂) - ((Q S₁ - Q S₂ : ℝ) : ℂ) := by
    simp only [geometricElectricSource, P, W, Q, Complex.ofReal_sub]
    ring
  rw [heq]
  calc
    _ ≤ ‖P S₁ - P S₂‖ + |Q S₁ - Q S₂| := by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using
        norm_sub_le (P S₁ - P S₂) ((Q S₁ - Q S₂ : ℝ) : ℂ)
    _ ≤ (|e| * M) ^ 2 *
        (512 * (3 * ε * D + ε * X + 11 * ε ^ 2 * G + ε ^ 2 * Φ) +
          8192 * ε ^ 2 * (G + U)) / 3 +
        (|e| * M) ^ 2 * (32 * ε * D + 80 * ε ^ 2 * (G + U)) := add_le_add hP hQ
    _ = (|e| * M) ^ 2 *
        ((512 * (3 * (ε * D) + (ε * X) + 11 * (ε ^ 2 * G) + (ε ^ 2 * Φ)) +
          8192 * (ε ^ 2 * G + ε ^ 2 * U)) / 3 +
          (32 * (ε * D) + 80 * (ε ^ 2 * G + ε ^ 2 * U))) := by ring
    _ ≤ (|e| * M) ^ 2 * (20000 * (ε * D + ε * X + ε ^ 2 * G + ε ^ 2 * Φ + ε ^ 2 * U)) :=
      mul_le_mul_of_nonneg_left (electric_budget_aux
        (mul_nonneg hε hD) (mul_nonneg hε hX) (mul_nonneg (sq_nonneg ε) hG)
        (mul_nonneg (sq_nonneg ε) hΦ) (mul_nonneg (sq_nonneg ε) hU)) (sq_nonneg _)
    _ = _ := by ring

end EmcsfAcExtension.Local
