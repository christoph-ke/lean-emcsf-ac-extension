module

public import EmcsfAcExtension.Local.Stability.GeomStrongElectricPoint
import EmcsfAcExtension.Local.Stability.GeomStrongElectricCharge
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMass
import EmcsfAcExtension.Local.Stability.FieldDifference
import EmcsfAcExtension.Local.Stability.DifferenceMomentsCloseOut

import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux
import EmcsfAcExtension.Local.Stability.GeomStrongElectricAlgebra

/-! # Closing the electric geometric-source comparison

Normalized charge, scalar, and mass comparisons give a nonsingular
pointwise bound. Its area factor supplies exactly the charged scale.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

private theorem electric_point_norm_aux {T B : ℝ} {f g : ℝ → ℝ → ℂ}
    (hB : 0 ≤ B) (hfg : supDist T f g ≤ ENNReal.ofReal B)
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 T) : ‖f u v - g u v‖ ≤ B := by
  have hh : ENNReal.ofReal ‖f u v - g u v‖ ≤ ENNReal.ofReal B := by
    rw [ofReal_norm]
    exact (le_iSup₂_of_le (u, v) hp le_rfl).trans hfg
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp hh

/-- The electric part of the common geometric source has a uniform
pointwise bound `C (|e|M)²(Δ₀+Δj+Δk+εG)`. The threshold and constant
depend only on `A` and the literal box, before all fields, background,
coupling, time, data, derivative suprema and minimum radii. -/
theorem stab_geometric_electric_source_difference_c1 (A : ℝ) (hA : 0 < A) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ T →
        ‖geometricElectricSource e S₁ u v - geometricElectricSource e S₂ u v‖ ≤
          C * (|e| * M) ^ 2 * (dataDist h₁ h₂ T +
            (jDist T S₁ S₂).toReal + (kDist e T S₁ S₂).toReal +
            ε * (geomDist T S₁ S₂).toReal) := by
  obtain ⟨ηq, Cq, hηq, hCq, hCharge⟩ := stab_normalized_charge_difference_c1 A hA
  obtain ⟨ηx, Cx, hηx, hCx, hRatio⟩ := stab_out_difference A hA
  obtain ⟨ηf, Cf, hηf, hCf, hField⟩ := stab_field_difference A hA
  obtain ⟨ηm, Cm, hηm, hCm, hMass⟩ := Stab.mass_volterra_difference A hA
  let C := 20000 * (Cq + Cx + Cf + 3 * Cm + 2)
  refine ⟨min ηq (min ηx (min ηf (min ηm (1 / 12)))), C,
    lt_min hηq (lt_min hηx (lt_min hηf (lt_min hηm (by norm_num)))),
    by dsimp only [C]; positivity, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall u v hu huv hvT
  let Δ := dataDist h₁ h₂ T
  let J := (jDist T S₁ S₂).toReal
  let K := (kDist e T S₁ S₂).toReal
  let G := (geomDist T S₁ S₂).toReal
  let U := (supDist T S₁.mu S₂.mu).toReal
  let H := J + ε * Δ + ε * G
  let Hbar := Δ + J + K + ε * G
  let D := Cq * H
  let X := Cx * (J + ε * G) + ε * G
  let Φ := Cf * (Δ + J + ε * G)
  have hΔ : 0 ≤ Δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hJ : 0 ≤ J := ENNReal.toReal_nonneg
  have hK : 0 ≤ K := ENNReal.toReal_nonneg
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hU0 : 0 ≤ U := ENNReal.toReal_nonneg
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hσ0 : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hs1 : ε ^ 2 + sigma e M T ≤ min ηx (min ηf (min ηm (1 / 12))) :=
    hsmall.trans (min_le_right _ _)
  have hs2 := hs1.trans (min_le_right _ _)
  have hs3 := hs2.trans (min_le_right _ _)
  have hsize := hs3.trans (min_le_right _ _)
  have hεsq : ε ^ 2 ≤ 1 := by linarith only [hsize, hσ0]
  have hσ : sigma e M T ≤ 1 := by linarith only [hsize, sq_nonneg ε]
  have hε1 : ε ≤ 1 := by nlinarith only [hεsq, sq_nonneg (ε - 1)]
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hHb : 0 ≤ Hbar := by dsimp only [Hbar]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  have hΦ : 0 ≤ Φ := by dsimp only [Φ]; positivity
  have hHG : ε * G ≤ Hbar := by dsimp only [Hbar]; linarith only [hΔ, hJ, hK]
  have hJG : J + ε * G ≤ Hbar := by dsimp only [Hbar]; linarith only [hΔ, hK]
  have hHJ : J ≤ Hbar := by dsimp only [Hbar]; linarith only [hΔ, hK, mul_nonneg hε hG]
  have hHF : Δ + J + ε * G ≤ Hbar := by dsimp only [Hbar]; linarith only [hK]
  have hHH : H ≤ Hbar := by
    have hh := mul_le_mul_of_nonneg_right hε1 hΔ
    dsimp only [H, Hbar]
    linarith only [hh, hK]
  have hm := (le_add_of_nonneg_right bot_le).trans
    (hMass T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hs3.trans (min_le_left _ _)))
  have hU : U ≤ Cm * ε * J + Cm * ε ^ 2 * G + Cm * sigma e M T * ε * H := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
    change U ≤ (ENNReal.ofReal
      (Cm * ε * J + Cm * ε ^ 2 * G + Cm * sigma e M T * ε * H)).toReal at hh
    simpa only [ENNReal.toReal_ofReal (show
      0 ≤ Cm * ε * J + Cm * ε ^ 2 * G + Cm * sigma e M T * ε * H by positivity)] using hh
  have hεG : ε ^ 2 * G ≤ Hbar := by
    calc
      _ = ε * (ε * G) := by ring
      _ ≤ 1 * Hbar := by gcongr
      _ = _ := one_mul _
  have hεU : ε ^ 2 * U ≤ 3 * Cm * Hbar := by
    calc
      _ ≤ ε ^ 2 * (Cm * ε * J + Cm * ε ^ 2 * G + Cm * sigma e M T * ε * H) :=
        mul_le_mul_of_nonneg_left hU (sq_nonneg ε)
      _ = Cm * (ε ^ 2 * ε * J) + Cm * (ε ^ 2 * (ε ^ 2 * G)) +
          Cm * (ε ^ 2 * sigma e M T * ε * H) := by ring
      _ ≤ Cm * (1 * 1 * Hbar) + Cm * (1 * Hbar) + Cm * (1 * 1 * 1 * Hbar) := by gcongr
      _ = _ := by ring
  have hb : ε * D + ε * X + ε ^ 2 * (G + U + Φ) ≤
      (Cq + Cx + Cf + 3 * Cm + 2) * Hbar := by
    have hd : ε * D ≤ Cq * Hbar := by
      dsimp only [D]
      calc
        _ = Cq * (ε * H) := by ring
        _ ≤ Cq * (1 * Hbar) := by gcongr
        _ = _ := by ring
    have hx : ε * X ≤ (Cx + 1) * Hbar := by
      dsimp only [X]
      calc
        _ = Cx * (ε * (J + ε * G)) + ε * (ε * G) := by ring
        _ ≤ Cx * (1 * Hbar) + 1 * Hbar := by gcongr
        _ = _ := by ring
    have hf : ε ^ 2 * Φ ≤ Cf * Hbar := by
      dsimp only [Φ]
      calc
        _ = Cf * (ε ^ 2 * (Δ + J + ε * G)) := by ring
        _ ≤ Cf * (1 * Hbar) := by gcongr
        _ = _ := by ring
    calc
      _ = ε * D + ε * X + ε ^ 2 * G + ε ^ 2 * U + ε ^ 2 * Φ := by ring
      _ ≤ Cq * Hbar + (Cx + 1) * Hbar + Hbar + 3 * Cm * Hbar + Cf * Hbar :=
        add_le_add (add_le_add (add_le_add (add_le_add hd hx) hεG) hεU) hf
      _ = _ := by ring
  rcases huv.eq_or_lt with heq | hlt
  · subst v
    have hp : (u, u) ∈ triangle 0 T := ⟨hu, le_rfl, hvT⟩
    simp only [geometricElectricSource, (h₁s.c1.axis u hp).1, (h₂s.c1.axis u hp).1,
      zero_pow (by decide : 3 ≠ 0), zero_pow (by decide : 2 ≠ 0), mul_zero,
      div_zero, zero_mul, Complex.ofReal_zero, sub_self, norm_zero]
    positivity
  · have hxB := (le_add_of_nonneg_right bot_le).trans
      (hRatio T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hs1.trans (min_le_left _ _)))
    have hfB := (le_add_of_nonneg_left bot_le).trans
      (hField T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hs2.trans (min_le_left _ _)))
    have hq t (ht : t ∈ Ioc u v) := hCharge T e ε M S₁ S₂ h₁ h₂ h₁s h₂s
      (hsmall.trans (min_le_left _ _)) u t hu ht.1 (ht.2.trans hvT)
    have hφ t (ht : t ∈ Ioc u v) : ‖S₁.phi u t - S₂.phi u t‖ ≤ Φ :=
      electric_point_norm_aux hΦ hfB ⟨hu, ht.1.le, ht.2.trans hvT⟩
    have hθ t (ht : t ∈ Ioc u v) : ‖S₁.theta u t - S₂.theta u t‖ ≤ X := by
      have hp : (u, t) ∈ triangle 0 T := ⟨hu, ht.1.le, ht.2.trans hvT⟩
      have hl₁ := h₁s.c1.lam_pos (u, t) hp
      have hl₂ := h₂s.c1.lam_pos (u, t) hp
      have hg := stab_geom_sum_le h₁s h₂s hp
      have hrad := div_nonneg (abs_nonneg (S₁.r u t - S₂.r u t))
        (h₁s.c1.r_pos (u, t) hp ht.1).le
      have hld : |S₁.lam u t - S₂.lam u t| ≤ G := by
        linarith only [hg, hrad, abs_nonneg (S₁.nu u t - S₂.nu u t)]
      have hh := stab_real_smul_difference_le
        (by rw [abs_of_pos hl₁]; exact (h₁s.box.2 (u, t) hp).2.1) hld
        (x := S₁.theta u t / (S₁.lam u t : ℂ))
        (y := S₂.theta u t / (S₂.lam u t : ℂ))
      have heq : (S₁.lam u t : ℂ) * (S₁.theta u t / (S₁.lam u t : ℂ)) -
          (S₂.lam u t : ℂ) * (S₂.theta u t / (S₂.lam u t : ℂ)) =
          S₁.theta u t - S₂.theta u t := by
        field_simp [Complex.ofReal_ne_zero.mpr hl₁.ne', Complex.ofReal_ne_zero.mpr hl₂.ne']
      rw [heq] at hh
      have hx := electric_point_norm_aux (show 0 ≤ Cx * (J + ε * G) by positivity) hxB hp
      have hx₂ := (le_add_of_nonneg_right (norm_nonneg (S₂.xi u t / (S₂.nu u t : ℂ)))).trans
        (h₂s.box.2 (u, t) hp).2.2.2.2.2.1
      apply hh.trans
      calc
        _ ≤ Cx * (J + ε * G) + G * ε := add_le_add hx (mul_le_mul_of_nonneg_left hx₂ hG)
        _ = X := by dsimp only [X]; ring
    apply (stab_geometric_electric_source_sub_le_c1 h₁s h₂s hu hlt hvT hD hX hΦ hq hθ hφ).trans
    apply (mul_le_mul_of_nonneg_left hb (show 0 ≤ 20000 * (|e| * M) ^ 2 by positivity)).trans_eq
    dsimp only [C, Hbar, Δ, J, K, G]
    ring

end EmcsfAcExtension.Local
