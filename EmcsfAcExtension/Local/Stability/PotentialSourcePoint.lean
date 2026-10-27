module

public import EmcsfAcExtension.Local.Stability.PotentialSource
public import EmcsfAcExtension.Local.Defs.Bounds
import EmcsfAcExtension.Local.Stability.PotentialSourceBounds
import EmcsfAcExtension.Local.Stability.PotentialSourceAlgebra
import EmcsfAcExtension.Local.Stability.PotentialCurrentAlgebra
import EmcsfAcExtension.Local.Stability.GeomStrongElectricSource
import EmcsfAcExtension.Local.Stability.ChargeDifferenceAlgebra
import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux

/-! # The six positive incoming-potential difference majorants

The exact A11p cancellation is subtracted at common labels. Geometric
envelopes, cubic charge Hardy terms, and local incoming scalar-ratio
terms are retained as integrable densities, before area closure.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

private theorem potential_expansion_coefficient_aux
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁) (h₂s : StabSetting e T ε M A S₂ h₂)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    let G := (geomDist T S₁ S₂).toReal
    let U := (supDist T S₁.mu S₂.mu).toReal
    let a (S : Fields) := S.nu u v * (2 * S.nu u v * S.lam u v / (1 - S.mu u v))
    |a S₁| ≤ 8 ∧ |a S₁ - a S₂| ≤ 48 * (G + U) ∧
      |S₁.r u v - S₂.r u v| / S₁.r u v ≤ G := by
  dsimp only
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hg := stab_geom_sum_le h₁s h₂s hp
  have hr : 0 ≤ |S₁.r u v - S₂.r u v| / S₁.r u v :=
    div_nonneg (abs_nonneg _) (h₁s.c1.r_pos (u, v) hp huv).le
  have hν : |S₁.nu u v - S₂.nu u v| ≤ (geomDist T S₁ S₂).toReal := by
    linarith only [hg, hr, abs_nonneg (S₁.lam u v - S₂.lam u v)]
  have hrel : |S₁.r u v - S₂.r u v| / S₁.r u v ≤ (geomDist T S₁ S₂).toReal := by
    linarith only [hg, abs_nonneg (S₁.lam u v - S₂.lam u v), abs_nonneg (S₁.nu u v - S₂.nu u v)]
  have hc := stab_geometric_electric_coefficients_c1 h₁s h₂s hu huv hvT
  have hc₂ := (stab_geometric_electric_coefficients_c1 h₂s h₂s hu huv hvT).1
  have hn : |S₁.nu u v| ≤ 1 := by
    rw [abs_of_neg (h₁s.c1.nu_neg (u, v) hp)]
    exact (h₁s.box.2 (u, v) hp).2.2.2.1
  have hh := stab_expansion_potential_coefficient_bounds hn hν hc.1 hc₂ hc.2
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  exact ⟨hh.1, hh.2, hrel⟩

/-- Six positive densities control the incoming potential source
subtraction. All displayed numerical coefficients are universal;
`C` is the fixed extended-record constant, before all field, data,
scale, background and coupling inputs. No bare singular endpoint
weight is multiplied by a uniform scalar difference. -/
theorem stab_potential_source_sub_le_of_stab_bounds_c1
    {C e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (hC : 0 < C) (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hε : ε ≤ 1)
    (hb : StabBounds C e T M (dataDist h₁ h₂ T) S₁ S₂)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    let E := |e| * M
    let Δ := dataDist h₁ h₂ T
    |potentialIncomingSource e (triangle 0 T) S₁ u v -
      potentialIncomingSource e (triangle 0 T) S₂ u v| ≤
      8 * E * ε * |geomN (triangle 0 T) S₁ u v - geomN (triangle 0 T) S₂ u v| +
      384 * C * E * Δ * |geomN (triangle 0 T) S₂ u v| +
      16 * (|S₁.Q u v - S₂.Q u v| / S₁.r u v ^ 3) +
      864 * C * Δ * (|S₂.Q u v| / S₂.r u v ^ 3) +
      32 * E * (‖S₁.xi u v / (S₁.nu u v : ℂ) - S₂.xi u v / (S₂.nu u v : ℂ)‖ / (v - u)) +
      480 * C * E * Δ * (‖S₂.xi u v / (S₂.nu u v : ℂ)‖ / (v - u)) := by
  dsimp only
  let E := |e| * M
  let Δ := dataDist h₁ h₂ T
  let d := C * Δ
  let G := (geomDist T S₁ S₂).toReal
  let U := (supDist T S₁.mu S₂.mu).toReal
  let a (S : Fields) := S.nu u v * (2 * S.nu u v * S.lam u v / (1 - S.mu u v))
  let J (S : Fields) := (starRingEnd ℂ (S.phi u v) * (S.xi u v / (S.nu u v : ℂ))).im
  let X := ‖S₁.xi u v / (S₁.nu u v : ℂ) - S₂.xi u v / (S₂.nu u v : ℂ)‖
  let Y := ‖S₂.xi u v / (S₂.nu u v : ℂ)‖
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hΔ : 0 ≤ Δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hd : 0 ≤ d := mul_nonneg hC.le hΔ
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans h₁s.box.1
  have hE : 0 ≤ E := mul_nonneg (abs_nonneg _) hM
  have hG0 : 0 ≤ G := ENNReal.toReal_nonneg
  have hU0 : 0 ≤ U := ENNReal.toReal_nonneg
  have hX : 0 ≤ X := norm_nonneg _
  have hY : 0 ≤ Y := norm_nonneg _
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi u v / (S₂.nu u v : ℂ)))).trans
      (h₂s.box.2 (u, v) hp).2.2.2.2.2.1)
  obtain ⟨hG, hU, hΦ⟩ := stab_real_distances_of_stab_bounds hd hb
  have hGU : G + U ≤ d + d := add_le_add hG hU
  have hc := potential_expansion_coefficient_aux h₁s h₂s hu huv hvT
  have hr := h₁s.c1.r_pos (u, v) hp huv
  have hs := h₂s.c1.r_pos (u, v) hp huv
  have hA := stab_real_product_sub_le (a := S₁.AV u v) (b := S₂.AV u v)
    (x := geomN (triangle 0 T) S₁ u v) (y := geomN (triangle 0 T) S₂ u v)
  have hAd := stab_potential_constraint_sub_le_of_stab_bounds_c1 hC h₁s h₂s hε hb hu huv hvT
  have hAb := stab_potential_constraint_abs_le_c1 h₁s hu huv hvT
  have hAN : |S₁.AV u v * geomN (triangle 0 T) S₁ u v -
      S₂.AV u v * geomN (triangle 0 T) S₂ u v| ≤
      8 * E * ε * |geomN (triangle 0 T) S₁ u v - geomN (triangle 0 T) S₂ u v| +
        384 * d * E * |geomN (triangle 0 T) S₂ u v| := by
    apply hA.trans
    have hh := add_le_add (mul_le_mul_of_nonneg_right hAb (abs_nonneg (geomN (triangle 0 T) S₁ u v -
        geomN (triangle 0 T) S₂ u v)))
      (mul_le_mul_of_nonneg_right hAd (abs_nonneg (geomN (triangle 0 T) S₂ u v)))
    convert hh using 1; dsimp only [E, d, Δ]; ring
  have ha : |2 * a S₁| ≤ 16 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith only [hc.1]
  have had : |2 * a S₁ - 2 * a S₂| ≤ 96 * (G + U) := by
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hh := mul_le_mul_of_nonneg_left hc.2.1 (by norm_num : (0 : ℝ) ≤ 2)
    convert hh using 1; ring
  have hR := stab_cubic_charge_source_sub_le
    (q₁ := S₁.Q u v) (q₂ := S₂.Q u v) hr hs
    (stab_radius_compare h₁s h₂s hu huv.le hvT).2 hG0 hU0 hc.2.2 ha had
  have hRadial : |(2 * a S₁) * (S₁.Q u v / S₁.r u v ^ 3) -
      (2 * a S₂) * (S₂.Q u v / S₂.r u v ^ 3)| ≤
      16 * (|S₁.Q u v - S₂.Q u v| / S₁.r u v ^ 3) +
        864 * d * (|S₂.Q u v| / S₂.r u v ^ 3) := by
    apply hR.trans
    calc
      _ ≤ 16 * (|S₁.Q u v - S₂.Q u v| / S₁.r u v ^ 3) +
          432 * (d + d) * (|S₂.Q u v| / S₂.r u v ^ 3) := by gcongr
      _ = _ := by ring
  have haE : |e * a S₁| ≤ 8 * |e| := by
    rw [abs_mul]
    apply (mul_le_mul_of_nonneg_left hc.1 (abs_nonneg e)).trans_eq
    ring
  have hadE : |e * a S₁ - e * a S₂| ≤ 48 * |e| * (G + U) := by
    rw [← mul_sub, abs_mul]
    apply (mul_le_mul_of_nonneg_left hc.2.1 (abs_nonneg e)).trans_eq
    ring
  have hJ : |J S₁ - J S₂| ≤ M * X + d * Y := by
    have hh := stab_scalar_current_sub_le (h₁s.box.2 (u, v) hp).2.2.2.2.2.2
      (le_refl Y) (le_refl X) (stab_phi_sub_le_of_stab_bounds hd hb hp)
    simpa only [J, X, Y, mul_comm] using! hh
  have hJ₂ : |J S₂| ≤ M * Y := by
    apply (Complex.abs_im_le_norm _).trans
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right (h₂s.box.2 (u, v) hp).2.2.2.2.2.2 hY
  have hCurrent := stab_current_over_radius_sub_le (sub_pos.mpr huv) hr hs
    (stab_radius_bounds h₁s hu huv.le hvT).1 (stab_radius_bounds h₂s hu huv.le hvT).1
    (abs_nonneg e) hG0 hU0 hM hd hX hY hc.2.2 haE hadE hJ hJ₂
  have heE : |e| ≤ E := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left h₁s.box.1 (abs_nonneg e)
  have hCur : |(e * a S₁) / S₁.r u v * J S₁ - (e * a S₂) / S₂.r u v * J S₂| ≤
      32 * E * (X / (v - u)) + 480 * d * E * (Y / (v - u)) := by
    apply hCurrent.trans
    calc
      _ = 32 * E * (X / (v - u)) +
          (32 * |e| * d + 224 * E * (G + U)) * (Y / (v - u)) := by dsimp only [E]; ring
      _ ≤ 32 * E * (X / (v - u)) +
          (32 * E * d + 224 * E * (d + d)) * (Y / (v - u)) := by gcongr
      _ = _ := by ring
  have hidentity (S : Fields) (hrS : S.r u v ≠ 0) (hgS : 1 - S.mu u v ≠ 0) :
      potentialIncomingSource e (triangle 0 T) S u v =
        S.AV u v * geomN (triangle 0 T) S u v -
          (2 * a S) * (S.Q u v / S.r u v ^ 3) + (e * a S) / S.r u v * J S := by
    dsimp only [potentialIncomingSource, Fields.AV, a, J]
    field_simp
  rw [hidentity S₁ hr.ne' (h₁s.c1.one_sub_mu_pos (u, v) hp).ne',
    hidentity S₂ hs.ne' (h₂s.c1.one_sub_mu_pos (u, v) hp).ne']
  apply (stab_real_three_source_sub_le _ _ _ _ _ _).trans
  apply (add_le_add (add_le_add hAN hRadial) hCur).trans_eq
  dsimp only [E, d, Δ, X, Y]
  ring

end EmcsfAcExtension.Local
