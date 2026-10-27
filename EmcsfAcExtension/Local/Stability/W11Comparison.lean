module

public import EmcsfAcExtension.Local.Stability.W11Integral
import EmcsfAcExtension.Local.Stability.AssemblyMoments
import EmcsfAcExtension.Local.Stability.DifferenceMomentsCloseOut
import EmcsfAcExtension.Local.Stability.DifferenceMomentsCloseIn
import EmcsfAcExtension.Local.Stability.DifferenceMomentsMixedHardy
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMass
import EmcsfAcExtension.Local.Stability.GeometryDifferenceWeights
import EmcsfAcExtension.Local.Stability.PotentialDifferenceBudget

/-! # Closing the characteristic derivative comparison

The main Lipschitz input is kept explicit while internal project record is being proved.
No variation or strong-derivative conclusion is assumed. The mass gap,
cubic correction, and incoming phase are estimated separately.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem triple_bounds_aux {x y z : ℝ≥0∞} {B : ℝ}
    (_hB : 0 ≤ B) (h : x + y + z ≤ ENNReal.ofReal B) :
    x ≤ ENNReal.ofReal B ∧ y ≤ ENNReal.ofReal B ∧ z ≤ ENNReal.ofReal B := by
  exact ⟨(le_add_of_nonneg_right bot_le).trans
      ((le_add_of_nonneg_right bot_le).trans h),
    (le_add_of_nonneg_left bot_le).trans ((le_add_of_nonneg_right bot_le).trans h),
    (le_add_of_nonneg_left bot_le).trans h⟩

private theorem in_mixed_linear_aux
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (hA : 0 < A) (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hε : ε ^ 2 ≤ 1 / 4)
    {v : ℝ} (hv : v ∈ Icc 0 T) :
    (∫⁻ u in Icc 0 v, ENNReal.ofReal (-S₁.nu u v / S₁.r u v *
      ‖S₂.xi u v / (S₂.nu u v : ℂ)‖)) ≤ ENNReal.ofReal (256 * A * ε) := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hm : (∫⁻ u in Icc 0 v, ENNReal.ofReal (-S₁.nu u v / S₁.r u v *
      ‖S₂.xi u v / (S₂.nu u v : ℂ)‖)) ≤
      16 * ∫⁻ u in Icc 0 v, ENNReal.ofReal (-S₂.nu u v / S₂.r u v *
        ‖S₂.xi u v / (S₂.nu u v : ℂ)‖) := by
    rw [← lintegral_const_mul' 16 _ (by norm_num)]
    apply setLIntegral_mono' measurableSet_Icc
    intro u hu
    rcases hu.2.eq_or_lt with rfl | huv
    · rw [(h₁s.c1.axis u ⟨hu.1, le_rfl, hv.2⟩).1, div_zero, zero_mul,
        ENNReal.ofReal_zero]
      exact bot_le
    · have hh := mul_le_mul_of_nonneg_right
        (stab_in_weight_le_sixteen h₁s h₂s hu.1 huv hv.2)
        (norm_nonneg (S₂.xi u v / (S₂.nu u v : ℂ)))
      simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16),
        ENNReal.ofReal_ofNat, mul_assoc] using ENNReal.ofReal_le_ofReal hh
  have hh := stab_in_hardy h₂s hε hv.1 hv.2
  have he := (le_add_of_nonneg_left bot_le).trans h₂s.env
  apply (hm.trans (mul_le_mul' le_rfl (hh.trans (mul_le_mul' le_rfl he)))).trans
  rw [← ENNReal.ofReal_ofNat 16, ← mul_assoc,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16 * (16 / 3))]
  apply ENNReal.ofReal_le_ofReal
  have hn : 0 ≤ A * ε := mul_nonneg hA.le hε0
  nlinarith only [hn]

private theorem derivative_budget_aux
    {X D E H L : ℝ≥0∞} {ε A U G B Bμ BH : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hA : 0 ≤ A)
    (_hU : 0 ≤ U) (hG : 0 ≤ G) (hB : 0 ≤ B) (hBμ : 0 ≤ Bμ) (hBH : 0 ≤ BH)
    (hUB : U ≤ Bμ) (hGB : G ≤ B)
    (hD : D ≤ ENNReal.ofReal B) (hE : E ≤ ENNReal.ofReal (A * ε))
    (hH : H ≤ ENNReal.ofReal BH) (hL : L ≤ ENNReal.ofReal (256 * A * ε))
    (hX : X ≤ 4 * D + ENNReal.ofReal (16 * U) * E +
      ENNReal.ofReal (3 * ε ^ 2) * H + ENNReal.ofReal (20 * G * ε ^ 2) * L) :
    X ≤ ENNReal.ofReal (4 * B + 16 * Bμ * A + 3 * BH + 5120 * B * A) := by
  have heps : ε ^ 2 ≤ 1 := by nlinarith only [hε, hε1]
  have hEU : ENNReal.ofReal (16 * U) ≤ ENNReal.ofReal (16 * Bμ) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hUB (by norm_num))
  have hEA : E ≤ ENNReal.ofReal A := hE.trans
    (ENNReal.ofReal_le_ofReal (by nlinarith only [mul_le_mul_of_nonneg_left hε1 hA]))
  have h3 : ENNReal.ofReal (3 * ε ^ 2) ≤ ENNReal.ofReal 3 :=
    ENNReal.ofReal_le_ofReal (by linarith only [heps])
  have h20 : ENNReal.ofReal (20 * G * ε ^ 2) ≤ ENNReal.ofReal (20 * B) := by
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ 20 * G * 1 := mul_le_mul_of_nonneg_left heps (by positivity)
      _ ≤ _ := by linarith only [hGB]
  have h256 : L ≤ ENNReal.ofReal (256 * A) := hL.trans
    (ENNReal.ofReal_le_ofReal (by nlinarith only [mul_le_mul_of_nonneg_left hε1 hA]))
  apply (hX.trans (add_le_add (add_le_add (add_le_add
    (mul_le_mul' le_rfl hD) (mul_le_mul' hEU hEA))
    (mul_le_mul' h3 hH)) (mul_le_mul' h20 h256))).trans_eq
  rw [← ENNReal.ofReal_ofNat 4,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 16 * Bμ),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 20 * B),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

/-- [internal]
Characteristic derivative comparison conditional only on the first three
clauses of the main Lipschitz estimate. The threshold and comparison
constant depend on `A` and its uniform main constant `C₀`, before all data,
fields, coupling, background, time and minimum radius. This helper does
not assume a variation, Hardy-difference or geometric-derivative conclusion. -/
theorem Stab.characteristic_variation_difference_of_main_lipschitz
    (A C₀ : ℝ) (hA : 0 < A) (hC₀ : 0 < C₀) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        jDist T S₁ S₂ + kDist e T S₁ S₂ + geomDist T S₁ S₂ ≤
          ENNReal.ofReal (C₀ * dataDist h₁ h₂ T) →
        (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T,
          ‖pdV (triangle 0 T) S₁.a u v - pdV (triangle 0 T) S₂.a u v‖ₑ) +
        (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
          ‖(pdU (triangle 0 T) S₁.b u v + Complex.I * e * S₁.A u v * S₁.b u v) -
            (pdU (triangle 0 T) S₂.b u v + Complex.I * e * S₂.A u v * S₂.b u v)‖ₑ) ≤
          ENNReal.ofReal (C * dataDist h₁ h₂ T) := by
  obtain ⟨ηo, Co, hηo, hCo, hOut⟩ := stab_out_difference A hA
  obtain ⟨ηi, Ci, hηi, hCi, hIn⟩ := stab_in_difference A hA
  obtain ⟨ηm, Cm, hηm, hCm, hMass⟩ := Stab.mass_volterra_difference A hA
  obtain ⟨ηp, Cp, hηp, hCp, hPhase⟩ := stab_potential_phase_bounds A hA
  let Kμ := Cm * (4 * C₀ + 1)
  let Ko := 2 * Co * C₀
  let Ki := Ci * (2 * C₀ + Cp * (2 * C₀ + 1))
  let C := 8 * C₀ + 32 * Kμ * A + 3 * (Ko + Ki) + 10240 * C₀ * A
  have hKμ : 0 < Kμ := by dsimp only [Kμ]; positivity
  have hKo : 0 < Ko := by dsimp only [Ko]; positivity
  have hKi : 0 < Ki := by dsimp only [Ki]; positivity
  refine ⟨min ηo (min ηi (min ηm (min ηp (1 / 4)))), C,
    lt_min hηo (lt_min hηi (lt_min hηm (lt_min hηp (by norm_num)))),
    by dsimp only [C]; positivity, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall hmain
  let Δ := dataDist h₁ h₂ T
  let J := (jDist T S₁ S₂).toReal
  let K := (kDist e T S₁ S₂).toReal
  let G := (geomDist T S₁ S₂).toReal
  let U := (supDist T S₁.mu S₂.mu).toReal
  let P := T * |e| * (supDist T S₁.A S₂.A).toReal
  let B := C₀ * Δ
  have hΔ : 0 ≤ Δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hB : 0 ≤ B := mul_nonneg hC₀.le hΔ
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hσ : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hsmall4 : ε ^ 2 + sigma e M T ≤ 1 / 4 :=
    hsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
  have hεsq : ε ^ 2 ≤ 1 / 4 := by linarith only [hsmall4, hσ]
  have hε1 : ε ≤ 1 := by nlinarith only [hεsq, sq_nonneg (ε - 1)]
  have hσ1 : sigma e M T ≤ 1 := by linarith only [hsmall4, sq_nonneg ε]
  obtain ⟨hJD, hKD, hGD⟩ := triple_bounds_aux hB hmain
  have real_bound {X : ℝ≥0∞} (hX : X ≤ ENNReal.ofReal B) : X.toReal ≤ B := by
    simpa only [ENNReal.toReal_ofReal hB] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hX
  have hJ : J ≤ B := real_bound hJD
  have hK : K ≤ B := real_bound hKD
  have hG : G ≤ B := real_bound hGD
  have hJ0 : 0 ≤ J := ENNReal.toReal_nonneg
  have hK0 : 0 ≤ K := ENNReal.toReal_nonneg
  have hG0 : 0 ≤ G := ENNReal.toReal_nonneg
  have hU0 : 0 ≤ U := ENNReal.toReal_nonneg
  have hT : 0 ≤ T := h₁s.pos.le
  have hP0 : 0 ≤ P := by dsimp only [P]; positivity
  have hmass := hMass T e ε M S₁ S₂ h₁ h₂ h₁s h₂s
    (hsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hμraw := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    ((le_add_of_nonneg_right bot_le).trans hmass)
  rw [ENNReal.toReal_ofReal (by positivity)] at hμraw
  have hμarg : ε * J + ε ^ 2 * G + sigma e M T * ε * (J + ε * Δ + ε * G) ≤ 4 * B + Δ := by
    calc
      _ ≤ 1 * B + 1 ^ 2 * B + 1 * 1 * (B + 1 * Δ + 1 * B) := by gcongr
      _ = _ := by ring
  have hμ : U ≤ Kμ * Δ := by
    calc
      U ≤ Cm * (ε * J + ε ^ 2 * G + sigma e M T * ε * (J + ε * Δ + ε * G)) := by
        dsimp only [U, J, G, Δ]
        linarith only [hμraw]
      _ ≤ Cm * (4 * B + Δ) := mul_le_mul_of_nonneg_left hμarg hCm.le
      _ = _ := by dsimp only [B, Kμ]; ring
  have hp := (hPhase T e ε M S₁ S₂ h₁ h₂ h₁s h₂s
    (hsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))))).2
  have hP : P ≤ Cp * (2 * B + Δ) := by
    calc
      P ≤ Cp * sigma e M T * (J + ε * Δ + ε * G) := hp
      _ ≤ Cp * 1 * (B + 1 * Δ + 1 * B) := by gcongr
      _ = _ := by ring
  have ho := (le_add_of_nonneg_left bot_le).trans
    (hOut T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hsmall.trans (min_le_left _ _)))
  have hi := (le_add_of_nonneg_left bot_le).trans
    (hIn T e ε M S₁ S₂ h₁ h₂ h₁s h₂s
      (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hoB : Co * (J + ε * G) ≤ Ko * Δ := by
    calc
      _ ≤ Co * (B + 1 * B) := by gcongr
      _ = _ := by dsimp only [B, Ko]; ring
  have hiB : Ci * (K + ε * G) + Ci * ε * P / 2 ≤ Ki * Δ := by
    calc
      _ ≤ Ci * (B + 1 * B) + Ci * 1 * (Cp * (2 * B + Δ)) := by
        have hh : Ci * ε * P / 2 ≤ Ci * ε * P := by
          linarith only [mul_nonneg (mul_nonneg hCi.le hε) hP0]
        exact (add_le_add le_rfl hh).trans (by gcongr)
      _ = _ := by dsimp only [B, Ki]; ring
  have hOutSup : (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T,
      ‖pdV (triangle 0 T) S₁.a u v - pdV (triangle 0 T) S₂.a u v‖ₑ) ≤
      ENNReal.ofReal ((4 * C₀ + 16 * Kμ * A + 3 * Ko + 5120 * C₀ * A) * Δ) := by
    apply iSup₂_le
    intro u hu
    have hH := (le_iSup₂_of_le u hu le_rfl).trans ho
    have hHb := hH.trans (ENNReal.ofReal_le_ofReal hoB)
    have hb := derivative_budget_aux hε hε1 hA.le hU0 hG0 hB (by positivity) (by positivity)
      hμ hG hJD ((le_add_of_nonneg_right bot_le).trans h₂s.env) hHb
      (stab_out_mixed_hardy_le h₁s h₂s hεsq hu.1 hu.2)
      (stab_out_derivative_difference_lintegral_raw h₁s h₂s hu.1 hu.2)
    convert hb using 1
    dsimp only [B]
    congr 1
    ring
  have hInSup : (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
      ‖(pdU (triangle 0 T) S₁.b u v + Complex.I * e * S₁.A u v * S₁.b u v) -
        (pdU (triangle 0 T) S₂.b u v + Complex.I * e * S₂.A u v * S₂.b u v)‖ₑ) ≤
      ENNReal.ofReal ((4 * C₀ + 16 * Kμ * A + 3 * Ki + 5120 * C₀ * A) * Δ) := by
    apply iSup₂_le
    intro v hv
    have hH := (le_iSup₂_of_le v hv le_rfl).trans hi
    have hHb : (∫⁻ u in Icc 0 v, ENNReal.ofReal (-S₁.nu u v / S₁.r u v *
        ‖S₁.xi u v / (S₁.nu u v : ℂ) - S₂.xi u v / (S₂.nu u v : ℂ)‖)) ≤
        ENNReal.ofReal (Ki * Δ) := by
      apply hH.trans
      apply ENNReal.ofReal_le_ofReal
      convert hiB using 1; dsimp only [P, K, G]; ring
    have hb := derivative_budget_aux hε hε1 hA.le hU0 hG0 hB (by positivity) (by positivity)
      hμ hG hKD ((le_add_of_nonneg_left bot_le).trans h₂s.env) hHb
      (in_mixed_linear_aux hA h₁s h₂s hεsq hv)
      (stab_in_derivative_difference_lintegral_raw h₁s h₂s hv.1 hv.2)
    convert hb using 1
    dsimp only [B]
    congr 1
    ring
  apply (add_le_add hOutSup hInSup).trans_eq
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  dsimp only [C]
  ring

end EmcsfAcExtension.Local
