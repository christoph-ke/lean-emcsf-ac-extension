module

public import EmcsfAcExtension.Local.Stability.MainRecords
public import EmcsfAcExtension.Local.Stability.SourceDifferenceEMPrimitives
public import EmcsfAcExtension.Local.Stability.SourceDifferenceCharge
import EmcsfAcExtension.Local.Stability.SourceDifferenceEMPrimitiveAlgebra
import EmcsfAcExtension.Local.Stability.MainFinite

/-! # Charged primitive integrand differences on a common radius scale

Both raw integrands retain their radius-square weight. The sharper datum
remainder is retained before characteristic integration.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local.Stab

/-- [internal]
 Pointwise difference of both literal charged primitive integrands.
`C` depends only on the fixed first-half comparison constant `D`,
uniformly in all physical parameters, data and derivative suprema.
The arbitrary common upper radius `d` will be the segment length. -/
theorem emPrimitive_difference_of_differences (D : ℝ) (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (T e ε M A : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      ε ≤ 1 → sigma e M T ≤ 1 →
      RatioDifferences D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      FieldDifference D T ε (dataDist h₁ h₂ T) S₁ S₂ →
      ChargeDifference D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      ∀ p ∈ triangle 0 T, p.1 < p.2 → ∀ d : ℝ, 0 ≤ d →
      S₁.r p.1 p.2 ≤ d → S₂.r p.1 p.2 ≤ d →
      let X := (jDist T S₁ S₂).toReal + (kDist e T S₁ S₂).toReal +
        ε * (geomDist T S₁ S₂).toReal + ε * dataDist h₁ h₂ T / M
      ‖emPrimitiveOut e S₁ p.1 p.2 - emPrimitiveOut e S₂ p.1 p.2‖ ≤
        C * e ^ 2 * M ^ 2 * d ^ 2 * X ∧
      ‖emPrimitiveIn e S₁ p.1 p.2 - emPrimitiveIn e S₂ p.1 p.2‖ ≤
        C * e ^ 2 * M ^ 2 * d ^ 2 * X := by
  obtain ⟨Q, hQ, hcharge⟩ := normalized_charge_factors_of_differences D hD
  obtain ⟨P, hP, hbracket⟩ := em_primitive_bracket_difference_le Q D hQ hD
  refine ⟨8 * (P + 1) * (D + 1), by positivity, ?_⟩
  intro T e ε M A S₁ S₂ h₁ h₂ hs₁ hs₂ hε₁ hσ₁ hratio hfield hq p hp hlt d hd hdr₁ hdr₂
  let J := (jDist T S₁ S₂).toReal
  let K := (kDist e T S₁ S₂).toReal
  let G := (geomDist T S₁ S₂).toReal
  let δ := dataDist h₁ h₂ T
  let H := J + ε * G + ε * δ / M
  let X := J + K + ε * G + ε * δ / M
  let Zₒ := J + ε * G
  let Zᵢ := K + ε * G + sigma e M T * ε / M * H
  let F := D * (δ + J + ε * G) / M
  have hM : 1 ≤ M := hs₂.box.1
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hε : 0 ≤ ε := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans
    (hs₂.box.2 p hp).2.2.2.2.2.1
  have hJ : 0 ≤ J := ENNReal.toReal_nonneg
  have hK : 0 ≤ K := ENNReal.toReal_nonneg
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hδ : 0 ≤ δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hσ : 0 ≤ sigma e M T := by unfold sigma; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hZₒ : 0 ≤ Zₒ := by dsimp [Zₒ]; positivity
  have hZᵢ : 0 ≤ Zᵢ := by dsimp [Zᵢ]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hphase : sigma e M T * ε / M * H ≤ H := by
    have hq₁ : sigma e M T * ε / M ≤ 1 := by
      apply (div_le_iff₀ hM0).2
      rw [one_mul]
      exact ((mul_le_of_le_one_left hε hσ₁).trans hε₁).trans hs₂.box.1
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hq₁ hH
  have hEF : ε * F ≤ D * X := by
    have hdiv : (J + ε * G) / M ≤ J + ε * G :=
      div_le_self (by positivity) hM
    have hεδ : ε * ((J + ε * G) / M) ≤ J + ε * G :=
      (mul_le_mul_of_nonneg_right hε₁ (by positivity)).trans (by simpa using hdiv)
    have heq : ε * F = D * (ε * δ / M + ε * ((J + ε * G) / M)) := by dsimp [F]; ring
    rw [heq]
    apply mul_le_mul_of_nonneg_left _ hD.le
    dsimp [X]
    linarith only [hεδ, hK]
  have hδterm : 0 ≤ ε * δ / M := by positivity
  have hεG : 0 ≤ ε * G := mul_nonneg hε hG
  have hsumₒ : H + Zₒ + ε * G + ε * F ≤ (4 + D) * X := by
    have h₁ : H ≤ X := by dsimp [H, X]; linarith only [hK]
    have h₂ : Zₒ ≤ X := by dsimp [Zₒ, X]; linarith only [hK, hδterm]
    have h₃ : ε * G ≤ X := by dsimp [X]; linarith only [hJ, hK, hδterm]
    nlinarith only [h₁, h₂, h₃, hEF, hX]
  have hsumᵢ : H + Zᵢ + ε * G + ε * F ≤ (5 + D) * X := by
    have h₁ : H ≤ X := by dsimp [H, X]; linarith only [hK]
    have h₂ : Zᵢ ≤ 2 * X :=
        by dsimp only [Zᵢ, H, X] at *; linarith only [hphase, hJ, hK, hεG, hδterm]
    have h₃ : ε * G ≤ X := by dsimp [X]; linarith only [hJ, hK, hδterm]
    nlinarith only [h₁, h₂, h₃, hEF, hX]
  have hqbound := hcharge T e ε M A S₁ S₂ h₁ h₂ hs₁ hs₂ hq p hp hlt
  have hb₁ := hs₁.box.2 p hp
  have hb₂ := hs₂.box.2 p hp
  have hr₁ := hs₁.c1.r_pos p hp hlt
  have hr₂ := hs₂.c1.r_pos p hp hlt
  have hl₁ := hs₁.c1.lam_pos p hp
  have hl₂ := hs₂.c1.lam_pos p hp
  have hn₁ := hs₁.c1.nu_neg p hp
  have hn₂ := hs₂.c1.nu_neg p hp
  have hla₁ : |S₁.lam p.1 p.2| ≤ 1 := by simpa only [abs_of_pos hl₁] using hb₁.2.1
  have hla₂ : |S₂.lam p.1 p.2| ≤ 1 := by simpa only [abs_of_pos hl₂] using hb₂.2.1
  have hna₁ : |S₁.nu p.1 p.2| ≤ 1 := by simpa only [abs_of_neg hn₁] using hb₁.2.2.2.1
  have hna₂ : |S₂.nu p.1 p.2| ≤ 1 := by simpa only [abs_of_neg hn₂] using hb₂.2.2.2.1
  have hgeo := geomDist_pointwise_le_of_settings hs₁ hs₂ hp
  have hrad : 0 ≤ |S₁.r p.1 p.2 - S₂.r p.1 p.2| / S₁.r p.1 p.2 :=
    div_nonneg (abs_nonneg _) hr₁.le
  have hδl : |S₁.lam p.1 p.2 - S₂.lam p.1 p.2| ≤ G := by
    linarith only [hgeo, hrad, abs_nonneg (S₁.nu p.1 p.2 - S₂.nu p.1 p.2)]
  have hδn : |S₁.nu p.1 p.2 - S₂.nu p.1 p.2| ≤ G := by
    linarith only [hgeo, hrad, abs_nonneg (S₁.lam p.1 p.2 - S₂.lam p.1 p.2)]
  have hδr : |S₁.r p.1 p.2 - S₂.r p.1 p.2| ≤ G * d :=
    (radius_difference_le_geomDist hs₁ hs₂ hp).trans
      (mul_le_mul_of_nonneg_left hdr₁ hG)
  have hφ : ‖S₁.phi p.1 p.2 - S₂.phi p.1 p.2‖ ≤ M * F := by
    have h := (le_add_of_nonneg_left (norm_nonneg _)).trans (hfield.bound p hp)
    convert h using 1; dsimp [F, δ, J, G]; field_simp
  have hx₁ := (le_add_of_nonneg_right (norm_nonneg _)).trans hb₁.2.2.2.2.2.1
  have hx₂ := (le_add_of_nonneg_right (norm_nonneg _)).trans hb₂.2.2.2.2.2.1
  have hy₁ := (le_add_of_nonneg_left (norm_nonneg _)).trans hb₁.2.2.2.2.2.1
  have hy₂ := (le_add_of_nonneg_left (norm_nonneg _)).trans hb₂.2.2.2.2.2.1
  have hc : ‖I * (e : ℂ)‖ ≤ |e| := by
    simp only [norm_mul, norm_I, one_mul, norm_real, Real.norm_eq_abs, le_refl]
  have hcn : ‖-I * (e : ℂ)‖ ≤ |e| := by simpa only [neg_mul, norm_neg] using hc
  have hq₁ : |S₁.Q p.1 p.2 / S₁.r p.1 p.2 ^ 2| ≤ |e| * M * ε := by
    linarith only [hqbound.1, abs_nonneg (S₁.Q p.1 p.2 / S₁.r p.1 p.2 ^ 2)]
  have hq₂ : |S₂.Q p.1 p.2 / S₂.r p.1 p.2 ^ 2| ≤ |e| * M * ε := by
    linarith only [hqbound.2.1, abs_nonneg (S₂.Q p.1 p.2 / S₂.r p.1 p.2 ^ 2)]
  have hbo := hbracket |e| M ε H Zₒ F
    (S₁.Q p.1 p.2 / S₁.r p.1 p.2 ^ 2) (S₂.Q p.1 p.2 / S₂.r p.1 p.2 ^ 2)
    (S₁.phi p.1 p.2) (S₂.phi p.1 p.2)
    (S₁.theta p.1 p.2 / S₁.lam p.1 p.2) (S₂.theta p.1 p.2 / S₂.lam p.1 p.2)
    (-I * e) (abs_nonneg _) hM hε hε₁ hH hZₒ hF hq₁ hq₂ hqbound.2.2
    hb₁.2.2.2.2.2.2 hb₂.2.2.2.2.2.2 hφ hx₁ hx₂ (hratio.out_pointwise p hp) hcn
  have hbi := hbracket |e| M ε H Zᵢ F
    (S₁.Q p.1 p.2 / S₁.r p.1 p.2 ^ 2) (S₂.Q p.1 p.2 / S₂.r p.1 p.2 ^ 2)
    (S₁.phi p.1 p.2) (S₂.phi p.1 p.2)
    (S₁.xi p.1 p.2 / S₁.nu p.1 p.2) (S₂.xi p.1 p.2 / S₂.nu p.1 p.2)
    (I * e) (abs_nonneg _) hM hε hε₁ hH hZᵢ hF hq₁ hq₂ hqbound.2.2
    hb₁.2.2.2.2.2.2 hb₂.2.2.2.2.2.2 hφ hy₁ hy₂ (hratio.in_pointwise p hp) hc
  simp only [sq_abs] at hbo hbi
  have hro := em_radial_integrand_difference_le hd hG
    (by positivity : 0 ≤ e ^ 2 * M ^ 2) hε hP.le
    (by positivity : 0 ≤ H + Zₒ + ε * F)
    hla₁ hla₂ hδl hr₁.le hr₂.le hdr₁ hdr₂ hδr (by simpa only [mul_assoc] using hbo.1)
    (by simpa only [mul_assoc] using hbo.2)
  have hri := em_radial_integrand_difference_le hd hG
    (by positivity : 0 ≤ e ^ 2 * M ^ 2) hε hP.le
    (by positivity : 0 ≤ H + Zᵢ + ε * F)
    hna₁ hna₂ hδn hr₁.le hr₂.le hdr₁ hdr₂ hδr (by simpa only [mul_assoc] using hbi.1)
    (by simpa only [mul_assoc] using hbi.2)
  have hε₂G : ε ^ 2 * G ≤ ε * G := by
    have := mul_le_mul_of_nonneg_right hε₁ (mul_nonneg hε hG)
    nlinarith only [this]
  have hfinish (Z : ℝ) (hz : H + Z + ε * G + ε * F ≤ (5 + D) * X) :
      e ^ 2 * M ^ 2 * d ^ 2 * (6 * ε ^ 2 * G + P * (H + Z + ε * F)) ≤
        8 * (P + 1) * (D + 1) * e ^ 2 * M ^ 2 * d ^ 2 * X := by
    have hGX : ε * G ≤ X := by dsimp only [X]; linarith only [hJ, hK, hδterm]
    have hZbound : H + Z + ε * F ≤ (5 + D) * X := by linarith only [hz, hεG]
    have h₁ := mul_le_mul_of_nonneg_left hZbound hP.le
    have hcoef : 6 + P * (5 + D) ≤ 8 * (P + 1) * (D + 1) := by
      have := mul_nonneg hP.le hD.le
      nlinarith only [this, hP, hD]
    have h₂ := mul_le_mul_of_nonneg_right hcoef hX
    have hsmall : 6 * ε ^ 2 * G + P * (H + Z + ε * F) ≤
        8 * (P + 1) * (D + 1) * X := by nlinarith only [hε₂G, hGX, h₁, h₂]
    convert mul_le_mul_of_nonneg_left hsmall
      (by positivity : 0 ≤ e ^ 2 * M ^ 2 * d ^ 2) using 1; ring
  rw [emPrimitiveOut_eq_normalized e S₁ p.1 p.2 hr₁.ne' hl₁.ne',
    emPrimitiveOut_eq_normalized e S₂ p.1 p.2 hr₂.ne' hl₂.ne',
    emPrimitiveIn_eq_normalized e S₁ p.1 p.2 hr₁.ne' hn₁.ne,
    emPrimitiveIn_eq_normalized e S₂ p.1 p.2 hr₂.ne' hn₂.ne]
  constructor
  · simpa only [mul_assoc] using hro.trans (hfinish Zₒ (by nlinarith only [hsumₒ, hX]))
  · simpa only [mul_assoc] using hri.trans (hfinish Zᵢ hsumᵢ)

end EmcsfAcExtension.Local.Stab
