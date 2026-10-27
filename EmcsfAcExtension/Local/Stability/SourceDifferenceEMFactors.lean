module

public import EmcsfAcExtension.Local.Stability.MainRecords
public import EmcsfAcExtension.Local.Stability.SourceDifferenceCharge
import EmcsfAcExtension.Local.Stability.SourceDifferenceEMAlgebra
import EmcsfAcExtension.Local.Stability.SourceDifferenceEMIdentity
import EmcsfAcExtension.Local.Stability.MainFinite

/-! # Explicit electromagnetic source comparison

The sharper data remainder is kept for the incoming closure. Constants
are chosen before every physical parameter and pair of solutions.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local.Stab

/-- [internal]
 Explicit electromagnetic sources from the first-half comparison records.
`C` depends only on their fixed constant `D`, uniformly in all physical
parameters. The data term retains its factor `ε/M`. -/
theorem explicit_em_source_difference_of_differences (D : ℝ) (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (T e ε M A : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      ε ≤ 1 → sigma e M T ≤ 1 →
      RatioDifferences D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      FieldDifference D T ε (dataDist h₁ h₂ T) S₁ S₂ →
      ChargeDifference D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      ∀ p ∈ triangle 0 T, p.1 < p.2 →
        ‖emSourceJ e S₁ p.1 p.2 - emSourceJ e S₂ p.1 p.2‖ +
          ‖emSourceK e S₁ p.1 p.2 - emSourceK e S₂ p.1 p.2‖ ≤
        C * e ^ 2 * M ^ 2 * ((jDist T S₁ S₂).toReal + (kDist e T S₁ S₂).toReal +
          ε * (geomDist T S₁ S₂).toReal + ε * dataDist h₁ h₂ T / M) := by
  obtain ⟨Q, hQ, hcharge⟩ := normalized_charge_factors_of_differences D hD
  obtain ⟨P, hP, hmono⟩ := em_monomial_difference_le Q D hQ hD
  refine ⟨16 * P * (D + 1), by positivity, ?_⟩
  intro T e ε M A S₁ S₂ h₁ h₂ hs₁ hs₂ hε₁ hσ₁ hratio hfield hq p hp hlt
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
  let B₁ := -S₁.nu p.1 p.2 * S₁.lam p.1 p.2
  let B₂ := -S₂.nu p.1 p.2 * S₂.lam p.1 p.2
  have hb₁ := hs₁.box.2 p hp
  have hb₂ := hs₂.box.2 p hp
  have hB₁ : |B₁| ≤ 1 := by
    dsimp [B₁]
    rw [abs_mul, abs_neg, abs_of_neg (hs₁.c1.nu_neg p hp), abs_of_pos (hs₁.c1.lam_pos p hp)]
    simpa only [one_mul] using mul_le_mul hb₁.2.2.2.1 hb₁.2.1
      (hs₁.c1.lam_pos p hp).le zero_le_one
  have hB₂ : |B₂| ≤ 1 := by
    dsimp [B₂]
    rw [abs_mul, abs_neg, abs_of_neg (hs₂.c1.nu_neg p hp), abs_of_pos (hs₂.c1.lam_pos p hp)]
    simpa only [one_mul] using mul_le_mul hb₂.2.2.2.1 hb₂.2.1
      (hs₂.c1.lam_pos p hp).le zero_le_one
  have hgeo := geomDist_pointwise_le_of_settings hs₁ hs₂ hp
  have hrad : 0 ≤ |S₁.r p.1 p.2 - S₂.r p.1 p.2| / S₁.r p.1 p.2 :=
    div_nonneg (abs_nonneg _) (hs₁.c1.r_pos p hp hlt).le
  have hδB : |B₁ - B₂| ≤ 2 * G := by
    have heq : B₁ - B₂ = -(S₁.nu p.1 p.2 - S₂.nu p.1 p.2) * S₁.lam p.1 p.2 -
        S₂.nu p.1 p.2 * (S₁.lam p.1 p.2 - S₂.lam p.1 p.2) := by dsimp [B₁, B₂]; ring
    rw [heq]
    have ha := abs_sub_le (-(S₁.nu p.1 p.2 - S₂.nu p.1 p.2) * S₁.lam p.1 p.2)
      0 (S₂.nu p.1 p.2 * (S₁.lam p.1 p.2 - S₂.lam p.1 p.2))
    simp only [sub_zero, zero_sub, abs_neg] at ha
    apply ha.trans
    rw [abs_mul, abs_mul, abs_neg, abs_of_pos (hs₁.c1.lam_pos p hp),
      abs_of_neg (hs₂.c1.nu_neg p hp)]
    have h₁ := mul_le_mul_of_nonneg_left hb₁.2.1 (abs_nonneg (S₁.nu p.1 p.2 - S₂.nu p.1 p.2))
    have h₂ := mul_le_mul_of_nonneg_right hb₂.2.2.2.1 (abs_nonneg (S₁.lam p.1 p.2 - S₂.lam p.1 p.2))
    dsimp [G] at *
    nlinarith only [h₁, h₂, hgeo, hrad, ENNReal.toReal_nonneg (a := geomDist T S₁ S₂)]
  have hφ : ‖S₁.phi p.1 p.2 - S₂.phi p.1 p.2‖ ≤ M * F := by
    have h := (le_add_of_nonneg_left (norm_nonneg _)).trans (hfield.bound p hp)
    convert h using 1; dsimp [F, δ, J, G]; field_simp
  have hx₁ := (le_add_of_nonneg_right (norm_nonneg _)).trans hb₁.2.2.2.2.2.1
  have hx₂ := (le_add_of_nonneg_right (norm_nonneg _)).trans hb₂.2.2.2.2.2.1
  have hy₁ := (le_add_of_nonneg_left (norm_nonneg _)).trans hb₁.2.2.2.2.2.1
  have hy₂ := (le_add_of_nonneg_left (norm_nonneg _)).trans hb₂.2.2.2.2.2.1
  have hc : ‖I * (e : ℂ)‖ ≤ |e| :=
      by simp only [norm_mul, norm_I, one_mul, norm_real, Real.norm_eq_abs, le_refl]
  have hcn : ‖-I * (e : ℂ)‖ ≤ |e| :=
      by simp only [norm_mul, norm_neg, norm_I, one_mul, norm_real, Real.norm_eq_abs, le_refl]
  have hd : ‖-I * (e : ℂ) ^ 2‖ ≤ |e| ^ 2 :=
      by simp only [norm_mul, norm_neg, norm_I, one_mul, norm_pow, norm_real, Real.norm_eq_abs,
           le_refl]
  have hq₁ : |S₁.Q p.1 p.2 / S₁.r p.1 p.2 ^ 2| ≤ |e| * M * ε :=
      by linarith only [hqbound.1, abs_nonneg (S₁.Q p.1 p.2 / S₁.r p.1 p.2 ^ 2)]
  have hq₂ : |S₂.Q p.1 p.2 / S₂.r p.1 p.2 ^ 2| ≤ |e| * M * ε :=
      by linarith only [hqbound.2.1, abs_nonneg (S₂.Q p.1 p.2 / S₂.r p.1 p.2 ^ 2)]
  have hmₒ := hmono |e| M ε G H Zₒ F B₁ B₂
    (S₁.Q p.1 p.2 / S₁.r p.1 p.2 ^ 2) (S₂.Q p.1 p.2 / S₂.r p.1 p.2 ^ 2)
    (S₁.phi p.1 p.2) (S₂.phi p.1 p.2)
    (S₁.theta p.1 p.2 / S₁.lam p.1 p.2) (S₂.theta p.1 p.2 / S₂.lam p.1 p.2)
    (I * e) (-I * (e : ℂ) ^ 2) (abs_nonneg _) hM hε hε₁ hG hH hZₒ hF
    hB₁ hB₂ hδB hq₁ hq₂ hqbound.2.2 hb₁.2.2.2.2.2.2 hb₂.2.2.2.2.2.2 hφ
    hx₁ hx₂ (hratio.out_pointwise p hp) hc hd
  have hmᵢ := hmono |e| M ε G H Zᵢ F B₁ B₂
    (S₁.Q p.1 p.2 / S₁.r p.1 p.2 ^ 2) (S₂.Q p.1 p.2 / S₂.r p.1 p.2 ^ 2)
    (S₁.phi p.1 p.2) (S₂.phi p.1 p.2)
    (S₁.xi p.1 p.2 / S₁.nu p.1 p.2) (S₂.xi p.1 p.2 / S₂.nu p.1 p.2)
    (-I * e) (-I * (e : ℂ) ^ 2) (abs_nonneg _) hM hε hε₁ hG hH hZᵢ hF
    hB₁ hB₂ hδB hq₁ hq₂ hqbound.2.2 hb₁.2.2.2.2.2.2 hb₂.2.2.2.2.2.2 hφ
    hy₁ hy₂ (hratio.in_pointwise p hp) hcn hd
  have heqₒ (S : Fields) (hr : S.r p.1 p.2 ≠ 0) (hl : S.lam p.1 p.2 ≠ 0) :=
    emSourceJ_eq_monomials e S p.1 p.2 hr hl
  have heqᵢ (S : Fields) (hr : S.r p.1 p.2 ≠ 0) (hn : S.nu p.1 p.2 ≠ 0) :=
    emSourceK_eq_monomials e S p.1 p.2 hr hn
  rw [heqₒ S₁ (hs₁.c1.r_pos p hp hlt).ne' (hs₁.c1.lam_pos p hp).ne',
    heqₒ S₂ (hs₂.c1.r_pos p hp hlt).ne' (hs₂.c1.lam_pos p hp).ne',
    heqᵢ S₁ (hs₁.c1.r_pos p hp hlt).ne' (hs₁.c1.nu_neg p hp).ne,
    heqᵢ S₂ (hs₂.c1.r_pos p hp hlt).ne' (hs₂.c1.nu_neg p hp).ne]
  have ho : ‖_‖ ≤ P * |e| ^ 2 * M ^ 2 * ((4 + D) * X) :=
    hmₒ.trans (mul_le_mul_of_nonneg_left hsumₒ (by positivity))
  have hi : ‖_‖ ≤ P * |e| ^ 2 * M ^ 2 * ((5 + D) * X) :=
    hmᵢ.trans (mul_le_mul_of_nonneg_left hsumᵢ (by positivity))
  have hrewrite (b q : ℝ) (z φ : ℂ) :
      5 * (b : ℂ) * q ^ 2 * z + I * e * b * q * (3 * z + φ) -
          I * (e : ℂ) ^ 2 * b * φ * (((starRingEnd ℂ φ * z).im : ℝ) : ℂ) =
        5 * (b : ℂ) * q ^ 2 * z + (I * e) * b * q * (3 * z + φ) +
          (-I * (e : ℂ) ^ 2) * b * φ * (((starRingEnd ℂ φ * z).im : ℝ) : ℂ) := by ring
  have hrewriten (b q : ℝ) (z φ : ℂ) :
      5 * (b : ℂ) * q ^ 2 * z - I * e * b * q * (3 * z + φ) -
          I * (e : ℂ) ^ 2 * b * φ * (((starRingEnd ℂ φ * z).im : ℝ) : ℂ) =
        5 * (b : ℂ) * q ^ 2 * z + (-I * e) * b * q * (3 * z + φ) +
          (-I * (e : ℂ) ^ 2) * b * φ * (((starRingEnd ℂ φ * z).im : ℝ) : ℂ) := by ring
  simp only [hrewrite, hrewriten]
  apply (add_le_add ho hi).trans
  rw [sq_abs]
  have hcoef : 9 + 2 * D ≤ 16 * (D + 1) := by linarith only [hD]
  have := mul_le_mul_of_nonneg_right hcoef (by positivity : 0 ≤ P * e ^ 2 * M ^ 2 * X)
  dsimp only [X, J, K, G, δ] at *
  nlinarith only [this]

end EmcsfAcExtension.Local.Stab
