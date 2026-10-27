module

public import EmcsfAcExtension.Local.Stability.MainRecords
import EmcsfAcExtension.Local.Stability.MainFinite
import EmcsfAcExtension.Local.Stability.SourceDifferenceGeometry
import EmcsfAcExtension.Local.Stability.MomentsSections

/-! # Field specialization of the inverse-cube coefficient comparison

The geometric distance controls each expansion difference and the relative
radius difference. The first-half ratio comparison supplies the remaining
scalar factor, with the incoming phase remainder unchanged.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local.Stab

/-- [internal]
 Both inverse-cube scalar coefficients from the ratio-difference record.
`C` depends only on its fixed constant `D`, independently of all pair
parameters and derivative suprema. The incoming phase term is explicit. -/
theorem scalar_primitive_coefficients_difference_of_differences (D : ℝ) (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (T e ε M A : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      RatioDifferences D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      ∀ u v, 0 ≤ u → u < v → v ≤ T →
      (‖(S₁.nu u v : ℂ) * S₁.theta u v / (S₁.r u v : ℂ) ^ 3 -
          (S₂.nu u v : ℂ) * S₂.theta u v / (S₂.r u v : ℂ) ^ 3‖ ≤
        C * ((jDist T S₁ S₂).toReal + ε * (geomDist T S₁ S₂).toReal) / (v - u) ^ 3) ∧
      (‖(S₁.lam u v : ℂ) * S₁.xi u v / (S₁.r u v : ℂ) ^ 3 -
          (S₂.lam u v : ℂ) * S₂.xi u v / (S₂.r u v : ℂ) ^ 3‖ ≤
        C * ((kDist e T S₁ S₂).toReal + ε * (geomDist T S₁ S₂).toReal +
          sigma e M T * ε / M * ((jDist T S₁ S₂).toReal +
            ε * (geomDist T S₁ S₂).toReal + ε * dataDist h₁ h₂ T / M)) / (v - u) ^ 3) := by
  refine ⟨1024 * (D + 1), mul_pos (by norm_num) (by linarith only [hD]), ?_⟩
  intro T e ε M A S₁ S₂ h₁ h₂ hset₁ hset₂ hratio u v hu huv hvT
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hd : 0 < v - u := sub_pos.mpr huv
  have hr₁ := hset₁.c1.r_pos (u, v) hp huv
  have hr₂ := hset₂.c1.r_pos (u, v) hp huv
  have hl₁ := hset₁.c1.lam_pos (u, v) hp
  have hl₂ := hset₂.c1.lam_pos (u, v) hp
  have hn₁ := hset₁.c1.nu_neg (u, v) hp
  have hn₂ := hset₂.c1.nu_neg (u, v) hp
  have hε0 : 0 ≤ ε := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans
    (hset₂.box.2 (u, v) hp).2.2.2.2.2.1
  have hb₁ := hset₁.box.2 (u, v) hp
  have hb₂ := hset₂.box.2 (u, v) hp
  have hla₁ : |S₁.lam u v| ≤ 1 := by
    simpa only [abs_of_pos hl₁] using hb₁.2.1
  have hla₂ : |S₂.lam u v| ≤ 1 := by
    simpa only [abs_of_pos hl₂] using hb₂.2.1
  have hna₁ : |S₁.nu u v| ≤ 1 := by
    simpa only [abs_of_neg hn₁] using hb₁.2.2.2.1
  have hna₂ : |S₂.nu u v| ≤ 1 := by
    simpa only [abs_of_neg hn₂] using hb₂.2.2.2.1
  have hx₁ : ‖S₁.theta u v / (S₁.lam u v : ℂ)‖ ≤ ε :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans hb₁.2.2.2.2.2.1
  have hx₂ : ‖S₂.theta u v / (S₂.lam u v : ℂ)‖ ≤ ε :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans hb₂.2.2.2.2.2.1
  have hy₁ : ‖S₁.xi u v / (S₁.nu u v : ℂ)‖ ≤ ε :=
    (le_add_of_nonneg_left (norm_nonneg _)).trans hb₁.2.2.2.2.2.1
  have hy₂ : ‖S₂.xi u v / (S₂.nu u v : ℂ)‖ ≤ ε :=
    (le_add_of_nonneg_left (norm_nonneg _)).trans hb₂.2.2.2.2.2.1
  let G := (geomDist T S₁ S₂).toReal
  let J := (jDist T S₁ S₂).toReal
  let K := (kDist e T S₁ S₂).toReal
  let δ := dataDist h₁ h₂ T
  let Z := K + ε * G + sigma e M T * ε / M * (J + ε * G + ε * δ / M)
  have hG0 : 0 ≤ G := ENNReal.toReal_nonneg
  have hJ0 : 0 ≤ J := ENNReal.toReal_nonneg
  have hδ : 0 ≤ δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hM0 : 0 ≤ M := zero_le_one.trans hset₂.box.1
  have hσ0 : 0 ≤ sigma e M T := by unfold sigma; positivity
  have hZ0 : 0 ≤ Z := by dsimp [Z, K]; positivity
  have hgeo := geomDist_pointwise_le_of_settings hset₁ hset₂ hp
  have hrad0 : 0 ≤ |S₁.r u v - S₂.r u v| / S₁.r u v := div_nonneg (abs_nonneg _) hr₁.le
  have hδl : |S₁.lam u v - S₂.lam u v| ≤ G := by
    linarith only [hgeo, hrad0, abs_nonneg (S₁.nu u v - S₂.nu u v)]
  have hδn : |S₁.nu u v - S₂.nu u v| ≤ G := by
    linarith only [hgeo, hrad0, abs_nonneg (S₁.lam u v - S₂.lam u v)]
  have hδr : |S₁.r u v - S₂.r u v| ≤ G * (v - u) := by
    have hrel : |S₁.r u v - S₂.r u v| / S₁.r u v ≤ G := by
      linarith only [hgeo, abs_nonneg (S₁.lam u v - S₂.lam u v),
        abs_nonneg (S₁.nu u v - S₂.nu u v)]
    exact ((div_le_iff₀ hr₁).mp hrel).trans
      (mul_le_mul_of_nonneg_left (stab_radius_bounds hset₁ hu huv.le hvT).2 hG0)
  have hrb₁ := (stab_radius_bounds hset₁ hu huv.le hvT).1
  have hrb₂ := (stab_radius_bounds hset₂ hu huv.le hvT).1
  have hnorm (S : Fields) (hl : S.lam u v ≠ 0) (hn : S.nu u v ≠ 0) :
      ((S.nu u v : ℂ) * S.theta u v / (S.r u v : ℂ) ^ 3 =
        (S.nu u v : ℂ) * S.lam u v * (S.theta u v / S.lam u v) / (S.r u v : ℂ) ^ 3) ∧
      ((S.lam u v : ℂ) * S.xi u v / (S.r u v : ℂ) ^ 3 =
        (S.lam u v : ℂ) * S.nu u v * (S.xi u v / S.nu u v) / (S.r u v : ℂ) ^ 3) := by
    have hlc := ofReal_ne_zero.mpr hl
    have hnc := ofReal_ne_zero.mpr hn
    constructor <;> congr 1 <;> field_simp
  have hc₁ := hnorm S₁ hl₁.ne' hn₁.ne
  have hc₂ := hnorm S₂ hl₂.ne' hn₂.ne
  constructor
  · rw [hc₁.1, hc₂.1]
    have hbound := scalar_primitive_coefficient_difference_le hd hrb₁ hrb₂ hε0 hG0
      (mul_nonneg hD.le (add_nonneg hJ0 (mul_nonneg hε0 hG0)))
      hla₁ hla₂ hna₁ hna₂ hx₁ hx₂ hδl hδn (hratio.out_pointwise (u, v) hp) hδr
    apply hbound.trans
    apply (div_le_div_iff_of_pos_right (pow_pos hd 3)).2
    have hEG : 0 ≤ ε * G := mul_nonneg hε0 hG0
    dsimp only [J, G] at *
    nlinarith only [hJ0, hEG]
  · rw [hc₁.2, hc₂.2]
    have hbound := scalar_primitive_coefficient_difference_le hd hrb₁ hrb₂ hε0 hG0
      (mul_nonneg hD.le hZ0) hna₁ hna₂ hla₁ hla₂ hy₁ hy₂ hδn hδl
      (hratio.in_pointwise (u, v) hp) hδr
    apply hbound.trans
    apply (div_le_div_iff_of_pos_right (pow_pos hd 3)).2
    have hZ : ε * G ≤ Z := by
      have hphase : 0 ≤ sigma e M T * ε / M * (J + ε * G + ε * δ / M) := by positivity
      have hK0 : 0 ≤ K := ENNReal.toReal_nonneg
      dsimp only [Z]
      linarith only [hK0, hphase]
    nlinarith only [hZ]

end EmcsfAcExtension.Local.Stab
