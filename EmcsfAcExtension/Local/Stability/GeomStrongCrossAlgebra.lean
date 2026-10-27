module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux
import EmcsfAcExtension.Local.Stability.GeometryDifferenceOpticalComparison

/-! # Subtracting the cross expansion source

The singular factor remains in the positive radial measure. Both
orientations retain the weighted mass difference rather than a uniform
mass difference multiplied by a divergent endpoint weight.
-/

public section

namespace EmcsfAcExtension.Local

/-- Product subtraction for a cross expansion density. The coefficients
`4,84,16` are universal and every singular weight remains explicit. -/
theorem stab_cross_source_algebra {a b w z μ ν q s G U : ℝ}
    (hw : 0 ≤ w) (hq : 0 ≤ s) (hG : 0 ≤ G) (hU : 0 ≤ U)
    (ha : |a| ≤ 4) (hb : |b| ≤ 4)
    (hab : |a - b| ≤ 4 * G + 16 * U) (hwz : |w - z| ≤ 20 * G * w) :
    |a * w * (μ - q) - b * z * (ν - s)| ≤
      4 * w * |μ - ν| + 4 * w * |q - s| +
        (84 * G + 16 * U) * w * (|ν| + s) := by
  have hbase : |ν - s| ≤ |ν| + s := by simpa only [abs_of_nonneg hq] using abs_sub ν s
  have hdiff : |(μ - ν) - (q - s)| ≤ |μ - ν| + |q - s| := abs_sub _ _
  have heq : a * w * (μ - q) - b * z * (ν - s) =
      a * w * ((μ - ν) - (q - s)) +
        (a - b) * w * (ν - s) + b * (w - z) * (ν - s) := by ring
  calc
    _ ≤ |a * w * ((μ - ν) - (q - s)) + (a - b) * w * (ν - s)| +
        |b * (w - z) * (ν - s)| := by rw [heq]; exact abs_add_le _ _
    _ ≤ |a * w * ((μ - ν) - (q - s))| + |(a - b) * w * (ν - s)| +
        |b * (w - z) * (ν - s)| := add_le_add (abs_add_le _ _) le_rfl
    _ ≤ 4 * w * (|μ - ν| + |q - s|) +
        (4 * G + 16 * U) * w * (|ν| + s) + 4 * (20 * G * w) * (|ν| + s) := by
      simp only [abs_mul, abs_of_nonneg hw]
      exact add_le_add (add_le_add
        (mul_le_mul (mul_le_mul_of_nonneg_right ha hw) hdiff (abs_nonneg _) (by positivity))
        (mul_le_mul (mul_le_mul_of_nonneg_right hab hw) hbase (abs_nonneg _) (by positivity)))
        (mul_le_mul (mul_le_mul hb hwz (abs_nonneg _) (by norm_num)) hbase
          (abs_nonneg _) (by positivity))
    _ = _ := by ring

/-- At every off-axis point the cross source obeys each own radial
comparison. The numerical coefficients are universal; `G` and `U` are
the finite uniform geometric and normalized mass differences. -/
theorem stab_cross_source_difference_le_c1
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    let G := (geomDist T S₁ S₂).toReal
    let U := (supDist T S₁.mu S₂.mu).toReal
    (|S₁.rUV u v - S₂.rUV u v| ≤
      4 * (S₁.lam u v / S₁.r u v) * |S₁.mu u v - S₂.mu u v| +
      4 * (S₁.lam u v / S₁.r u v) *
        |S₁.Q u v ^ 2 / S₁.r u v ^ 2 - S₂.Q u v ^ 2 / S₂.r u v ^ 2| +
      (84 * G + 16 * U) * (S₁.lam u v / S₁.r u v) *
        (|S₂.mu u v| + S₂.Q u v ^ 2 / S₂.r u v ^ 2)) ∧
    (|S₁.rUV u v - S₂.rUV u v| ≤
      4 * (-S₁.nu u v / S₁.r u v) * |S₁.mu u v - S₂.mu u v| +
      4 * (-S₁.nu u v / S₁.r u v) *
        |S₁.Q u v ^ 2 / S₁.r u v ^ 2 - S₂.Q u v ^ 2 / S₂.r u v ^ 2| +
      (84 * G + 16 * U) * (-S₁.nu u v / S₁.r u v) *
        (|S₂.mu u v| + S₂.Q u v ^ 2 / S₂.r u v ^ 2)) := by
  dsimp only
  let G := (geomDist T S₁ S₂).toReal
  let U := (supDist T S₁.mu S₂.mu).toReal
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hb₁ := h₁s.box.2 (u, v) hp
  have hb₂ := h₂s.box.2 (u, v) hp
  have hg₁ := h₁s.c1.one_sub_mu_pos _ hp
  have hg₂ := h₂s.c1.one_sub_mu_pos _ hp
  have hr := h₁s.c1.r_pos _ hp huv
  have hgeom := stab_geom_sum_le h₁s h₂s hp
  have hrad : 0 ≤ |S₁.r u v - S₂.r u v| / S₁.r u v := div_nonneg (abs_nonneg _) hr.le
  have hν : |S₁.nu u v - S₂.nu u v| ≤ G := by
    linarith only [hgeom, hrad, abs_nonneg (S₁.lam u v - S₂.lam u v)]
  have hl : |S₁.lam u v - S₂.lam u v| ≤ G := by
    linarith only [hgeom, hrad, abs_nonneg (S₁.nu u v - S₂.nu u v)]
  have hmu : |(1 - S₁.mu u v) - (1 - S₂.mu u v)| ≤ U := by
    rw [show (1 - S₁.mu u v) - (1 - S₂.mu u v) = -(S₁.mu u v - S₂.mu u v) by ring,
      abs_neg]
    exact stab_mu_sub_le h₁s h₂s hp
  have hνa : |S₁.nu u v / (1 - S₁.mu u v)| ≤ 4 := by
    rw [abs_div, abs_of_neg (h₁s.c1.nu_neg _ hp), abs_of_pos hg₁, div_le_iff₀ hg₁]
    linarith only [hb₁.2.2.2.1, hb₁.2.2.2.2.1]
  have hνb : |S₂.nu u v / (1 - S₂.mu u v)| ≤ 4 := by
    rw [abs_div, abs_of_neg (h₂s.c1.nu_neg _ hp), abs_of_pos hg₂, div_le_iff₀ hg₂]
    linarith only [hb₂.2.2.2.1, hb₂.2.2.2.2.1]
  have hla : |-S₁.lam u v / (1 - S₁.mu u v)| ≤ 4 := by
    rw [abs_div, abs_neg, abs_of_pos (h₁s.c1.lam_pos _ hp), abs_of_pos hg₁,
      div_le_iff₀ hg₁]
    linarith only [hb₁.2.1, hb₁.2.2.2.2.1]
  have hlb : |-S₂.lam u v / (1 - S₂.mu u v)| ≤ 4 := by
    rw [abs_div, abs_neg, abs_of_pos (h₂s.c1.lam_pos _ hp), abs_of_pos hg₂,
      div_le_iff₀ hg₂]
    linarith only [hb₂.2.1, hb₂.2.2.2.2.1]
  have hνd : |S₁.nu u v / (1 - S₁.mu u v) - S₂.nu u v / (1 - S₂.mu u v)| ≤
      4 * G + 16 * U := by
    apply (stab_optical_quotient_sub_le hb₁.2.2.2.2.1 hb₂.2.2.2.2.1
      (by rw [abs_of_neg (h₂s.c1.nu_neg _ hp)]; exact hb₂.2.2.2.1)).trans
    exact add_le_add (mul_le_mul_of_nonneg_left hν (by norm_num))
      (mul_le_mul_of_nonneg_left hmu (by norm_num))
  have hld : |-S₁.lam u v / (1 - S₁.mu u v) - -S₂.lam u v / (1 - S₂.mu u v)| ≤
      4 * G + 16 * U := by
    apply (stab_optical_quotient_sub_le hb₁.2.2.2.2.1 hb₂.2.2.2.2.1
      (by rw [abs_neg, abs_of_pos (h₂s.c1.lam_pos _ hp)]; exact hb₂.2.1)).trans
    rw [neg_sub_neg, abs_sub_comm]
    exact add_le_add (mul_le_mul_of_nonneg_left hl (by norm_num))
      (mul_le_mul_of_nonneg_left hmu (by norm_num))
  constructor
  · have hh := stab_cross_source_algebra
      (μ := S₁.mu u v) (ν := S₂.mu u v) (q := S₁.Q u v ^ 2 / S₁.r u v ^ 2)
      (div_nonneg (h₁s.c1.lam_pos _ hp).le hr.le)
      (div_nonneg (sq_nonneg (S₂.Q u v)) (sq_nonneg (S₂.r u v)))
      ENNReal.toReal_nonneg ENNReal.toReal_nonneg hνa hνb hνd
      (stab_out_weight_sub_le h₁s h₂s hu huv hvT)
    convert hh using 1; dsimp only [Fields.rUV]; congr 1; simp only [div_eq_mul_inv]; ring
  · have hh := stab_cross_source_algebra
      (μ := S₁.mu u v) (ν := S₂.mu u v) (q := S₁.Q u v ^ 2 / S₁.r u v ^ 2)
      (div_nonneg (neg_pos.mpr (h₁s.c1.nu_neg _ hp)).le hr.le)
      (div_nonneg (sq_nonneg (S₂.Q u v)) (sq_nonneg (S₂.r u v)))
      ENNReal.toReal_nonneg ENNReal.toReal_nonneg hla hlb hld
      (stab_in_weight_sub_le h₁s h₂s hu huv hvT)
    convert hh using 1; dsimp only [Fields.rUV]; congr 1; simp only [div_eq_mul_inv]; ring

end EmcsfAcExtension.Local
