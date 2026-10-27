module

public import EmcsfAcExtension.Local.Broad.PotentialAlgebra

/-! # The mass and electric coefficient in scalar transport

All reciprocal gap errors are explicit. The constants depend only on
the lower gap bound and the stated bound for the electric ratio.
-/

public section

namespace EmcsfAcExtension.Local.Broad

/-- The absolute scalar transport coefficient is controlled by the sum of
the nonnegative mass and electric ratios, with exact coefficient `1/c`. -/
theorem mass_charge_coefficient_le {μ q c : ℝ} (hc : 0 < c)
    (hgap : c ≤ 1 - μ) (hμ : 0 ≤ μ) (hq : 0 ≤ q) :
    |(μ - q) / (1 - μ)| ≤ c⁻¹ * (μ + q) := by
  rw [abs_div, abs_of_pos (hc.trans_le hgap)]
  calc
    _ ≤ (μ + q) / (1 - μ) := div_le_div_of_nonneg_right
      ((abs_sub _ _).trans_eq (by rw [abs_of_nonneg hμ, abs_of_nonneg hq]))
      (hc.trans_le hgap).le
    _ ≤ (μ + q) / c := div_le_div_of_nonneg_left (add_nonneg hμ hq) hc hgap
    _ = _ := by ring

/-- The scalar coefficient difference, retaining the inverse-gap error.
The explicit coefficient `1/c + (1+Qmax)/c²` is uniform in both mass and
electric ratios. The second mass lies in `[0,1]`, and its electric ratio
lies in `[0,Qmax]`. -/
theorem mass_charge_coefficient_difference_of_bounds {μ₁ μ₂ q₁ q₂ c Qmax : ℝ}
    (hc : 0 < c) (hgap₁ : c ≤ 1 - μ₁) (hgap₂ : c ≤ 1 - μ₂)
    (hμ₂ : 0 ≤ μ₂) (hμ₂1 : μ₂ ≤ 1) (hq₂ : 0 ≤ q₂) (hq₂max : q₂ ≤ Qmax) :
    |(μ₁ - q₁) / (1 - μ₁) - (μ₂ - q₂) / (1 - μ₂)| ≤
      (c⁻¹ + (1 + Qmax) / c ^ 2) * (|μ₁ - μ₂| + |q₁ - q₂|) := by
  have hg₁ := hc.trans_le hgap₁
  have hinv := abs_inv_sub_le_of_lower hc hgap₁ hgap₂
    (X := |μ₁ - μ₂|) (by
      rw [show (1 - μ₁) - (1 - μ₂) = -(μ₁ - μ₂) by ring, abs_neg])
  have hqmax : 0 ≤ Qmax := hq₂.trans hq₂max
  have hbase : |μ₂ - q₂| ≤ 1 + Qmax := by
    apply (abs_sub _ _).trans
    rw [abs_of_nonneg hμ₂, abs_of_nonneg hq₂]
    exact add_le_add hμ₂1 hq₂max
  have hδ : |(μ₁ - q₁) - (μ₂ - q₂)| ≤ |μ₁ - μ₂| + |q₁ - q₂| := by
    calc
      _ = |(μ₁ - μ₂) - (q₁ - q₂)| := by congr 1; ring
      _ ≤ _ := abs_sub _ _
  have heq : (μ₁ - q₁) / (1 - μ₁) - (μ₂ - q₂) / (1 - μ₂) =
      ((μ₁ - q₁) - (μ₂ - q₂)) / (1 - μ₁) +
        (μ₂ - q₂) * ((1 - μ₁)⁻¹ - (1 - μ₂)⁻¹) := by ring
  rw [heq]
  calc
    _ ≤ |((μ₁ - q₁) - (μ₂ - q₂)) / (1 - μ₁)| +
        |(μ₂ - q₂) * ((1 - μ₁)⁻¹ - (1 - μ₂)⁻¹)| := abs_add_le _ _
    _ ≤ c⁻¹ * (|μ₁ - μ₂| + |q₁ - q₂|) + (1 + Qmax) * (|μ₁ - μ₂| / c ^ 2) := by
      rw [abs_div, abs_of_pos hg₁, abs_mul]
      apply add_le_add
      · calc
          _ ≤ (|μ₁ - μ₂| + |q₁ - q₂|) / (1 - μ₁) :=
            div_le_div_of_nonneg_right hδ hg₁.le
          _ ≤ (|μ₁ - μ₂| + |q₁ - q₂|) / c :=
            div_le_div_of_nonneg_left (by positivity) hc hgap₁
          _ = _ := by ring
      · exact mul_le_mul hbase hinv (abs_nonneg _) (by positivity)
    _ ≤ _ := by
      have hh := mul_nonneg (div_nonneg (by positivity : 0 ≤ 1 + Qmax) (sq_nonneg c))
        (abs_nonneg (q₁ - q₂))
      calc
        _ = (c⁻¹ + (1 + Qmax) / c ^ 2) * (|μ₁ - μ₂| + |q₁ - q₂|) -
            (1 + Qmax) / c ^ 2 * |q₁ - q₂| := by ring
        _ ≤ _ := sub_le_self _ hh

end EmcsfAcExtension.Local.Broad
