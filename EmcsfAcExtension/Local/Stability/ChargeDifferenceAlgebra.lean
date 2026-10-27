module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Subtraction of the oscillatory charge current

The moving radial measure and the two complex factors are subtracted
at the same labels, before any primitive or change of radius is used.
-/

public section

namespace EmcsfAcExtension.Local

/-- The outgoing area weight has the relative difference bound `8G`.
The numerical coefficient is universal for the literal fixed box. -/
theorem stab_area_weight_sub_le {a b r s G : ℝ}
    (ha : 1 / 4 ≤ a) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hr : 0 < r)
    (hab : |a - b| ≤ G) (hrs : |r - s| / r ≤ G) :
    |a * r - b * s| ≤ 8 * G * (a * r) := by
  have hG : 0 ≤ G := (abs_nonneg _).trans hab
  have hrr : |r - s| ≤ G * r := (div_le_iff₀ hr).mp hrs
  have heq : a * r - b * s = (a - b) * r + b * (r - s) := by ring
  calc
    _ ≤ |(a - b) * r| + |b * (r - s)| := by rw [heq]; exact abs_add_le _ _
    _ = |a - b| * r + b * |r - s| := by
      rw [abs_mul, abs_mul, abs_of_pos hr, abs_of_nonneg hb0]
    _ ≤ G * r + b * (G * r) :=
      add_le_add (mul_le_mul_of_nonneg_right hab hr.le) (mul_le_mul_of_nonneg_left hrr hb0)
    _ ≤ G * r + G * r := add_le_add le_rfl (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hb1 (mul_nonneg hG hr.le))
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right (show 2 ≤ 8 * a by linarith only [ha])
        (mul_nonneg hG hr.le)
      nlinarith only [hh]

/-- The imaginary scalar current is Lipschitz in both factors, with
literal coefficient `1` uniformly in the values and all norm bounds. -/
theorem stab_scalar_current_sub_le {p q x y : ℂ} {M ε X Φ : ℝ}
    (hp : ‖p‖ ≤ M) (hy : ‖y‖ ≤ ε)
    (hxy : ‖x - y‖ ≤ X) (hpq : ‖p - q‖ ≤ Φ) :
    |(starRingEnd ℂ p * x).im - (starRingEnd ℂ q * y).im| ≤ M * X + ε * Φ := by
  have hM : 0 ≤ M := (norm_nonneg p).trans hp
  have hΦ : 0 ≤ Φ := (norm_nonneg (p - q)).trans hpq
  have heq : starRingEnd ℂ p * x - starRingEnd ℂ q * y =
      starRingEnd ℂ p * (x - y) + starRingEnd ℂ (p - q) * y := by
    simp only [map_sub]
    ring
  calc
    _ ≤ ‖starRingEnd ℂ p * x - starRingEnd ℂ q * y‖ := by
      simpa only [Complex.sub_im] using
        Complex.abs_im_le_norm (starRingEnd ℂ p * x - starRingEnd ℂ q * y)
    _ ≤ ‖starRingEnd ℂ p * (x - y)‖ + ‖starRingEnd ℂ (p - q) * y‖ := by
      rw [heq]
      exact norm_add_le _ _
    _ = ‖p‖ * ‖x - y‖ + ‖p - q‖ * ‖y‖ := by
      rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
    _ ≤ M * X + Φ * ε := add_le_add
      (mul_le_mul hp hxy (norm_nonneg _) hM) (mul_le_mul hpq hy (norm_nonneg _) hΦ)
    _ = _ := by ring

/-- The full oscillatory charge density difference retains the scalar
ratio, scalar field and area-weight differences. The only geometric
coefficient is the universal number `8`. -/
theorem stab_charge_density_sub_le
    {p q x y : ℂ} {a b G M ε X Φ : ℝ}
    (ha : 0 ≤ a) (hp : ‖p‖ ≤ M) (hq : ‖q‖ ≤ M) (hy : ‖y‖ ≤ ε)
    (hxy : ‖x - y‖ ≤ X) (hpq : ‖p - q‖ ≤ Φ)
    (hab : |a - b| ≤ 8 * G * a) :
    |a * (starRingEnd ℂ p * x).im - b * (starRingEnd ℂ q * y).im| ≤
      a * (M * X + ε * Φ + 8 * G * M * ε) := by
  have hM : 0 ≤ M := (norm_nonneg p).trans hp
  have hε : 0 ≤ ε := (norm_nonneg y).trans hy
  have hIm : |(starRingEnd ℂ q * y).im| ≤ M * ε := by
    apply (Complex.abs_im_le_norm _).trans
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul hq hy (norm_nonneg _) hM
  have heq : a * (starRingEnd ℂ p * x).im - b * (starRingEnd ℂ q * y).im =
      a * ((starRingEnd ℂ p * x).im - (starRingEnd ℂ q * y).im) +
        (a - b) * (starRingEnd ℂ q * y).im := by ring
  calc
    _ ≤ |a * ((starRingEnd ℂ p * x).im - (starRingEnd ℂ q * y).im)| +
        |(a - b) * (starRingEnd ℂ q * y).im| := by rw [heq]; exact abs_add_le _ _
    _ = a * |(starRingEnd ℂ p * x).im - (starRingEnd ℂ q * y).im| +
        |a - b| * |(starRingEnd ℂ q * y).im| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha]
    _ ≤ a * (M * X + ε * Φ) + (8 * G * a) * (M * ε) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (stab_scalar_current_sub_le hp hy hxy hpq) ha
      · exact mul_le_mul hab hIm (abs_nonneg _) ((abs_nonneg _).trans hab)
    _ = _ := by ring

end EmcsfAcExtension.Local
