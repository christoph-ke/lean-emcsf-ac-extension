module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux

/-! # Subtracting pure expansion derivatives

The logarithmic derivative and its quadratic correction are subtracted
before multiplication by the differing expansion coefficients.
-/

public section

namespace EmcsfAcExtension.Local

/-- Pure derivative product subtraction has coefficient one in each
error, uniformly in all inputs. No denominator or radius enters this
algebraic inequality. -/
theorem stab_pure_derivative_product_sub_le
    {a b x y f g G : ℝ} (ha : |a| ≤ 1) (hab : |a - b| ≤ G) :
    |a * (x - f) - b * (y - g)| ≤
      |x - y| + |f - g| + G * (|y| + |g|) := by
  have hG : 0 ≤ G := (abs_nonneg _).trans hab
  have heq : a * (x - f) - b * (y - g) =
      a * ((x - y) - (f - g)) + (a - b) * (y - g) := by ring
  calc
    _ ≤ |a * ((x - y) - (f - g))| + |(a - b) * (y - g)| := by
      rw [heq]
      exact abs_add_le _ _
    _ = |a| * |(x - y) - (f - g)| + |a - b| * |y - g| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * (|x - y| + |f - g|) + G * (|y| + |g|) :=
      add_le_add (mul_le_mul ha (abs_sub _ _) (abs_nonneg _) (by norm_num))
        (mul_le_mul hab (abs_sub _ _) (abs_nonneg _) hG)
    _ = _ := by ring

/-- The outgoing pure derivative difference is controlled by the
geometric renormalization, quadratic-flux difference and the second
solution's individual budget. All literal coefficients are universal.
- minimum radii and derivative suprema play no role. -/
theorem stab_pure_outgoing_difference_le_c1
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂)
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 T) :
    |pdV (triangle 0 T) S₁.lam u v - pdV (triangle 0 T) S₂.lam u v| ≤
      |geomL (triangle 0 T) S₁ u v - geomL (triangle 0 T) S₂ u v| +
      |S₁.lam u v / S₁.r u v * ‖S₁.theta u v / (S₁.lam u v : ℂ)‖ ^ 2 -
        S₂.lam u v / S₂.r u v * ‖S₂.theta u v / (S₂.lam u v : ℂ)‖ ^ 2| +
      (geomDist T S₁ S₂).toReal *
        (|geomL (triangle 0 T) S₂ u v| +
          |S₂.lam u v / S₂.r u v * ‖S₂.theta u v / (S₂.lam u v : ℂ)‖ ^ 2|) := by
  have hgeo := stab_geom_sum_le h₁s h₂s hp
  have hr : 0 ≤ |S₁.r u v - S₂.r u v| / S₁.r u v := by
    rcases hp.2.1.eq_or_lt with heq | hlt
    · change u = v at heq
      subst v
      rw [(h₁s.c1.axis u hp).1, div_zero]
    · exact div_nonneg (abs_nonneg _) (h₁s.c1.r_pos (u, v) hp hlt).le
  have hd : |S₁.lam u v - S₂.lam u v| ≤ (geomDist T S₁ S₂).toReal := by
    linarith only [hgeo, hr, abs_nonneg (S₁.nu u v - S₂.nu u v)]
  have hh := stab_pure_derivative_product_sub_le
    (x := geomL (triangle 0 T) S₁ u v) (y := geomL (triangle 0 T) S₂ u v)
    (f := S₁.lam u v / S₁.r u v * ‖S₁.theta u v / (S₁.lam u v : ℂ)‖ ^ 2)
    (g := S₂.lam u v / S₂.r u v * ‖S₂.theta u v / (S₂.lam u v : ℂ)‖ ^ 2)
    (by rw [abs_of_pos (h₁s.c1.lam_pos _ hp)]; exact (h₁s.box.2 _ hp).2.1) hd
  have id₁ : S₁.lam u v * (geomL (triangle 0 T) S₁ u v -
      S₁.lam u v / S₁.r u v * ‖S₁.theta u v / (S₁.lam u v : ℂ)‖ ^ 2) =
      pdV (triangle 0 T) S₁.lam u v := by
    rw [geomL, add_sub_cancel_right, mul_div_cancel₀ _ (h₁s.c1.lam_pos _ hp).ne']
  have id₂ : S₂.lam u v * (geomL (triangle 0 T) S₂ u v -
      S₂.lam u v / S₂.r u v * ‖S₂.theta u v / (S₂.lam u v : ℂ)‖ ^ 2) =
      pdV (triangle 0 T) S₂.lam u v := by
    rw [geomL, add_sub_cancel_right, mul_div_cancel₀ _ (h₂s.c1.lam_pos _ hp).ne']
  rwa [id₁, id₂] at hh


/-- The incoming pure derivative difference is controlled by the
geometric renormalization, quadratic-flux difference and the second
solution's individual budget. All literal coefficients are universal.
- minimum radii and derivative suprema play no role. -/
theorem stab_pure_incoming_difference_le_c1
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂)
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 T) :
    |pdU (triangle 0 T) S₁.nu u v - pdU (triangle 0 T) S₂.nu u v| ≤
      |geomN (triangle 0 T) S₁ u v - geomN (triangle 0 T) S₂ u v| +
      |(-S₁.nu u v) / S₁.r u v * ‖S₁.xi u v / (S₁.nu u v : ℂ)‖ ^ 2 -
        (-S₂.nu u v) / S₂.r u v * ‖S₂.xi u v / (S₂.nu u v : ℂ)‖ ^ 2| +
      (geomDist T S₁ S₂).toReal *
        (|geomN (triangle 0 T) S₂ u v| +
          |(-S₂.nu u v) / S₂.r u v * ‖S₂.xi u v / (S₂.nu u v : ℂ)‖ ^ 2|) := by
  have hgeo := stab_geom_sum_le h₁s h₂s hp
  have hr : 0 ≤ |S₁.r u v - S₂.r u v| / S₁.r u v := by
    rcases hp.2.1.eq_or_lt with heq | hlt
    · change u = v at heq
      subst v
      rw [(h₁s.c1.axis u hp).1, div_zero]
    · exact div_nonneg (abs_nonneg _) (h₁s.c1.r_pos (u, v) hp hlt).le
  have hd : |S₁.nu u v - S₂.nu u v| ≤ (geomDist T S₁ S₂).toReal := by
    linarith only [hgeo, hr, abs_nonneg (S₁.lam u v - S₂.lam u v)]
  have hh := stab_pure_derivative_product_sub_le
    (x := geomN (triangle 0 T) S₁ u v) (y := geomN (triangle 0 T) S₂ u v)
    (f := S₁.nu u v / S₁.r u v * ‖S₁.xi u v / (S₁.nu u v : ℂ)‖ ^ 2)
    (g := S₂.nu u v / S₂.r u v * ‖S₂.xi u v / (S₂.nu u v : ℂ)‖ ^ 2)
    (by rw [abs_of_neg (h₁s.c1.nu_neg _ hp)]; exact (h₁s.box.2 _ hp).2.2.2.1) hd
  have id₁ : S₁.nu u v * (geomN (triangle 0 T) S₁ u v -
      S₁.nu u v / S₁.r u v * ‖S₁.xi u v / (S₁.nu u v : ℂ)‖ ^ 2) =
      pdU (triangle 0 T) S₁.nu u v := by
    rw [geomN, add_sub_cancel_right, mul_div_cancel₀ _ (h₁s.c1.nu_neg _ hp).ne]
  have id₂ : S₂.nu u v * (geomN (triangle 0 T) S₂ u v -
      S₂.nu u v / S₂.r u v * ‖S₂.xi u v / (S₂.nu u v : ℂ)‖ ^ 2) =
      pdU (triangle 0 T) S₂.nu u v := by
    rw [geomN, add_sub_cancel_right, mul_div_cancel₀ _ (h₂s.c1.nu_neg _ hp).ne]
  rw [id₁, id₂] at hh
  simpa only [neg_div, neg_mul, neg_sub_neg, abs_sub_comm, abs_neg] using! hh


end EmcsfAcExtension.Local
