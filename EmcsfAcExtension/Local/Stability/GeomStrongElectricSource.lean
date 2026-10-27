module

public import EmcsfAcExtension.Local.Stability.GeomStrongElectricPrimitiveC1
public import EmcsfAcExtension.Local.Stability.GeomStrongScalarPrimitive
import EmcsfAcExtension.Local.Stability.PotentialDifferenceAlgebra
import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux
import EmcsfAcExtension.Local.Stability.DifferenceMomentsAlgebra
import EmcsfAcExtension.Local.Calculus.CurvatureIntegral

import EmcsfAcExtension.Local.Stability.ChargeDifferenceIndividual

/-! # The electromagnetic part of the geometric transport source

The electric radial primitive and explicit normalized-charge square
are kept separate. Their subtraction has a nonsingular pointwise bound.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

/-- Electromagnetic contribution to the negative geometric source,
written with the cubic outer coefficient and normalized charge. -/
@[expose] noncomputable def geometricElectricSource (e : ℝ) (S : Fields)
    (u v : ℝ) : ℂ :=
  ((2 * S.nu u v * S.lam u v / ((1 - S.mu u v) * S.r u v ^ 3) : ℝ) : ℂ) *
    (∫ t in u..v, electricCurvatureIntegrand e S u t) -
    ((2 * (2 * S.nu u v * S.lam u v / (1 - S.mu u v)) *
      (S.Q u v / S.r u v ^ 2) ^ 2 : ℝ) : ℂ)

private theorem electric_source_outer_aux (e : ℝ) (S : Fields) (u v : ℝ) :
    geometricElectricSource e S u v =
      ((2 * S.nu u v * S.lam u v / ((1 - S.mu u v) * S.r u v ^ 2) : ℝ) : ℂ) *
        curvEM e S u v -
        ((2 * (2 * S.nu u v * S.lam u v / (1 - S.mu u v)) *
          (S.Q u v / S.r u v ^ 2) ^ 2 : ℝ) : ℂ) := by
  dsimp only [geometricElectricSource, curvEM, electricCurvatureIntegrand]
  congr 1
  by_cases hr : S.r u v = 0
  · simp [hr]
  · have hrC : (S.r u v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
    push_cast
    field_simp

/-- The common real geometric source is the negative real part of its
scalar and electric primitive contributions. The equality includes the
axis and has no estimate constant or smallness premise. -/
theorem stab_geometric_source_split_c1
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    geomSource S u v = -(geometricScalarSource (triangle 0 T) S u v +
      geometricElectricSource e S u v).re := by
  rcases huv.eq_or_lt with heq | hlt
  · subst v
    have hr := (hset.c1.axis u ⟨hu, le_rfl, hvT⟩).1
    simp only [geomSource, geometricScalarSource, geometricElectricSource, hr,
      zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 3 ≠ 0),
      mul_zero, div_zero, zero_mul, neg_zero, Complex.ofReal_zero,
      Complex.zero_re, sub_self, add_zero, sub_zero]
  · rw [geomSource, Stab.curvature_radial_representation hset.c1 hu hlt hvT,
      electric_source_outer_aux, geometricScalarSource]
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    have hr := (hset.c1.r_pos (u, v) ⟨hu, hlt.le, hvT⟩ hlt).ne'
    have hg := (hset.c1.one_sub_mu_pos (u, v) ⟨hu, hlt.le, hvT⟩).ne'
    field_simp [hr, hg]; ring

/-- The full source difference is bounded by the two complex primitive
differences. The coefficient one is universal on the complete triangle.
- result no extra integral or derivative assumptions are introduced. -/
theorem stab_geometric_source_sub_le_parts_c1
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    |geomSource S₁ u v - geomSource S₂ u v| ≤
      ‖geometricScalarSource (triangle 0 T) S₁ u v - geometricScalarSource (triangle 0 T) S₂ u v‖ +
      ‖geometricElectricSource e S₁ u v - geometricElectricSource e S₂ u v‖ := by
  rw [stab_geometric_source_split_c1 h₁s hu huv hvT,
    stab_geometric_source_split_c1 h₂s hu huv hvT]
  have heq : -(geometricScalarSource (triangle 0 T) S₁ u v + geometricElectricSource e S₁ u v).re -
      -(geometricScalarSource (triangle 0 T) S₂ u v + geometricElectricSource e S₂ u v).re =
      -((geometricScalarSource (triangle 0 T) S₁ u v - geometricScalarSource (triangle 0 T) S₂ u v)
          +
        (geometricElectricSource e S₁ u v - geometricElectricSource e S₂ u v)).re := by
    simp only [Complex.add_re, Complex.sub_re]
    ring
  rw [heq, abs_neg]
  exact (Complex.abs_re_le_norm _).trans (norm_add_le _ _)

/-- The potential coefficient and its difference have universal bounds
`8` and `40(G+U)` in the literal stability box, without radius cutoffs. -/
theorem stab_geometric_electric_coefficients_c1
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    |2 * S₁.nu u v * S₁.lam u v / (1 - S₁.mu u v)| ≤ 8 ∧
    |2 * S₁.nu u v * S₁.lam u v / (1 - S₁.mu u v) -
      2 * S₂.nu u v * S₂.lam u v / (1 - S₂.mu u v)| ≤
      40 * ((geomDist T S₁ S₂).toReal + (supDist T S₁.mu S₂.mu).toReal) := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hb₁ := h₁s.box.2 (u, v) hp
  have hb₂ := h₂s.box.2 (u, v) hp
  have hg := stab_geom_sum_le h₁s h₂s hp
  have hnonneg : 0 ≤ |S₁.r u v - S₂.r u v| / S₁.r u v :=
    div_nonneg (abs_nonneg _) (h₁s.c1.r_pos (u, v) hp huv).le
  have hl₁ : |S₁.lam u v| ≤ 1 := by rw [abs_of_pos (h₁s.c1.lam_pos _ hp)]; exact hb₁.2.1
  have hl₂ : |S₂.lam u v| ≤ 1 := by rw [abs_of_pos (h₂s.c1.lam_pos _ hp)]; exact hb₂.2.1
  have hn₁ : |S₁.nu u v| ≤ 1 := by rw [abs_of_neg (h₁s.c1.nu_neg _ hp)]; exact hb₁.2.2.2.1
  have hn₂ : |S₂.nu u v| ≤ 1 := by rw [abs_of_neg (h₂s.c1.nu_neg _ hp)]; exact hb₂.2.2.2.1
  exact ⟨stab_potential_coefficient_abs_le hn₁ hl₁ hb₁.2.2.2.2.1,
    stab_potential_coefficient_sub_le hl₁ hl₂ hn₂ hb₁.2.2.2.2.1 hb₂.2.2.2.2.1
      (by linarith only [hg, hnonneg]) (stab_mu_sub_le h₁s h₂s hp)⟩

/-- The explicit electric charge-square source has the pointwise cost
`E²[32εD+80ε²(G+U)]`, where `E=|e|M`. The coefficients are universal,
uniformly in the fields and all scale parameters. -/
theorem stab_electric_charge_square_sub_le_c1
    {e T ε M A D : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) (_hD : 0 ≤ D)
    (hq : |S₁.Q u v / S₁.r u v ^ 2 - S₂.Q u v / S₂.r u v ^ 2| ≤ |e| * M * D) :
    |2 * (2 * S₁.nu u v * S₁.lam u v / (1 - S₁.mu u v)) * (S₁.Q u v / S₁.r u v ^ 2) ^ 2 -
      2 * (2 * S₂.nu u v * S₂.lam u v / (1 - S₂.mu u v)) * (S₂.Q u v / S₂.r u v ^ 2) ^ 2| ≤
      (|e| * M) ^ 2 * (32 * ε * D + 80 * ε ^ 2 *
        ((geomDist T S₁ S₂).toReal + (supDist T S₁.mu S₂.mu).toReal)) := by
  let E := |e| * M
  let q₁ := S₁.Q u v / S₁.r u v ^ 2
  let q₂ := S₂.Q u v / S₂.r u v ^ 2
  let B₁ := 2 * S₁.nu u v * S₁.lam u v / (1 - S₁.mu u v)
  let B₂ := 2 * S₂.nu u v * S₂.lam u v / (1 - S₂.mu u v)
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi u v / (S₂.nu u v : ℂ)))).trans
      (h₂s.box.2 (u, v) hp).2.2.2.2.2.1)
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans h₁s.box.1
  have hE : 0 ≤ E := mul_nonneg (abs_nonneg _) hM
  have hq₁ : |q₁| ≤ E * ε := by
    simpa only [q₁, E, abs_div, abs_pow, sq_abs] using stab_charge_ratio_le h₁s hu huv hvT
  have hq₂ : |q₂| ≤ E * ε := by
    simpa only [q₂, E, abs_div, abs_pow, sq_abs] using stab_charge_ratio_le h₂s hu huv hvT
  have hsq : |q₁ ^ 2 - q₂ ^ 2| ≤ 2 * (E * ε) * (E * D) := by
    have hh := stab_norm_sq_sub_le (z := (q₁ : ℂ)) (w := (q₂ : ℂ))
      (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hq₁)
      (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hq₂)
    simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hq (by positivity))
  have hq₂sq : q₂ ^ 2 ≤ (E * ε) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg q₂) hq₂ 2
  have hc := stab_geometric_electric_coefficients_c1 h₁s h₂s hu huv hvT
  have heq : 2 * B₁ * q₁ ^ 2 - 2 * B₂ * q₂ ^ 2 =
      2 * (B₁ * (q₁ ^ 2 - q₂ ^ 2) + (B₁ - B₂) * q₂ ^ 2) := by ring
  change |2 * B₁ * q₁ ^ 2 - 2 * B₂ * q₂ ^ 2| ≤ _
  rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply (mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num : (0 : ℝ) ≤ 2)).trans
  simp only [abs_mul, abs_pow, sq_abs]
  apply (mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul hc.1 hsq (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 8))
    (mul_le_mul hc.2 hq₂sq (sq_nonneg _) (by positivity))) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq
  dsimp only [E]
  ring

end EmcsfAcExtension.Local
