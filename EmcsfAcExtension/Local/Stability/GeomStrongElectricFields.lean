module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeomStrongElectricAlgebra
import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux
import EmcsfAcExtension.Local.Stability.ChargeDifferenceIndividual
import EmcsfAcExtension.Local.Stability.PotentialDifferenceAlgebra

/-! # Quadratic radial vanishing of electric curvature differences

The normalized charge comparison is used before the two radii and
scalar factors are subtracted. The forcing remains quadratically small
at the regular axis.
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- The electromagnetic integrand of the outgoing curvature primitive.
It is totalized at the regular axis, as in the frozen source formula. -/
@[expose] noncomputable def electricCurvatureIntegrand (e : ℝ) (S : Fields)
    (u v : ℝ) : ℂ :=
  ((S.lam u v * S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) : ℂ) -
    Complex.I * e * S.Q u v * S.theta u v * starRingEnd ℂ (S.phi u v)

private theorem electric_normalization_aux (e l q r : ℝ) (z p : ℂ) (hr : r ≠ 0) :
    ((l * q ^ 2 / r ^ 2 : ℝ) : ℂ) - Complex.I * e * q * z * starRingEnd ℂ p =
      ((r ^ 2 : ℝ) : ℂ) *
        (((l * (q / r ^ 2) ^ 2 : ℝ) : ℂ) -
          Complex.I * e * (q / r ^ 2) * z * starRingEnd ℂ p) := by
  push_cast
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  field_simp

/-- An individual electric forcing has the universal quadratic bound
`2 (|e|M)² ε² (v-u)²`, before all fields, data and scales. -/
theorem stab_electric_curvature_integrand_le_c1
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    ‖electricCurvatureIntegrand e S u v‖ ≤
      2 * (|e| * M) ^ 2 * ε ^ 2 * (v - u) ^ 2 := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv, hvT⟩
  rcases huv.eq_or_lt with heq | hlt
  · subst v
    simp only [electricCurvatureIntegrand, (hset.c1.axis u hp).1,
      zero_pow (by decide : 2 ≠ 0), div_zero, Complex.ofReal_zero,
      (hset.c1.axis u hp).2.2.1, Complex.ofReal_zero, mul_zero, zero_mul, sub_zero, norm_zero]
    positivity
  · have hr := hset.c1.r_pos (u, v) hp hlt
    have hb := hset.box.2 (u, v) hp
    have hε : 0 ≤ ε := (norm_nonneg _).trans
      ((le_add_of_nonneg_right (norm_nonneg (S.xi u v / (S.nu u v : ℂ)))).trans
        hb.2.2.2.2.2.1)
    have hθ : ‖S.theta u v‖ ≤ ε := by
      have hx : ‖S.theta u v / (S.lam u v : ℂ)‖ ≤ ε :=
        (le_add_of_nonneg_right (norm_nonneg _)).trans hb.2.2.2.2.2.1
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hset.c1.lam_pos _ hp)] at hx
      exact ((div_le_iff₀ (hset.c1.lam_pos _ hp)).mp hx).trans
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hb.2.1 hε)
    have hn := stab_electric_integrand_norm_le
      (e := e) (l := S.lam u v) (q := S.Q u v / S.r u v ^ 2)
      (z := S.theta u v) (p := S.phi u v)
      (show 0 ≤ M from (by norm_num : (0 : ℝ) ≤ 1).trans hset.box.1) hε
      (by rw [abs_of_pos (hset.c1.lam_pos _ hp)]; exact hb.2.1)
      (by simpa only [abs_div, abs_pow, sq_abs] using stab_charge_ratio_le hset hu hlt hvT)
      hθ hb.2.2.2.2.2.2
    rw [electricCurvatureIntegrand, electric_normalization_aux e _ _ _ _ _ hr.ne',
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_pow, sq_abs]
    have hn' := hn
    simp only [Complex.ofReal_div, Complex.ofReal_pow] at hn'
    have hR := (stab_radius_bounds hset hu huv hvT).2
    calc
      _ ≤ S.r u v ^ 2 * (2 * (|e| * M) ^ 2 * ε ^ 2) :=
        mul_le_mul_of_nonneg_left hn' (sq_nonneg _)
      _ ≤ (v - u) ^ 2 * (2 * (|e| * M) ^ 2 * ε ^ 2) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le hR 2) (by positivity)
      _ = _ := by ring

/-- The radius-square error is bounded relatively with universal
coefficient `5`. No lower bound on either positive radius is fixed. -/
theorem stab_radius_sq_sub_le {r s G : ℝ} (hr : 0 < r) (hs : 0 ≤ s)
    (hc : s ≤ 4 * r) (hrel : |r - s| / r ≤ G) :
    |r ^ 2 - s ^ 2| ≤ 5 * G * r ^ 2 := by
  have hG : 0 ≤ G := (div_nonneg (abs_nonneg _) hr.le).trans hrel
  have hd : |r - s| ≤ G * r := (div_le_iff₀ hr).mp hrel
  have hsum : r + s ≤ 5 * r := by linarith only [hc]
  rw [show r ^ 2 - s ^ 2 = (r - s) * (r + s) by ring,
    abs_mul, abs_of_nonneg (add_nonneg hr.le hs)]
  apply (mul_le_mul hd hsum (add_nonneg hr.le hs) (mul_nonneg hG hr.le)).trans_eq
  ring

/-- Local electric forcing subtraction retains the normalized charge,
scalar derivative, scalar field and geometric errors. The coefficients
`3,1,11,1` are universal, with every radial factor explicit. -/
theorem stab_electric_curvature_integrand_sub_le_c1
    {e T ε M A D X Φ : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T)
    (hD : 0 ≤ D) (hX : 0 ≤ X) (hΦ : 0 ≤ Φ)
    (hq : |S₁.Q u v / S₁.r u v ^ 2 - S₂.Q u v / S₂.r u v ^ 2| ≤ |e| * M * D)
    (hθ : ‖S₁.theta u v - S₂.theta u v‖ ≤ X)
    (hφ : ‖S₁.phi u v - S₂.phi u v‖ ≤ Φ) :
    ‖electricCurvatureIntegrand e S₁ u v - electricCurvatureIntegrand e S₂ u v‖ ≤
      (|e| * M) ^ 2 * (3 * ε * D + ε * X +
        11 * ε ^ 2 * (geomDist T S₁ S₂).toReal + ε ^ 2 * Φ) * (v - u) ^ 2 := by
  let G := (geomDist T S₁ S₂).toReal
  let ψ (S : Fields) : ℂ := ((S.lam u v * (S.Q u v / S.r u v ^ 2) ^ 2 : ℝ) : ℂ) -
    Complex.I * e * ((S.Q u v / S.r u v ^ 2 : ℝ) : ℂ) * S.theta u v * starRingEnd ℂ (S.phi u v)
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hb₁ := h₁s.box.2 (u, v) hp
  have hb₂ := h₂s.box.2 (u, v) hp
  have hr₁ := h₁s.c1.r_pos (u, v) hp huv
  have hr₂ := h₂s.c1.r_pos (u, v) hp huv
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi u v / (S₂.nu u v : ℂ)))).trans
      hb₂.2.2.2.2.2.1)
  have hl₁ : |S₁.lam u v| ≤ 1 := by rw [abs_of_pos (h₁s.c1.lam_pos _ hp)]; exact hb₁.2.1
  have hl₂ : |S₂.lam u v| ≤ 1 := by rw [abs_of_pos (h₂s.c1.lam_pos _ hp)]; exact hb₂.2.1
  have ht (S : Fields) (hs : StabSetting e T ε M A S h₁) : ‖S.theta u v‖ ≤ ε := by
    have hb := hs.box.2 (u, v) hp
    have hx := (le_add_of_nonneg_right (norm_nonneg (S.xi u v / (S.nu u v : ℂ)))).trans
      hb.2.2.2.2.2.1
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hs.c1.lam_pos _ hp)] at hx
    exact ((div_le_iff₀ (hs.c1.lam_pos _ hp)).mp hx).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hb.2.1 hε)
  have ht₂ : ‖S₂.theta u v‖ ≤ ε := by
    have hx := (le_add_of_nonneg_right (norm_nonneg (S₂.xi u v / (S₂.nu u v : ℂ)))).trans
      hb₂.2.2.2.2.2.1
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (h₂s.c1.lam_pos _ hp)] at hx
    exact ((div_le_iff₀ (h₂s.c1.lam_pos _ hp)).mp hx).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hb₂.2.1 hε)
  have hg := stab_geom_sum_le h₁s h₂s hp
  have hrel : |S₁.r u v - S₂.r u v| / S₁.r u v ≤ G := by
    linarith only [hg, abs_nonneg (S₁.lam u v - S₂.lam u v), abs_nonneg (S₁.nu u v - S₂.nu u v)]
  have hld : |S₁.lam u v - S₂.lam u v| ≤ G := by
    linarith only [hg, abs_nonneg (S₁.nu u v - S₂.nu u v), div_nonneg (abs_nonneg (S₁.r u v - S₂.r u
        v)) hr₁.le]
  have hq₁ : |S₁.Q u v / S₁.r u v ^ 2| ≤ |e| * M * ε := by
    simpa only [abs_div, abs_pow, sq_abs] using stab_charge_ratio_le h₁s hu huv hvT
  have hq₂ : |S₂.Q u v / S₂.r u v ^ 2| ≤ |e| * M * ε := by
    simpa only [abs_div, abs_pow, sq_abs] using stab_charge_ratio_le h₂s hu huv hvT
  have hψ := stab_electric_integrand_sub_le h₁s.box.1 hε hD hX hΦ hG hl₁ hld
    hq₁ hq₂ hq (ht S₁ h₁s) ht₂ hθ hb₁.2.2.2.2.2.2 hφ
  have hψ₂ := stab_electric_integrand_norm_le
    ((by norm_num : (0 : ℝ) ≤ 1).trans h₂s.box.1) hε hl₂ hq₂ ht₂ hb₂.2.2.2.2.2.2
  have hψ₂' : ‖ψ S₂‖ ≤ 2 * (|e| * M) ^ 2 * ε ^ 2 := by
    simpa only [ψ] using! hψ₂
  have hrD := stab_radius_sq_sub_le hr₁ hr₂.le (stab_radius_compare h₁s h₂s hu huv.le hvT).2 hrel
  have heq : electricCurvatureIntegrand e S₁ u v - electricCurvatureIntegrand e S₂ u v =
      ((S₁.r u v ^ 2 : ℝ) : ℂ) * (ψ S₁ - ψ S₂) +
      ((S₁.r u v ^ 2 - S₂.r u v ^ 2 : ℝ) : ℂ) * ψ S₂ := by
    simp only [electricCurvatureIntegrand, electric_normalization_aux e _ _ _ _ _ hr₁.ne',
      electric_normalization_aux e _ _ _ _ _ hr₂.ne', ψ, Complex.ofReal_sub]
    push_cast
    ring
  rw [heq]
  calc
    _ ≤ S₁.r u v ^ 2 * ‖ψ S₁ - ψ S₂‖ + |S₁.r u v ^ 2 - S₂.r u v ^ 2| * ‖ψ S₂‖ := by
      have hh := norm_add_le (((S₁.r u v ^ 2 : ℝ) : ℂ) * (ψ S₁ - ψ S₂))
        (((S₁.r u v ^ 2 - S₂.r u v ^ 2 : ℝ) : ℂ) * ψ S₂)
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_sq] at hh
      exact hh
    _ ≤ S₁.r u v ^ 2 * ((|e| * M) ^ 2 * (3 * ε * D + ε * X + ε ^ 2 * G + ε ^ 2 * Φ)) +
        (5 * G * S₁.r u v ^ 2) * (2 * (|e| * M) ^ 2 * ε ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hψ (sq_nonneg _))
        (mul_le_mul hrD hψ₂' (norm_nonneg _) (by positivity))
    _ = S₁.r u v ^ 2 * ((|e| * M) ^ 2 * (3 * ε * D + ε * X + 11 * ε ^ 2 * G + ε ^ 2 * Φ)) := by ring
    _ ≤ (v - u) ^ 2 * ((|e| * M) ^ 2 * (3 * ε * D + ε * X + 11 * ε ^ 2 * G + ε ^ 2 * Φ)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr₁.le (stab_radius_bounds h₁s hu huv.le hvT).2
          2)
        (by positivity)
    _ = _ := by ring

end EmcsfAcExtension.Local
