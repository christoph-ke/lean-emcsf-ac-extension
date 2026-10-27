module

public import EmcsfAcExtension.Local.Stability.GeomStrongElectricFields
import EmcsfAcExtension.Local.Stability.GeomStrongElectricPrimitive
import EmcsfAcExtension.Local.Stability.GeomStrongSourceCoefficients

/-! # Cubic electric primitives in the classical stability box

Measurability precedes quadratic domination and absolute integrability.
The cubic outer kernel then cancels the exact radial polynomial cost.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

/-- The classical electric forcing is a.e. measurable on every closed
outgoing section. The assertion has no integrability hypothesis or
estimate constant. -/
theorem stab_electric_integrand_aemeasurable_c1
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h)
    {u v : ℝ} (hu : 0 ≤ u) (_huv : u ≤ v) (hvT : v ≤ T) :
    AEMeasurable (electricCurvatureIntegrand e S u) (volume.restrict (Icc u v)) := by
  have hm : MapsTo (fun t : ℝ => (u, t)) (Icc u v) (triangle 0 T) :=
    fun t ht => ⟨hu, ht.1, ht.2.trans hvT⟩
  have c : ContinuousOn (fun t : ℝ => (u, t)) (Icc u v) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have ar := (hset.c1.c1_r.continuousOn.comp c hm).aemeasurable (μ := volume) measurableSet_Icc
  have al := (hset.c1.c1_lam.continuousOn.comp c hm).aemeasurable (μ := volume) measurableSet_Icc
  have aq := (hset.c1.c1_Q.continuousOn.comp c hm).aemeasurable (μ := volume) measurableSet_Icc
  have aTheta := (hset.c1.c1_theta.continuousOn.comp c hm).aemeasurable (μ := volume)
      measurableSet_Icc
  have ap := (hset.c1.c1_phi.continuousOn.comp c hm).aemeasurable (μ := volume) measurableSet_Icc
  change AEMeasurable (fun t =>
    ((S.lam u t * S.Q u t ^ 2 / S.r u t ^ 2 : ℝ) : ℂ) -
      Complex.I * e * S.Q u t * S.theta u t * starRingEnd ℂ (S.phi u t))
    (volume.restrict (Icc u v))
  fun_prop

/-- Electric forcing is absolutely integrable on the complete outgoing
section by its quadratic radial majorant. No minimum-radius cutoff,
derivative supremum or unspecified bound is needed. -/
theorem stab_electric_integrand_intervalIntegrable_c1
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    IntervalIntegrable (electricCurvatureIntegrand e S u) volume u v := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le huv).2
  apply stab_quadratic_majorant_integrable huv
    (stab_electric_integrand_aemeasurable_c1 hset hu huv hvT).aestronglyMeasurable
  · intro t ht
    exact stab_electric_curvature_integrand_le_c1 hset hu ht.1 (ht.2.trans hvT)

/-- The geometric electric primitive difference has a nonsingular
explicit pointwise bound. All coefficients are universal, before the
fields, scales, data, coupling and background. The local bounds `D,X,Φ`
remain explicit for the subsequent stability closure. -/
theorem stab_geometric_electric_primitive_sub_le_c1
    {e T ε M A D X Φ : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T)
    (hD : 0 ≤ D) (hX : 0 ≤ X) (hΦ : 0 ≤ Φ)
    (hq : ∀ t ∈ Ioc u v,
      |S₁.Q u t / S₁.r u t ^ 2 - S₂.Q u t / S₂.r u t ^ 2| ≤ |e| * M * D)
    (hθ : ∀ t ∈ Ioc u v, ‖S₁.theta u t - S₂.theta u t‖ ≤ X)
    (hφ : ∀ t ∈ Ioc u v, ‖S₁.phi u t - S₂.phi u t‖ ≤ Φ) :
    let W (S : Fields) : ℂ := (2 * S.nu u v * S.lam u v /
      ((1 - S.mu u v) * S.r u v ^ 3) : ℝ)
    let G := (geomDist T S₁ S₂).toReal
    let U := (supDist T S₁.mu S₂.mu).toReal
    ‖W S₁ * (∫ t in u..v, electricCurvatureIntegrand e S₁ u t) -
      W S₂ * (∫ t in u..v, electricCurvatureIntegrand e S₂ u t)‖ ≤
      (|e| * M) ^ 2 *
        (512 * (3 * ε * D + ε * X + 11 * ε ^ 2 * G + ε ^ 2 * Φ) +
          8192 * ε ^ 2 * (G + U)) / 3 := by
  dsimp only
  let G := (geomDist T S₁ S₂).toReal
  let U := (supDist T S₁.mu S₂.mu).toReal
  let W (S : Fields) : ℂ := (2 * S.nu u v * S.lam u v /
    ((1 - S.mu u v) * S.r u v ^ 3) : ℝ)
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hU : 0 ≤ U := ENNReal.toReal_nonneg
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi u v / (S₂.nu u v : ℂ)))).trans
      (h₂s.box.2 (u, v) hp).2.2.2.2.2.1)
  have i₁ := stab_electric_integrand_intervalIntegrable_c1 h₁s hu huv.le hvT
  have i₂ := stab_electric_integrand_intervalIntegrable_c1 h₂s hu huv.le hvT
  have hb₂ t (ht : t ∈ Icc u v) : ‖electricCurvatureIntegrand e S₂ u t‖ ≤
      (2 * (|e| * M) ^ 2 * ε ^ 2) * (t - u) ^ 2 :=
    stab_electric_curvature_integrand_le_c1 h₂s hu ht.1 (ht.2.trans hvT)
  have hbδ t (ht : t ∈ Icc u v) :
      ‖electricCurvatureIntegrand e S₁ u t - electricCurvatureIntegrand e S₂ u t‖ ≤
        ((|e| * M) ^ 2 * (3 * ε * D + ε * X + 11 * ε ^ 2 * G + ε ^ 2 * Φ)) * (t - u) ^ 2 := by
    rcases ht.1.eq_or_lt with heq | hlt
    · subst t
      have ha : (u, u) ∈ triangle 0 T := ⟨hu, le_rfl, huv.le.trans hvT⟩
      simp only [electricCurvatureIntegrand, (h₁s.c1.axis u ha).1, (h₂s.c1.axis u ha).1,
        (h₁s.c1.axis u ha).2.2.1, (h₂s.c1.axis u ha).2.2.1,
        zero_pow (by decide : 2 ≠ 0), div_zero, Complex.ofReal_zero, mul_zero,
        zero_mul, norm_zero, sub_self, le_refl]
    · exact stab_electric_curvature_integrand_sub_le_c1 h₁s h₂s hu hlt (ht.2.trans hvT)
        hD hX hΦ (hq t ⟨hlt, ht.2⟩) (hθ t ⟨hlt, ht.2⟩) (hφ t ⟨hlt, ht.2⟩)
  have hc := stab_geometric_scalar_coefficients_c1 h₁s h₂s hu huv hvT
  have hw₁ : ‖W S₁‖ ≤ 512 / (v - u) ^ 3 := by
    simpa only [W, Complex.norm_real, Real.norm_eq_abs] using hc.1
  have hwδ : ‖W S₁ - W S₂‖ ≤ 4096 * (G + U) / (v - u) ^ 3 := by
    dsimp only [W]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hc.2
  have hh := stab_electric_primitive_difference_of_quadratic_bounds huv
    (by norm_num : (0 : ℝ) ≤ 512) (show 0 ≤ 4096 * (G + U) by positivity)
    (show 0 ≤ 2 * (|e| * M) ^ 2 * ε ^ 2 by positivity)
    (show 0 ≤ (|e| * M) ^ 2 *
      (3 * ε * D + ε * X + 11 * ε ^ 2 * G + ε ^ 2 * Φ) by positivity)
    i₁ i₂ hb₂ hbδ hw₁ hwδ
  apply hh.trans_eq
  ring

end EmcsfAcExtension.Local
