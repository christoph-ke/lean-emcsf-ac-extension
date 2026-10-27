/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Global.Defs.Observation
public import EmcsfAcExtension.Global.Cooling.VariationMeasure
import EmcsfAcExtension.Infra.AC.Quotient
import EmcsfAcExtension.Infra.AC.Variation
import EmcsfAcExtension.Global.Calculus.Gauge

/-! # Square-root energy growth from the cylinder identity

Regularize the normalized energy by a positive constant, apply the AC
chain rule, integrate, and pass to zero (`charged_SF_new_version.tex:L2874–L2913`).
The conditional algebra remains available for compatibility; `Cylinder.lean`
discharges the identity from the landed observation-energy calculus.
-/

public section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global.Cooling

private theorem ac_sqrt_add {E : ℝ → ℝ} {s t κ : ℝ}
    (hE : AbsolutelyContinuousOnInterval E s t) (hκ : 0 < κ)
    (hn : ∀ x ∈ uIcc s t, 0 ≤ E x) :
    AbsolutelyContinuousOnInterval (fun x => Real.sqrt (E x + κ)) s t := by
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => κ) s t :=
    (LipschitzWith.const κ).lipschitzOnWith.absolutelyContinuousOnInterval
  have hlog := (hE.fun_add hconst).log_of_pos_le hκ (by
    intro x hx
    exact le_add_of_nonneg_left (hn x hx))
  apply ((hlog.const_mul (1 / 2 : ℝ)).exp).congr
  intro x hx
  dsimp only
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by linarith [hn x hx])]
  congr 1
  ring

/-- [internal] Divide the exact cylinder identity by its fixed positive
radius. This is the normalization at `charged_SF_new_version.tex:L2874–L2882`;
its only analytic input is AC of the undivided energy. -/
theorem _root_.EmcsfAcExtension.Global.charged_cool_identity_of_cylinder {Q D F : ℝ → ℝ} {b s t : ℝ}
    (hb : 0 < b) (hst : s ≤ t) (hQ : AbsolutelyContinuousOnInterval Q s t)
    (hid : ∀ᵐ x ∂volume.restrict (Icc s t), deriv Q x + D x / 2 = b * F x) :
    AbsolutelyContinuousOnInterval (fun x => Q x / b) s t ∧
      ∀ᵐ x ∂volume.restrict (Icc s t),
        deriv (fun y => Q y / b) x + D x / (2 * b) = F x := by
  refine ⟨by simpa only [div_eq_mul_inv, mul_comm] using hQ.const_mul b⁻¹, ?_⟩
  have hae : ∀ᵐ x ∂volume.restrict (Icc s t), DifferentiableAt ℝ Q x := by
    apply (ae_restrict_iff' measurableSet_Icc).2
    simpa only [uIcc_of_le hst] using hQ.ae_differentiableAt
  filter_upwards [hid, hae] with x hx hdx
  rw [(hdx.hasDerivAt.div_const b).deriv]
  field_simp [hb.ne']
  nlinarith only [hx]

/-- [internal] Abstract AC square-root growth with the exact universal
coefficient `1 / sqrt 2`. No duration or size bound enters this estimate. -/
theorem sqrt_growth_of_ae_deriv_le {E g : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hE : AbsolutelyContinuousOnInterval E s t)
    (hg : IntervalIntegrable g volume s t)
    (hn : ∀ x ∈ Icc s t, 0 ≤ E x) (hgn : ∀ x ∈ Icc s t, 0 ≤ g x)
    (hd : ∀ᵐ x ∂volume.restrict (Icc s t),
      deriv E x ≤ Real.sqrt (2 * E x) * g x) :
    Real.sqrt (E t) ≤ Real.sqrt (E s) + (∫ x in s..t, g x) / Real.sqrt 2 := by
  have htwo : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have htwo_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hreg (κ : ℝ) (hκ : 0 < κ) :
      Real.sqrt (E t + κ) ≤ Real.sqrt (E s + κ) +
        (∫ x in s..t, g x) / Real.sqrt 2 := by
    have hn' : ∀ x ∈ uIcc s t, 0 ≤ E x := by
      simpa only [uIcc_of_le hst] using hn
    have hF := ac_sqrt_add hE hκ hn'
    have hderiv : ∀ᵐ x ∂volume.restrict (Icc s t),
        deriv (fun y => Real.sqrt (E y + κ)) x ≤ g x / Real.sqrt 2 := by
      have hae : ∀ᵐ x ∂volume.restrict (Icc s t), DifferentiableAt ℝ E x := by
        apply (ae_restrict_iff' measurableSet_Icc).2
        simpa only [uIcc_of_le hst] using hE.ae_differentiableAt_of_mem_uIcc
      filter_upwards [hd, hae, ae_restrict_mem measurableSet_Icc] with x hx hdx hxm
      have hp : 0 < E x + κ := by linarith [hn x hxm]
      rw [((hdx.hasDerivAt.add_const κ).sqrt hp.ne').deriv]
      have hroot : Real.sqrt (2 * E x) = Real.sqrt 2 * Real.sqrt (E x) :=
        Real.sqrt_mul (by norm_num) _
      have hmono := Real.sqrt_le_sqrt (le_add_of_nonneg_right hκ.le : E x ≤ E x + κ)
      have hspos := Real.sqrt_pos.2 hp
      have hquot : (Real.sqrt (2 * E x) * g x) / (2 * Real.sqrt (E x + κ)) ≤
          g x / Real.sqrt 2 := by
        apply (div_le_div_iff₀ (by positivity : 0 < 2 * Real.sqrt (E x + κ)) htwo).2
        rw [hroot]
        have he : (Real.sqrt 2 * Real.sqrt (E x) * g x) * Real.sqrt 2 =
            2 * (Real.sqrt (E x) * g x) := by
          calc
            _ = Real.sqrt 2 ^ 2 * (Real.sqrt (E x) * g x) := by ring
            _ = _ := by rw [htwo_sq]
        rw [he]
        nlinarith only [mul_nonneg (hgn x hxm) (sub_nonneg.mpr hmono)]
      exact (div_le_div_of_nonneg_right hx (by positivity)).trans hquot
    have hi : (∫ x in s..t, deriv (fun y => Real.sqrt (E y + κ)) x) ≤
        ∫ x in s..t, g x / Real.sqrt 2 := by
      apply intervalIntegral.integral_mono_ae_restrict hst hF.intervalIntegrable_deriv
        (hg.div_const _)
      exact hderiv
    rw [hF.integral_deriv_eq_sub, intervalIntegral.integral_div] at hi
    linarith
  have hk : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have ht : Tendsto (fun n : ℕ => Real.sqrt (E t + 1 / (n + 1))) atTop
      (𝓝 (Real.sqrt (E t + 0))) := (tendsto_const_nhds.add hk).sqrt
  have hs : Tendsto (fun n : ℕ => Real.sqrt (E s + 1 / (n + 1)) +
      (∫ x in s..t, g x) / Real.sqrt 2) atTop
      (𝓝 (Real.sqrt (E s + 0) + (∫ x in s..t, g x) / Real.sqrt 2)) :=
    ((tendsto_const_nhds.add hk).sqrt).add_const _
  simpa only [add_zero] using le_of_tendsto_of_tendsto' ht hs
    (fun n => hreg (1 / (n + 1)) (by positivity))

/-- [internal] Scalar endpoint form of square-root propagation, with the
universal coefficients `2,1`. This uses no observation window. -/
theorem cooling_time_propagation_of_square_root {q₀ q₁ σ : ℝ} (h₀ : 0 ≤ q₀) (h₁ : 0 ≤ q₁)
    (hσ : 0 ≤ σ) (hroot : Real.sqrt q₁ ≤ Real.sqrt q₀ + σ / Real.sqrt 2) :
    q₁ ≤ 2 * q₀ + σ ^ 2 := by
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg q₁) (by positivity)).2 hroot
  have hsum : (Real.sqrt q₀ + σ / Real.sqrt 2) ^ 2 ≤
      2 * Real.sqrt q₀ ^ 2 + 2 * (σ / Real.sqrt 2) ^ 2 := by
    nlinarith only [sq_nonneg (Real.sqrt q₀ - σ / Real.sqrt 2)]
  have hc : 2 * (σ / Real.sqrt 2) ^ 2 = σ ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  rw [Real.sq_sqrt h₀, hc] at hsum
  rw [Real.sq_sqrt h₁] at hsq
  exact hsq.trans hsum

/-- [internal] Squaring the square-root estimate gives the universal
unfinished-stage energy bound, with no observation premise. -/
theorem supremum_energy_bound_of_square_root {q : ℝ → ℝ} {s t σ : ℝ}
    (hq : ∀ x ∈ Icc s t, 0 ≤ q x) (hs : s ≤ t) (hσ : 0 ≤ σ)
    (hroot : ∀ x ∈ Icc s t, Real.sqrt (q x) ≤ Real.sqrt (q s) + σ / Real.sqrt 2) :
    ∀ x ∈ Icc s t, q x ≤ 2 * q s + σ ^ 2 := by
  intro x hx
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg (q x)) (by positivity)).2 (hroot x hx)
  have hsum : (Real.sqrt (q s) + σ / Real.sqrt 2) ^ 2 ≤
      2 * Real.sqrt (q s) ^ 2 + 2 * (σ / Real.sqrt 2) ^ 2 := by
    nlinarith only [sq_nonneg (Real.sqrt (q s) - σ / Real.sqrt 2)]
  have hc : 2 * (σ / Real.sqrt 2) ^ 2 = σ ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  rw [Real.sq_sqrt (hq s (left_mem_Icc.mpr hs)), hc] at hsum
  rw [Real.sq_sqrt (hq x hx)] at hsq
  exact hsq.trans hsum

/-- [internal] Normalized charged energy is nonnegative and dominates half
the squared outgoing scalar ratio. The numerical constants are universal. -/
theorem normalized_energy_lower {S : Fields} {b u v : ℝ} (hb : 0 < b)
    (hmu : 0 ≤ S.mu u v ∧ S.mu u v < 1) :
    0 ≤ cylinderEnergy S b u v / b ∧
      ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 ≤ 2 * (cylinderEnergy S b u v / b) := by
  have hl := Real.log_le_sub_one_of_pos (sub_pos.mpr hmu.2)
  have heq : cylinderEnergy S b u v / b =
      (‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 - Real.log (1 - S.mu u v)) / 2 := by
    rw [cylinderEnergy_def]
    field_simp
  rw [heq]
  constructor <;> nlinarith only [hl, hmu.1, sq_nonneg ‖S.theta u v / (S.lam u v : ℂ)‖]

end Cooling

/-- [internal] The architecture's square-root interface, conditional only
on the AC cylinder identity from internal project record. Its covariant-AC premise is required
by internal project record. The coefficient is universal and does not use observation. -/
theorem Observation.square_root_energy_of_cylinder (ui e b s t : ℝ) (S : Fields)
    (h : OriginalData ui e S) (hb : 0 < b) (hst : s < t)
    (γ : ClockCylinder S (origDomain ui) b s t)
    (hac : AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V s) s t)
    (hcylinder :
      AbsolutelyContinuousOnInterval
        (fun x => cylinderEnergy S b (γ.U x) (γ.V x) / b) s t ∧
      ∀ᵐ x ∂volume.restrict (Icc s t),
        deriv (fun y => cylinderEnergy S b (γ.U y) (γ.V y) / b) x +
          ‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ) -
            S.xi (γ.U x) (γ.V x) / (S.nu (γ.U x) (γ.V x) : ℂ)‖ ^ 2 / (2 * b) =
          (starRingEnd ℂ (curveParallel e S
            (fun u v => S.theta u v / (S.lam u v : ℂ)) γ.U γ.V s x) *
              deriv (curveParallel e S S.a γ.U γ.V s) x).re) :
    ENNReal.ofReal (Real.sqrt (cylinderEnergy S b (γ.U t) (γ.V t) / b)) ≤
      ENNReal.ofReal (Real.sqrt (cylinderEnergy S b (γ.U s) (γ.V s) / b)) +
      ENNReal.ofReal (1 / Real.sqrt 2) * curveCovVar e S S.a γ.U γ.V s t := by
  let E := fun x => cylinderEnergy S b (γ.U x) (γ.V x) / b
  let g := fun x => ‖deriv (curveParallel e S S.a γ.U γ.V s) x‖
  have hn (x : ℝ) (hx : x ∈ Icc s t) :=
    Cooling.normalized_energy_lower hb (h.mu _ (γ.mem x hx))
  have hd : ∀ᵐ x ∂volume.restrict (Icc s t), deriv E x ≤ Real.sqrt (2 * E x) * g x := by
    filter_upwards [hcylinder.2, ae_restrict_mem measurableSet_Icc] with x hx hxm
    have hy : ‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ≤
        Real.sqrt (2 * E x) := by
      exact Real.le_sqrt_of_sq_le (hn x hxm).2
    have hp := Complex.re_le_norm (starRingEnd ℂ (curveParallel e S
      (fun u v => S.theta u v / (S.lam u v : ℂ)) γ.U γ.V s x) *
        deriv (curveParallel e S S.a γ.U γ.V s) x)
    rw [norm_mul, Complex.norm_conj, Calculus.norm_curveParallel] at hp
    have hp' := hp.trans (mul_le_mul_of_nonneg_right hy (norm_nonneg _))
    have hD : 0 ≤ ‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ) -
        S.xi (γ.U x) (γ.V x) / (S.nu (γ.U x) (γ.V x) : ℂ)‖ ^ 2 / (2 * b) := by
      positivity
    dsimp only [E, g] at *
    linarith
  have hg := hac.intervalIntegrable_deriv_finiteDimensional.norm
  have hroot := Cooling.sqrt_growth_of_ae_deriv_le hst.le hcylinder.1 hg
    (fun x hx => (hn x hx).1) (fun _ _ => norm_nonneg _) hd
  have hintn : 0 ≤ ∫ x in s..t, ‖deriv (curveParallel e S S.a γ.U γ.V s) x‖ :=
    intervalIntegral.integral_nonneg hst.le (fun _ _ => norm_nonneg _)
  rw [curveCovVar_def, hac.eVariationOn_eq_integral_norm_deriv hst.le,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / Real.sqrt 2),
    ← ENNReal.ofReal_add (Real.sqrt_nonneg _) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  simpa only [E, g, div_eq_mul_inv, mul_comm, one_mul] using hroot

end EmcsfAcExtension.Global
