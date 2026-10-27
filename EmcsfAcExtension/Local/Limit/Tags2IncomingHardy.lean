module

public import EmcsfAcExtension.Local.Defs.Box
public import EmcsfAcExtension.Frozen.KIn
public import EmcsfAcExtension.Frozen.IsSolution
import EmcsfAcExtension.Local.Broad.BVHardy
import EmcsfAcExtension.Local.Calculus.Reconstruction
public import EmcsfAcExtension.Local.Limit.AcBridgePhase

/-! # Incoming AC Hardy absorption with the actual connection

The BV Hardy bound is converted to the norm of the covariant derivative of
an AC section. The literal frozen k identity absorbs the cubic correction.
The helpers use no classical solution assumption. charged_SF_new_version.tex:L5455–5491.
-/

public section

open Set Filter MeasureTheory Complex
open scoped ENNReal Topology

namespace EmcsfAcExtension.Local

/-- [internal] Incoming Hardy controlled by the speed of the actual parallel
representative. The exact coefficient is one, uniformly in every parameter.
The incoming AC premise is explicit in this analytic helper. -/
theorem incoming_hardy_le_covariant_of_ac {e T v : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle 0 T)) (hv : v ∈ Icc 0 T)
    (hb : AbsolutelyContinuousOnInterval (fun u => S.b u v) 0 v) :
    IntervalIntegrable (fun u => -S.nu u v / S.r u v * ‖S.xi u v / S.nu u v‖) volume 0 v ∧
      (∫ u in (0 : ℝ)..v, -S.nu u v / S.r u v * ‖S.xi u v / S.nu u v‖) ≤
        ∫ u in (0 : ℝ)..v, ‖incomingCovDeriv e S u v‖ := by
  have hseg : inSeg 0 v v ⊆ triangle 0 T := by
    rintro ⟨u,w⟩ ⟨hu, huv, rfl⟩
    exact ⟨hu, huv, hv.2⟩
  obtain ⟨hi, hh⟩ := Broad.incoming_bv_hardy_solution hS hv.1 hseg
  have hA := continuousOn_in_section hS.cont_A hseg
  have iA := hA.intervalIntegrable_of_Icc (μ := volume) hv.1
  let P (u : ℝ) := Complex.exp (I * e * ∫ s in v..u, S.A s v)
  have hangle :=
    (iA.absolutelyContinuousOnInterval_intervalIntegral_normed right_mem_uIcc).const_mul e
  have hP : AbsolutelyContinuousOnInterval P 0 v := by
    simpa only [P, Complex.ofReal_mul, mul_assoc] using hangle.unit_phase
  have hF := hP.mul_normed_ring hb
  have hder : deriv (fun u => P u * S.b u v) =ᵐ[volume.restrict (Icc 0 v)]
      (fun u => P u * incomingCovDeriv e S u v) := by
    filter_upwards [ae_restrict_of_ae iA.ae_hasDerivAt_integral,
      ae_restrict_of_ae hb.ae_differentiableAt_of_mem_uIcc,
      ae_restrict_mem measurableSet_Icc] with u hu hbu humem
    have hum : u ∈ uIcc 0 v := by rwa [uIcc_of_le hv.1]
    have hd := (((hu hum v right_mem_uIcc).ofReal_comp.const_mul (I * (e : ℂ))).cexp).mul
      (hbu hum).hasDerivAt
    simpa only [P, incomingCovDeriv, Pi.mul_def, mul_add, mul_assoc, add_comm] using hd.deriv
  refine ⟨hi, hh.trans_eq ?_⟩
  rw [hF.toReal_eVariationOn_eq_integral_norm_deriv hv.1]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le hv.1]
  filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hder] with u hu
  rw [hu, norm_mul]
  have hunit : ‖P u‖ = 1 := by
    simpa only [P, ← Complex.ofReal_mul, mul_assoc] using
      Complex.norm_exp_I_mul_ofReal (e * ∫ s in v..u, S.A s v)
  rw [hunit, one_mul]

/-- [internal] The incoming AC Hardy integral absorbs its cubic term with
coefficient `2/c`, depending only on the fixed positive geometric gap `c`.
There is no dependence on coupling, background, length or derivative suprema. -/
theorem incoming_hardy_le_envelope_of_ac {e T c Cb η M v : ℝ} {S : Fields} {K : ℝ → ℝ}
    (hc : 0 < c) (_hη : 0 ≤ η) (hsmall : η ^ 2 ≤ 1 / 2)
    (hS : IsSolution e S (triangle 0 T)) (hbox : StabBox S c Cb η M (triangle 0 T))
    (hv : v ∈ Icc 0 T) (hb : AbsolutelyContinuousOnInterval (fun u => S.b u v) 0 v)
    (hK : IntervalIntegrable K volume 0 v)
    (hdom : ∀ᵐ u ∂volume.restrict (Icc 0 v), ‖kIn e S u v‖ ≤ K u) :
    IntervalIntegrable (fun u => -S.nu u v / S.r u v * ‖S.xi u v / S.nu u v‖) volume 0 v ∧
      (∫ u in (0 : ℝ)..v, -S.nu u v / S.r u v * ‖S.xi u v / S.nu u v‖) ≤
        (2 / c) * ∫ u in (0 : ℝ)..v, K u := by
  let F u := -S.nu u v / S.r u v * ‖S.xi u v / S.nu u v‖
  have hseg : inSeg 0 v v ⊆ triangle 0 T := by
    rintro ⟨u,w⟩ ⟨hu, huv, rfl⟩
    exact ⟨hu, huv, hv.2⟩
  obtain ⟨hF, hFb⟩ := incoming_hardy_le_covariant_of_ac hS hv hb
  have hcov := (incoming_covDeriv_integral_of_ac (e := e) hv.1
    (continuousOn_in_section hS.cont_A hseg) hb).1.norm
  have hpoint : ∀ᵐ u ∂volume.restrict (Icc 0 v),
      ‖incomingCovDeriv e S u v‖ ≤ K u / c + η ^ 2 * F u := by
    rw [← restrict_Ioo_eq_restrict_Icc] at hdom ⊢
    filter_upwards [hdom, ae_restrict_mem measurableSet_Ioo] with u hu hum
    have hp : (u,v) ∈ triangle 0 T := ⟨hum.1.le, hum.2.le, hv.2⟩
    have hr := hS.r_pos (u,v) hp hum.2
    obtain ⟨_,_,hn,_,hg,hx,_⟩ := hbox.2 (u,v) hp
    have hgpos : 0 < 1 - S.mu u v := hc.trans_le hg
    have hq : 0 ≤ -S.nu u v / S.r u v := div_nonneg (hc.le.trans hn) hr.le
    let z : ℂ := S.nu u v / S.r u v * ‖S.xi u v / S.nu u v‖ ^ 2 * (S.xi u v / S.nu u v)
    have heq : ‖kIn e S u v‖ = (1 - S.mu u v) * ‖incomingCovDeriv e S u v - z‖ := by
      simp only [kIn, incomingCovDeriv, ← Complex.ofReal_one, ← Complex.ofReal_sub]
      change ‖((1 - S.mu u v : ℝ) : ℂ) * (incomingCovDeriv e S u v - z)‖ = _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hgpos]
      rfl
    have hsub : ‖incomingCovDeriv e S u v - z‖ ≤ K u / c := by
      apply (le_div_iff₀ hc).2
      calc
        _ ≤ ‖incomingCovDeriv e S u v - z‖ * (1 - S.mu u v) :=
          mul_le_mul_of_nonneg_left hg (norm_nonneg _)
        _ = ‖kIn e S u v‖ := by rw [heq, mul_comm]
        _ ≤ K u := hu
    have hz : ‖z‖ ≤ η ^ 2 * F u := by
      have hx' : ‖S.xi u v / S.nu u v‖ ≤ η :=
        (le_add_of_nonneg_left (norm_nonneg _)).trans hx
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hx' 2
      have hnneg := hS.nu_neg _ hp
      have hnorm : ‖z‖ = (-S.nu u v / S.r u v) *
          ‖S.xi u v / S.nu u v‖ ^ 2 * ‖S.xi u v / S.nu u v‖ := by
        simp only [z, ← Complex.ofReal_div, ← Complex.ofReal_pow, norm_mul,
          Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_neg hnneg,
          abs_of_pos hr, abs_of_nonneg (sq_nonneg ‖S.xi u v / S.nu u v‖)]
      rw [hnorm]
      dsimp only [F]
      convert mul_le_mul_of_nonneg_right hsq
        (mul_nonneg hq (norm_nonneg (S.xi u v / S.nu u v))) using 1; ring
    exact (norm_le_norm_sub_add (incomingCovDeriv e S u v) z).trans (add_le_add hsub hz)
  have hi := intervalIntegral.integral_mono_ae_restrict hv.1 hcov
    ((hK.div_const c).add (hF.const_mul (η ^ 2))) hpoint
  rw [intervalIntegral.integral_add (hK.div_const c) (hF.const_mul (η ^ 2)),
    intervalIntegral.integral_div, intervalIntegral.integral_const_mul] at hi
  have hF0 : 0 ≤ ∫ u in (0 : ℝ)..v, F u := by
    apply intervalIntegral.integral_nonneg hv.1
    intro u hu
    have hp : (u,v) ∈ triangle 0 T := ⟨hu.1, hu.2, hv.2⟩
    have hr0 : 0 ≤ S.r u v := by
      rcases hu.2.eq_or_lt with heq | huv
      · rw [heq, (hS.axis v ⟨hv.1,le_rfl,hv.2⟩).1]
      · exact (hS.r_pos _ hp huv).le
    exact mul_nonneg (div_nonneg (neg_nonneg.mpr (hS.nu_neg _ hp).le) hr0) (norm_nonneg _)
  have hbound : (∫ u in (0 : ℝ)..v, F u) ≤ (∫ u in (0 : ℝ)..v, K u) / c +
      η ^ 2 * ∫ u in (0 : ℝ)..v, F u := hFb.trans hi
  have hhalf := mul_le_mul_of_nonneg_right hsmall hF0
  refine ⟨hF, ?_⟩
  dsimp only [F] at hbound hF0 hhalf ⊢
  have hh : (∫ u in (0 : ℝ)..v, -S.nu u v / S.r u v * ‖S.xi u v / S.nu u v‖) ≤
      2 * ((∫ u in (0 : ℝ)..v, K u) / c) := by linarith only [hbound, hhalf]
  convert hh using 1; ring

end EmcsfAcExtension.Local
