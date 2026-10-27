module

public import EmcsfAcExtension.Global.Calculus.Normalized
public import EmcsfAcExtension.Global.Defs.Renormalized
import EmcsfAcExtension.Infra.Density.ParamIntegral
import EmcsfAcExtension.Infra.AC.Variation
import EmcsfAcExtension.Infra.AC.Quotient
import EmcsfAcExtension.Local.Calculus.Sections
import EmcsfAcExtension.Local.Algebra.Radial
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! # Weak differentiation of characteristic integral equations

Outgoing derivatives are first treated on rectangles. Uniform characteristic
variation gives product integrability; Fubini then differentiates the incoming
integral equation without restricting any product-a.e. density to a curve.
The initial density is fixed before the incoming time is varied.
-/

public section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global.Calculus

/-- [internal] Clamping extends a continuous rectangular field to a globally
continuous one, without changing its values on the rectangle. -/
theorem exists_continuous_rectangle_extension {f : ℝ → ℝ → ℂ} {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hf : ContinuousOn f.uncurry (Icc a b ×ˢ Icc c d)) :
    ∃ F : ℝ → ℝ → ℂ, Continuous F.uncurry ∧
      EqOn F.uncurry f.uncurry (Icc a b ×ˢ Icc c d) := by
  let π : ℝ × ℝ → ℝ × ℝ := fun p => (min (max a p.1) b, min (max c p.2) d)
  have hπ : Continuous π := by fun_prop
  have hm (p : ℝ × ℝ) : π p ∈ Icc a b ×ˢ Icc c d :=
    ⟨⟨le_min (le_max_left _ _) hab, min_le_right _ _⟩,
      ⟨le_min (le_max_left _ _) hcd, min_le_right _ _⟩⟩
  refine ⟨fun u v => f.uncurry (π (u, v)), hf.comp_continuous hπ hm, ?_⟩
  rintro ⟨u, v⟩ ⟨hu, hv⟩
  simp only [Function.uncurry, π, max_eq_right hu.1, min_eq_left hu.2,
    max_eq_right hv.1, min_eq_left hv.2]

/-- [internal] Equal rectangular representatives have the same outgoing
ordinary derivative at every outgoing interior label, uniformly in the row. -/
theorem outgoing_deriv_eq_of_eqOn_rectangle {f F : ℝ → ℝ → ℂ} {a b c d u v : ℝ}
    (heq : EqOn F.uncurry f.uncurry (Icc a b ×ˢ Icc c d))
    (hu : u ∈ Icc a b) (hv : v ∈ Ioo c d) : deriv (F u) v = deriv (f u) v := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioo_mem_nhds hv.1 hv.2] with t ht
  exact heq (show (u, t) ∈ Icc a b ×ˢ Icc c d from ⟨hu, Ioo_subset_Icc_self ht⟩)

/-- [internal] The outgoing derivative of a continuous rectangular field is
jointly a.e. strongly measurable. Clamping constructs a global continuous
extension; its outgoing derivative agrees on the outgoing interior. -/
theorem aestronglyMeasurable_outgoing_deriv_of_continuousOn
    {f : ℝ → ℝ → ℂ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c < d)
    (hf : ContinuousOn f.uncurry (Icc a b ×ˢ Icc c d)) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => deriv (f p.1) p.2)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
  let U : ℝ → ℝ := fun x => min (max a x) b
  let V : ℝ → ℝ := fun x => min (max c x) d
  have hU : Continuous U := (continuous_const.max continuous_id).min continuous_const
  have hV : Continuous V := (continuous_const.max continuous_id).min continuous_const
  have hUm (x : ℝ) : U x ∈ Icc a b :=
    ⟨le_min (le_max_left _ _) hab, min_le_right _ _⟩
  have hVm (x : ℝ) : V x ∈ Icc c d :=
    ⟨le_min (le_max_left _ _) hcd.le, min_le_right _ _⟩
  let F : ℝ → ℝ → ℂ := fun u v => f (U u) (V v)
  have hF : Continuous F.uncurry := hf.comp_continuous
    ((hU.comp continuous_fst).prodMk (hV.comp continuous_snd))
    (fun p => ⟨hUm p.1, hVm p.2⟩)
  have hgood : ∀ᵐ p ∂(volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)),
      p ∈ Icc a b ×ˢ Ioo c d := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.prod measurableSet_Ioo)).2
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact (ae_restrict_mem measurableSet_Ioo).mono fun v hv => ⟨hu, hv⟩
  apply (stronglyMeasurable_deriv_with_param hF).aestronglyMeasurable.congr
  filter_upwards [hgood] with p hp
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioo_mem_nhds hp.2.1 hp.2.2] with v hv
  simp only [F, U, V, max_eq_right hp.1.1, min_eq_left hp.1.2,
    max_eq_right hv.1.le, min_eq_left hv.2.le]

/-- [internal] Uniform finite row variation makes the actual outgoing
derivative integrable on the rectangle. The bound `B` belongs to this
rectangle and field; no terminal uniformity or L² density is asserted. -/
theorem integrable_outgoing_deriv_of_uniform_variation
    {f : ℝ → ℝ → ℂ} {a b c d : ℝ} {B : ℝ≥0∞}
    (hab : a ≤ b) (hcd : c < d)
    (hf : ContinuousOn f.uncurry (Icc a b ×ˢ Icc c d)) (hB : B < ⊤)
    (hvar : ∀ u ∈ Icc a b, eVariationOn (f u) (Icc c d) ≤ B) :
    Integrable (fun p : ℝ × ℝ => deriv (f p.1) p.2)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
  have hm := aestronglyMeasurable_outgoing_deriv_of_continuousOn hab hcd hf
  have hbv (u : ℝ) (hu : u ∈ Icc a b) : BoundedVariationOn (f u) (Icc c d) :=
    ne_top_of_le_ne_top hB.ne (hvar u hu)
  apply (integrable_prod_iff hm).2
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hcd.le).1
      ((hbv u hu).intervalIntegrable_deriv_finiteDimensional hcd.le)
  · apply Integrable.mono' (integrableOn_const (C := B.toReal) measure_Icc_lt_top.ne)
      hm.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    calc
      (∫ v in Icc c d, ‖deriv (f u) v‖) = ∫ v in c..d, ‖deriv (f u) v‖ := by
        rw [intervalIntegral.integral_of_le hcd.le, integral_Icc_eq_integral_Ioc]
      _ ≤ (eVariationOn (f u) (Icc c d)).toReal := (hbv u hu).integral_norm_deriv_le hcd.le
      _ ≤ B.toReal := ENNReal.toReal_mono hB.ne (hvar u hu)

/-- [internal] The rough normalized outgoing derivative is product-integrable
on every compact rectangle in the frozen class. The local variation bound
is obtained from `IsSolution.bv_loc`, rather than assumed separately. -/
theorem integrable_normalized_outgoing_deriv {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a b c d : ℝ} (hab : a ≤ b) (hcd : c < d)
    (hrect : Icc a b ×ˢ Icc c d ⊆ D) :
    Integrable (fun p : ℝ × ℝ => deriv (S.a p.1) p.2)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
  obtain ⟨B, hB, hout, _⟩ := hS.bv_loc _ hrect (isCompact_Icc.prod isCompact_Icc)
  apply integrable_outgoing_deriv_of_uniform_variation hab hcd
    ((continuousOn_a hS).mono hrect) hB
  intro u hu
  exact (hout u c d (fun p hp => ⟨by simpa only [hp.1] using hu, hp.2⟩)).2.2.1

/-- [internal] The displayed differentiated forcing is jointly continuous
on any positive-radius subset of a solution. Its construction uses no
outgoing derivative of a normalized field. -/
theorem continuousOn_rawDensitySource {e : ℝ} {S : Fields} {D K : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hK : K ⊆ D ∩ {p | p.1 < p.2}) :
    ContinuousOn (Function.uncurry (rawDensitySource e S)) K := by
  have cr := hS.cont_r.mono (fun p hp => (hK hp).1)
  have cl := hS.cont_lam.mono (fun p hp => (hK hp).1)
  have cn := hS.cont_nu.mono (fun p hp => (hK hp).1)
  have cm := hS.cont_m.mono (fun p hp => (hK hp).1)
  have cQ := hS.cont_Q.mono (fun p hp => (hK hp).1)
  have cp := hS.cont_phi.mono (fun p hp => (hK hp).1)
  have ct := hS.cont_theta.mono (fun p hp => (hK hp).1)
  have hr (p : ℝ × ℝ) (hp : p ∈ K) := (hS.r_pos p (hK hp).1 (hK hp).2).ne'
  have hl (p : ℝ × ℝ) (hp : p ∈ K) := (hS.lam_pos p (hK hp).1).ne'
  have cmu : ContinuousOn (Function.uncurry S.mu) K :=
    (continuousOn_const.mul cm).div cr hr
  have cg : ContinuousOn (fun p : ℝ × ℝ => 1 - S.mu p.1 p.2) K :=
    continuousOn_const.sub cmu
  have hg (p : ℝ × ℝ) (hp : p ∈ K) := (hS.one_sub_mu_pos p (hK hp).1).ne'
  have cy : ContinuousOn (fun p : ℝ × ℝ => S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ)) K :=
    ct.div (Complex.continuous_ofReal.comp_continuousOn cl)
      (fun p hp => Complex.ofReal_ne_zero.mpr (hl p hp))
  have cq : ContinuousOn (fun p : ℝ × ℝ => S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2) K :=
    (cQ.pow 2).div (cr.pow 2) (fun p hp => pow_ne_zero _ (hr p hp))
  have cB : ContinuousOn (fun p : ℝ × ℝ =>
      S.lam p.1 p.2 * (-S.nu p.1 p.2) / ((1 - S.mu p.1 p.2) * S.r p.1 p.2 ^ 2)) K :=
    (cl.mul cn.neg).div (cg.mul (cr.pow 2))
      (fun p hp => mul_ne_zero (hg p hp) (pow_ne_zero _ (hr p hp)))
  change ContinuousOn (fun p : ℝ × ℝ => rawDensitySource e S p.1 p.2) K
  dsimp only [rawDensitySource]
  fun_prop

/-- [internal] The normalized incoming source in the product form used for
weak outgoing differentiation. This is a rearrangement of denominators,
without a regularity or nonvanishing premise. -/
theorem normalized_incoming_source_eq (e : ℝ) (S : Fields) (u v : ℝ) :
    (-(S.nu u v : ℂ) / S.r u v) *
      (((S.mu u v : ℂ) - S.Q u v ^ 2 / (S.r u v : ℂ) ^ 2) /
        (1 - S.mu u v) * (S.theta u v / S.lam u v) +
        I * e * S.Q u v * S.phi u v / (1 - S.mu u v)) - I * e * S.A u v * S.a u v =
      (-S.nu u v / ((1 - S.mu u v) * S.r u v) : ℝ) *
        (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) * (S.a u v - S.phi u v) +
        I * e * (-S.nu u v / ((1 - S.mu u v) * S.r u v) : ℝ) * S.Q u v * S.phi u v -
        I * e * S.A u v * S.a u v := by
  simp only [Fields.a, add_sub_cancel_left]
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- [internal] The real density coefficient cancels the incoming expansion
equation. This identity holds even at zero denominators under Lean's field
conventions; its application is on positive-radius characteristic segments. -/
theorem density_coefficient_mul_lam (S : Fields) (u v : ℝ) :
    S.rUV u v +
      (-S.nu u v / ((1 - S.mu u v) * S.r u v) *
        (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2)) * S.lam u v = 0 := by
  simp only [Fields.rUV, div_eq_mul_inv, mul_inv_rev]
  ring

/-- [internal] The coefficient of the sole rough density is continuous on
positive-radius subsets, directly from the undifferentiated frozen fields. -/
theorem continuousOn_density_coefficient {e : ℝ} {S : Fields} {D K : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hK : K ⊆ D ∩ {p | p.1 < p.2}) :
    ContinuousOn (fun p : ℝ × ℝ =>
      ((-S.nu p.1 p.2 / ((1 - S.mu p.1 p.2) * S.r p.1 p.2) *
        (S.mu p.1 p.2 - S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2) : ℝ) : ℂ) -
      I * e * S.A p.1 p.2) K := by
  have cr := hS.cont_r.mono (fun p hp => (hK hp).1)
  have cn := hS.cont_nu.mono (fun p hp => (hK hp).1)
  have cm := hS.cont_m.mono (fun p hp => (hK hp).1)
  have cQ := hS.cont_Q.mono (fun p hp => (hK hp).1)
  have cA := hS.cont_A.mono (fun p hp => (hK hp).1)
  have hr (p : ℝ × ℝ) (hp : p ∈ K) := (hS.r_pos p (hK hp).1 (hK hp).2).ne'
  have hg (p : ℝ × ℝ) (hp : p ∈ K) := (hS.one_sub_mu_pos p (hK hp).1).ne'
  have cmu : ContinuousOn (Function.uncurry S.mu) K :=
    (continuousOn_const.mul cm).div cr hr
  have cP := cn.neg.div ((continuousOn_const.sub cmu).mul cr)
    (fun p hp => mul_ne_zero (hg p hp) (hr p hp))
  have cB := cmu.sub ((cQ.pow 2).div (cr.pow 2) (fun p hp => pow_ne_zero _ (hr p hp)))
  exact (Complex.continuous_ofReal.comp_continuousOn (cP.mul cB)).sub
    ((continuousOn_const.mul continuousOn_const).mul
      (Complex.continuous_ofReal.comp_continuousOn cA))

/-- [internal] Differentiate the ordinary incoming normalized source along
an outgoing AC row. The only rough term is the first outgoing derivative of
`a`; its coefficient and the remaining `rawDensitySource` are derivative-free.
This is the sectional product-rule calculation in internal project record (W3)–(W4). -/
theorem normalized_source_out_section {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    let P : ℝ → ℝ := fun v => -S.nu u v / ((1 - S.mu u v) * S.r u v)
    let B : ℝ → ℝ := fun v => S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2
    let G : ℝ → ℂ := fun v => P v * B v * (S.a u v - S.phi u v) +
      I * e * P v * S.Q u v * S.phi u v - I * e * S.A u v * S.a u v
    AbsolutelyContinuousOnInterval G a b ∧
      ∀ᵐ v ∂volume.restrict (Icc a b), HasDerivAt G
        ((P v * B v - I * e * S.A u v) * deriv (S.a u) v + rawDensitySource e S u v) v := by
  let P : ℝ → ℝ := fun v => -S.nu u v / ((1 - S.mu u v) * S.r u v)
  let B : ℝ → ℝ := fun v => S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2
  have h := Local.IsSolution.out_section hS hua hab hs
  have mem (v : ℝ) (hv : v ∈ Icc a b) : (u, v) ∈ D := hs ⟨rfl, hv.1, hv.2⟩
  have hr (v : ℝ) (hv : v ∈ Icc a b) :=
    (hS.r_pos (u, v) (mem v hv) (hua.trans_le hv.1)).ne'
  have hg (v : ℝ) (hv : v ∈ Icc a b) := (hS.one_sub_mu_pos (u, v) (mem v hv)).ne'
  have hl (v : ℝ) (hv : v ∈ Icc a b) := (hS.lam_pos (u, v) (mem v hv)).ne'
  have acmu : AbsolutelyContinuousOnInterval (S.mu u) a b :=
    ac_div_of_ne_zero (h.2.2.1.1.const_mul 2) h.1.1
      (fun v hv => hr v (by simpa [uIcc_of_le hab] using hv))
  have acg : AbsolutelyContinuousOnInterval (fun v => 1 - S.mu u v) a b :=
    (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval.sub acmu
  have acP : AbsolutelyContinuousOnInterval P a b :=
    ac_div_of_ne_zero h.2.1.1.neg (acg.mul h.1.1)
      (fun v hv => mul_ne_zero (hg v (by simpa [uIcc_of_le hab] using hv))
        (hr v (by simpa [uIcc_of_le hab] using hv)))
  have acB : AbsolutelyContinuousOnInterval B a b := by
    simpa only [B, pow_two] using! acmu.sub
      (ac_div_of_ne_zero (h.2.2.2.1.1.mul h.2.2.2.1.1) (h.1.1.mul h.1.1)
        (fun v hv => mul_ne_zero (hr v (by simpa [uIcc_of_le hab] using hv))
          (hr v (by simpa [uIcc_of_le hab] using hv))))
  have aca := (hS.ac_out u a b hab hs).2.2.2.2
  have acG := ((acP.ofReal.mul_normed_ring acB.ofReal).mul_normed_ring
    (aca.sub h.2.2.2.2.2.1.1)).add
      ((((acP.ofReal.const_smul (I * e)).mul_normed_ring h.2.2.2.1.1.ofReal).mul_normed_ring
        h.2.2.2.2.2.1.1)) |>.sub
          ((h.2.2.2.2.1.1.ofReal.const_smul (I * e)).mul_normed_ring aca)
  refine ⟨by simpa only [smul_eq_mul, P, B, pow_two, Complex.ofReal_mul] using! acG, ?_⟩
  have haa := (ae_restrict_iff' measurableSet_Icc).2 (by
    simpa only [uIcc_of_le hab] using aca.ae_differentiableAt_of_mem_uIcc)
  filter_upwards [h.1.2, h.2.1.2, h.2.2.1.2, h.2.2.2.1.2,
    h.2.2.2.2.1.2, h.2.2.2.2.2.1.2, haa, ae_restrict_mem measurableSet_Icc]
    with v hrv hnv hmv hQv hAv hpv hav hv
  let y := S.theta u v / (S.lam u v : ℂ)
  let q := S.Q u v ^ 2 / S.r u v ^ 2
  let j := (starRingEnd ℂ (S.phi u v) * y).im
  have dmu : HasDerivAt (S.mu u)
      (S.lam u v / S.r u v * ((1 - S.mu u v) * ‖y‖ ^ 2 + q - S.mu u v)) v := by
    apply ((hmv.const_mul 2).div hrv (hr v hv)).congr_deriv
    calc
      _ = 2 * S.mV u v / S.r u v - 2 * S.m u v * S.lam u v / S.r u v ^ 2 := by
        field_simp [hr v hv]
      _ = _ := Local.Stab.outgoing_mu_derivative_identity_algebra
        (hr v hv) (hl v hv) (show S.mV u v = _ from rfl)
  have dP : HasDerivAt P (S.lam u v * P v / S.r u v * (‖y‖ ^ 2 - 1)) v := by
    apply (hnv.neg.div (((hasDerivAt_const v (1 : ℝ)).sub dmu).mul hrv)
      (mul_ne_zero (hg v hv) (hr v hv))).congr_deriv
    simp only [P, q, Fields.rUV, Pi.mul_apply, Pi.sub_apply, Pi.neg_apply]
    field_simp [hr v hv, hg v hv]
    ring
  have dQ : HasDerivAt (S.Q u) (-e * S.r u v * S.lam u v * j) v := by
    apply hQv.congr_deriv
    dsimp [Fields.QV, j, y]
    rw [← mul_div_assoc, Complex.div_ofReal_im]
    field_simp [hl v hv]
  have dp : HasDerivAt (S.phi u) (S.lam u v * y / S.r u v) v := by
    apply hpv.congr_deriv
    dsimp [Fields.phiV, y]
    field_simp [Complex.ofReal_ne_zero.mpr (hl v hv)]
  have dB : HasDerivAt B
      (S.lam u v / S.r u v *
        ((1 - S.mu u v) * ‖y‖ ^ 2 - S.mu u v + 3 * q + 2 * e * S.Q u v * j)) v := by
    apply (dmu.sub ((dQ.pow 2).div (hrv.pow 2) (pow_ne_zero _ (hr v hv)))).congr_deriv
    simp only [q, Pi.pow_apply]
    field_simp [hr v hv]
    ring
  have hd := (((dP.ofReal_comp.mul dB.ofReal_comp).mul (hav.hasDerivAt.sub dp)).add
    ((((dP.ofReal_comp.const_mul (I * e)).mul dQ.ofReal_comp).mul dp))).sub
      (((hAv.ofReal_comp.const_mul (I * e)).mul hav.hasDerivAt))
  have hscale : S.lam u v * (-S.nu u v) / ((1 - S.mu u v) * S.r u v ^ 2) =
      S.lam u v * P v / S.r u v := by
    dsimp only [P]
    field_simp
  have hAV : S.AV u v = -2 * S.lam u v * P v * S.Q u v / S.r u v := by
    dsimp only [Fields.AV, P]
    field_simp
  change HasDerivAt
    (fun t => (P t : ℂ) * (B t : ℂ) * (S.a u t - S.phi u t) +
      I * e * P t * S.Q u t * S.phi u t - I * e * S.A u t * S.a u t)
    (((P v : ℂ) * (B v : ℂ) - I * e * S.A u v) * deriv (S.a u) v +
      rawDensitySource e S u v) v
  apply hd.congr_deriv
  simp only [Pi.mul_apply, Pi.sub_apply]
  dsimp only [rawDensitySource]
  have hy : S.theta u v / (S.lam u v : ℂ) = y := rfl
  have hq : S.Q u v ^ 2 / S.r u v ^ 2 = q := rfl
  have hj : (starRingEnd ℂ (S.phi u v) * y).im = j := rfl
  have hBv : B v = S.mu u v - q := rfl
  simp only [Fields.a, add_sub_cancel_left, hy, hq, hj, hBv, hAV, hscale]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr (hr v hv)]
  ring

/-- [internal] Fubini identifies the outgoing primitive of the incoming
integral equation at every point. The initial derivative is one fixed L¹
density. Both integral-form premises are discharged by characteristic
equations in the field-level consumer. -/
theorem primitive_identity_of_characteristic_forms
    {f G H : ℝ → ℝ → ℂ} {a b c d : ℝ} (_hab : a ≤ b) (hcd : c ≤ d)
    (hf₀ : AbsolutelyContinuousOnInterval (f a) c d)
    (hH : Integrable H.uncurry
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))))
    (hin : ∀ v ∈ Icc c d, ∀ u ∈ Icc a b,
      IntegralForm (fun s => f s v) (fun s => G s v) a u)
    (hout : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d, IntegralForm (G u) (H u) c v) :
    ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      f u v = f u c + ∫ t in c..v, deriv (f a) t + ∫ s in a..u, H s t := by
  intro u hu v hv
  have hsubu : uIcc a u ⊆ Icc a b := by
    rw [uIcc_of_le hu.1]
    exact Icc_subset_Icc le_rfl hu.2
  have hsubv : uIcc c v ⊆ Icc c d := by
    rw [uIcc_of_le hv.1]
    exact Icc_subset_Icc le_rfl hv.2
  have hHrect : IntegrableOn H.uncurry (uIoc a u ×ˢ uIoc c v) := by
    have hh : IntegrableOn H.uncurry (Icc a b ×ˢ Icc c d) := by
      simpa only [IntegrableOn, Measure.prod_restrict, ← Measure.volume_eq_prod] using! hH
    exact hh.mono_set (prod_mono (uIoc_subset_uIcc.trans hsubu)
      (uIoc_subset_uIcc.trans hsubv))
  have hswap := Density.integral_integral_swap_rectangle hHrect
  have hHuv : Integrable H.uncurry
      ((volume.restrict (uIoc a u)).prod (volume.restrict (Icc c d))) :=
    hH.mono_measure (Measure.prod_mono
      (Measure.restrict_mono (uIoc_subset_uIcc.trans hsubu) le_rfl) le_rfl)
  have hHi : IntervalIntegrable (fun t => ∫ s in a..u, H s t) volume c d := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hcd).2
    simpa only [Function.uncurry, intervalIntegral.integral_of_le hu.1,
      uIoc_of_le hu.1] using! hHuv.integral_prod_right
  have hI : (∫ s in a..u, G s v - G s c) =
      ∫ t in c..v, ∫ s in a..u, H s t := by
    rw [← hswap]
    apply intervalIntegral.integral_congr
    intro s hs
    exact (hout s (hsubu hs) v hv).2
  have hGs := intervalIntegral.integral_sub (hin v hv u hu).1
    (hin c ⟨le_rfl, hcd⟩ u hu).1
  have hv' : v ∈ uIcc c d := by rwa [uIcc_of_le hcd]
  have hinit := (hf₀.mono (uIcc_subset_uIcc left_mem_uIcc hv')).integral_deriv_eq_sub_complex
  rw [intervalIntegral.integral_add
    (hf₀.intervalIntegrable_deriv_complex.mono_set (uIcc_subset_uIcc left_mem_uIcc hv'))
    (hHi.mono_set (uIcc_subset_uIcc left_mem_uIcc hv')), hinit, ← hI, hGs,
    ← (hin v hv u hu).2, ← (hin c ⟨le_rfl, hcd⟩ u hu).2]
  abel

end EmcsfAcExtension.Global.Calculus
