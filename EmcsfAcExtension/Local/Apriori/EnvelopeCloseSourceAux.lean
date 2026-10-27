module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseFields
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity
import EmcsfAcExtension.Infra.Triangle
import EmcsfAcExtension.Infra.Null.Parametric

/-! # Measurability and integration order for scalar transport sources

The scalar primitives retain their literal outgoing and incoming orientations.
The zero extension permits Tonelli on the triangle before using a
characteristic variation bound, as required by `charged_SF_new_version.tex:L4695–L4730`.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- Both section orders equal the plane integral on the triangle when the
zero extension is measurable. The equalities allow infinite integrals and
introduce no estimate constant. -/
theorem triangle_lintegral_orders {s : ℝ} {F : ℝ × ℝ → ℝ≥0∞}
    (hF : Measurable ((triangle 0 s).indicator F)) :
    (∫⁻ p in triangle 0 s, F p ∂(volume.prod volume)) =
      (∫⁻ u in Icc 0 s, ∫⁻ v in Icc u s, F (u, v)) ∧
    (∫⁻ p in triangle 0 s, F p ∂(volume.prod volume)) =
      (∫⁻ v in Icc 0 s, ∫⁻ u in Icc 0 v, F (u, v)) := by
  have hout := lintegral_triangle_eq_lintegral_lintegral (a := 0) (b := s) hF
  have hin := lintegral_triangle_eq_lintegral_lintegral_symm (a := 0) (b := s) hF
  rw [setLIntegral_indicator (measurableSet_triangle 0 s), inter_self] at hout hin
  constructor
  · apply hout.trans
    apply setLIntegral_congr_fun measurableSet_Icc
    intro u hu
    apply setLIntegral_congr_fun measurableSet_Icc
    intro v hv
    exact indicator_of_mem (show (u, v) ∈ triangle 0 s from ⟨hu.1, hv.1, hv.2⟩) F
  · apply hin.trans
    apply setLIntegral_congr_fun measurableSet_Icc
    intro v hv
    apply setLIntegral_congr_fun measurableSet_Icc
    intro u hu
    exact indicator_of_mem (show (u, v) ∈ triangle 0 s from ⟨hu.1, hu.2, hv.2⟩) F

/-- Tonelli on the triangle needs measurability only of the zero extension
of the density. This identity is exact and allows infinite integrals. -/
theorem swap_triangle_lintegral_of_measurable_extension
    {s : ℝ} {F : ℝ × ℝ → ℝ≥0∞}
    (hF : Measurable ((triangle 0 s).indicator F)) :
    (∫⁻ u in Icc 0 s, ∫⁻ v in Icc u s, F (u, v)) =
      ∫⁻ v in Icc 0 s, ∫⁻ u in Icc 0 v, F (u, v) := by
  have hout : (∫⁻ u in Icc 0 s, ∫⁻ v in Icc u s, F (u, v)) =
      ∫⁻ u in Icc 0 s, ∫⁻ v in Icc u s, (triangle 0 s).indicator F (u, v) := by
    apply setLIntegral_congr_fun measurableSet_Icc
    intro u hu
    apply setLIntegral_congr_fun measurableSet_Icc
    intro v hv
    exact (indicator_of_mem (show (u, v) ∈ triangle 0 s from ⟨hu.1, hv.1, hv.2⟩) F).symm
  have hin : (∫⁻ v in Icc 0 s, ∫⁻ u in Icc 0 v, F (u, v)) =
      ∫⁻ v in Icc 0 s, ∫⁻ u in Icc 0 v, (triangle 0 s).indicator F (u, v) := by
    apply setLIntegral_congr_fun measurableSet_Icc
    intro v hv
    apply setLIntegral_congr_fun measurableSet_Icc
    intro u hu
    exact (indicator_of_mem (show (u, v) ∈ triangle 0 s from ⟨hu.1, hu.2, hv.2⟩) F).symm
  rw [hout, hin]
  exact lintegral_lintegral_swap_triangle hF

private theorem scalar_primitive_continuous {e s : ℝ} {S : Fields}
    (hs : 0 < s) (hS : IsC1Solution e S (triangle 0 s)) :
    ContinuousOn (Function.uncurry (curvScalar (triangle 0 s) S))
      (triangle 0 s ∩ {p : ℝ × ℝ | p.1 < p.2}) ∧
    ContinuousOn (Function.uncurry (curvScalarIn e (triangle 0 s) S))
      (triangle 0 s ∩ {p : ℝ × ℝ | p.1 < p.2}) := by
  let D := triangle 0 s
  let O := D ∩ {p : ℝ × ℝ | p.1 < p.2}
  have cr := Complex.continuous_ofReal.comp_continuousOn hS.c1_r.continuousOn
  have cn := Complex.continuous_ofReal.comp_continuousOn hS.c1_nu.continuousOn
  have cl := Complex.continuous_ofReal.comp_continuousOn hS.c1_lam.continuousOn
  have cy := hS.c1_theta.continuousOn.div cl
    (fun p hp => Complex.ofReal_ne_zero.mpr (hS.lam_pos p hp).ne')
  have cz := hS.c1_xi.continuousOn.div cn
    (fun p hp => Complex.ofReal_ne_zero.mpr (hS.nu_neg p hp).ne)
  let Fj := fun u v => (S.r u v : ℂ) * starRingEnd ℂ (S.xi u v / S.nu u v) *
    jC1 D S u v
  let Fk := fun u v => (S.r u v : ℂ) * starRingEnd ℂ (S.theta u v / S.lam u v) *
    kC1 e D S u v
  have cj : ContinuousOn (Function.uncurry Fj) D :=
    (cr.mul cz.star).mul (continuousOn_jC1_aux hs hS)
  have ck : ContinuousOn (Function.uncurry Fk) D :=
    (cr.mul cy.star).mul (continuousOn_kC1_aux hs hS)
  have cpj := continuousOn_integral_outgoing cj
  have cpk := continuousOn_integral_incoming ck
  have cpk' : ContinuousOn (fun p : ℝ × ℝ => ∫ x in p.1..p.2, Fk x p.2) D := by
    have cd := cpk.comp (continuous_snd.prodMk continuous_snd).continuousOn
      (show MapsTo (fun p : ℝ × ℝ => (p.2, p.2)) D D from
        fun p hp => ⟨hp.1.trans hp.2.1, le_rfl, hp.2.2⟩)
    apply (cd.sub cpk).congr
    intro p hp
    have hi : IntervalIntegrable (fun x => Fk x p.2) volume 0 p.2 :=
      (ck.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun x hx => ⟨hx.1, hx.2, hp.2.2⟩)).intervalIntegrable_of_Icc
          (hp.1.trans hp.2.1)
    have hi' := hi.mono_set (show uIcc 0 p.1 ⊆ uIcc 0 p.2 from by
      rw [uIcc_of_le hp.1, uIcc_of_le (hp.1.trans hp.2.1)]
      exact Icc_subset_Icc le_rfl hp.2.1)
    exact (intervalIntegral.integral_interval_sub_left hi hi').symm
  have hr (p : ℝ × ℝ) (hp : p ∈ O) : (S.r p.1 p.2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hS.r_pos p hp.1 hp.2).ne'
  have cri := (continuousOn_const (c := (1 : ℂ))).div
    (cr.mono (show O ⊆ D from inter_subset_left)) hr
  constructor
  · apply (cri.mul (cpj.mono (show O ⊆ D from inter_subset_left))).congr
    intro p hp
    change curvScalar (triangle 0 s) S p.1 p.2 =
      (1 : ℂ) / S.r p.1 p.2 * ∫ x in p.1..p.2, Fj p.1 x
    simp only [curvScalar, Fj, D, one_div]
  · apply (cri.mul (cpk'.mono (show O ⊆ D from inter_subset_left))).neg.congr
    intro p hp
    change curvScalarIn e (triangle 0 s) S p.1 p.2 =
      -((1 : ℂ) / S.r p.1 p.2 * ∫ x in p.1..p.2, Fk x p.2)
    simp only [curvScalarIn, Fk, D, one_div]

/-- The two scalar curvature transport densities have measurable zero
extensions. The primitives keep the different null orientations of ruling
internal project record. No source integrability or closed-envelope estimate is assumed. -/
theorem measurable_scalar_transport {e s : ℝ} {S : Fields}
    (hs : 0 < s) (hS : IsC1Solution e S (triangle 0 s)) :
    Measurable ((triangle 0 s).indicator (fun p : ℝ × ℝ =>
      ‖S.nu p.1 p.2 * S.theta p.1 p.2 / S.r p.1 p.2 ^ 2 *
        curvScalar (triangle 0 s) S p.1 p.2‖ₑ)) ∧
    Measurable ((triangle 0 s).indicator (fun p : ℝ × ℝ =>
      ‖S.lam p.1 p.2 * S.xi p.1 p.2 / S.r p.1 p.2 ^ 2 *
        curvScalarIn e (triangle 0 s) S p.1 p.2‖ₑ)) := by
  let O := triangle 0 s ∩ {p : ℝ × ℝ | p.1 < p.2}
  have hr (p : ℝ × ℝ) (hp : p ∈ O) : (S.r p.1 p.2 : ℂ) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (hS.r_pos p hp.1 hp.2).ne')
  have cr := (Complex.continuous_ofReal.comp_continuousOn hS.c1_r.continuousOn).mono
    (show O ⊆ triangle 0 s from inter_subset_left)
  have cn := (Complex.continuous_ofReal.comp_continuousOn hS.c1_nu.continuousOn).mono
    (show O ⊆ triangle 0 s from inter_subset_left)
  have cl := (Complex.continuous_ofReal.comp_continuousOn hS.c1_lam.continuousOn).mono
    (show O ⊆ triangle 0 s from inter_subset_left)
  have ct := hS.c1_theta.continuousOn.mono (show O ⊆ triangle 0 s from inter_subset_left)
  have cx := hS.c1_xi.continuousOn.mono (show O ⊆ triangle 0 s from inter_subset_left)
  have cprim := scalar_primitive_continuous hs hS
  constructor
  · apply measurable_triangle_enorm_of_zero_axis
      (((cn.mul ct).div (cr.pow 2) hr).mul cprim.1)
    intro t ht
    change S.nu t t * S.theta t t / (S.r t t : ℂ) ^ 2 *
      curvScalar (triangle 0 s) S t t = 0
    simp only [(hS.axis t ⟨ht.1, le_rfl, ht.2⟩).1, Complex.ofReal_zero,
      zero_pow (by decide : 2 ≠ 0), div_zero, zero_mul]
  · apply measurable_triangle_enorm_of_zero_axis
      (((cl.mul cx).div (cr.pow 2) hr).mul cprim.2)
    intro t ht
    change S.lam t t * S.xi t t / (S.r t t : ℂ) ^ 2 *
      curvScalarIn e (triangle 0 s) S t t = 0
    simp only [(hS.axis t ⟨ht.1, le_rfl, ht.2⟩).1, Complex.ofReal_zero,
      zero_pow (by decide : 2 ≠ 0), div_zero, zero_mul]

end EmcsfAcExtension.Local
