module

public import EmcsfAcExtension.Global.Calculus.DensityRepresentative
public import EmcsfAcExtension.Global.Calculus.Raychaudhuri
import EmcsfAcExtension.Local.Algebra.Radial
import EmcsfAcExtension.Local.Calculus.Sections

/-! # The exterior outgoing derivative and its exact charged source

The incoming equation is interpreted using the fixed initial-label density,
not a restriction of an arbitrary product-a.e. derivative. The displayed
source retains all electromagnetic terms of `charged_SF_new_version.tex:L1254–L1296`.
The radial identities use the original characteristic equations on proper
positive-radius intervals. No terminal hypothesis is needed in this file.
-/

public section

open Set MeasureTheory Complex Topology

namespace EmcsfAcExtension.Global.Exterior

variable {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}

/-- [node c:exterior#normalized-scalar-transport]
The incoming normalized scalar equation, in ordinary integral form with the
connection term displayed. This is the covariant equation N1 of approved
internal project record on every proper incoming segment. There are no constants. -/
theorem normalized_scalar_transport (hS : IsSolution e S D) {a b v : ℝ}
    (hab : a ≤ b) (hbv : b < v) (hs : inSeg a b v ⊆ D) :
    IntegralForm (fun u => S.a u v)
      (fun u => (-S.nu u v / ((1 - S.mu u v) * S.r u v) : ℝ) *
        ((S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) *
          (S.theta u v / (S.lam u v : ℂ)) + I * e * S.Q u v * S.phi u v) -
        I * e * S.A u v * S.a u v) a b := by
  convert Calculus.constant_label_connector_calculus hS hab hbv hs using 1
  funext u
  rw [Calculus.normalized_incoming_source_eq]
  simp only [Fields.a, add_sub_cancel_left]
  ring

/-- [node c:exterior#radial-differentiation-identities]
The first radial coefficient identity, with `λ` as the outgoing Jacobian.
It holds a.e. on every proper outgoing interval and uses no terminal input.
This form makes no outgoing derivative of `λ` or `θ` necessary. -/
theorem radial_log_coefficient (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    ∀ᵐ v ∂volume.restrict (Icc a b),
      HasDerivAt (fun v => Real.log (-S.nu u v / ((1 - S.mu u v) * S.r u v)))
        (S.lam u v / S.r u v * (‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 - 1)) v := by
  have h := Local.IsSolution.out_section hS hua hab hs
  have hlog := Calculus.raychaudhuri_out_section hS hua hab hs
  have hmem : ∀ᵐ v ∂volume.restrict (Icc a b), v ∈ Ioo a b := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [h.1.2, hlog.2, hmem] with v hrv hd hv'
  have hv : v ∈ Icc a b := Ioo_subset_Icc_self hv'
  have hp : (u, v) ∈ D := hs ⟨rfl, hv⟩
  have hr := hS.r_pos (u, v) hp (hua.trans_le hv.1)
  have hl := hS.lam_pos (u, v) hp
  have heq : (fun t => Real.log (-S.nu u t / ((1 - S.mu u t) * S.r u t))) =ᶠ[
      nhds v] (fun t => Real.log (-S.nu u t / (1 - S.mu u t)) - Real.log (S.r u t)) := by
    filter_upwards [Ioo_mem_nhds hv'.1 hv'.2] with t ht
    have hpt : (u, t) ∈ D := hs ⟨rfl, ht.1.le, ht.2.le⟩
    rw [div_mul_eq_div_div, Real.log_div
      (div_ne_zero (neg_ne_zero.mpr (hS.nu_neg (u, t) hpt).ne)
        (hS.one_sub_mu_pos (u, t) hpt).ne')
      (hS.r_pos (u, t) hpt (hua.trans ht.1)).ne']
  have hdiff := hd.sub (hrv.log hr.ne')
  apply (hdiff.congr_of_eventuallyEq heq).congr_deriv
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl, div_pow]
  field_simp [hr.ne', hl.ne']

/-- [node c:exterior#radial-differentiation-identities]
The second radial identity, including the Maxwell current with its exact
sign and coefficient. The derivative is written in the original label;
division by positive `λ` gives N2 of internal project record. No constant occurs. -/
theorem radial_mass_charge_coefficient (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    ∀ᵐ v ∂volume.restrict (Icc a b),
      HasDerivAt (fun v => S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2)
        (S.lam u v / S.r u v *
          ((1 - S.mu u v) * ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 - S.mu u v +
            3 * (S.Q u v ^ 2 / S.r u v ^ 2) +
            2 * e * S.Q u v * (starRingEnd ℂ (S.phi u v) *
              (S.theta u v / (S.lam u v : ℂ))).im)) v := by
  have h := Local.IsSolution.out_section hS hua hab hs
  filter_upwards [h.1.2, h.2.2.1.2, h.2.2.2.1.2,
    ae_restrict_mem measurableSet_Icc] with v hrv hmv hQv hv
  have hp : (u, v) ∈ D := hs ⟨rfl, hv⟩
  have hr := (hS.r_pos (u, v) hp (hua.trans_le hv.1)).ne'
  have hl := (hS.lam_pos (u, v) hp).ne'
  let y := S.theta u v / (S.lam u v : ℂ)
  let q := S.Q u v ^ 2 / S.r u v ^ 2
  let j := (starRingEnd ℂ (S.phi u v) * y).im
  have dmu : HasDerivAt (S.mu u)
      (S.lam u v / S.r u v * ((1 - S.mu u v) * ‖y‖ ^ 2 + q - S.mu u v)) v := by
    apply ((hmv.const_mul 2).div hrv hr).congr_deriv
    calc
      _ = 2 * S.mV u v / S.r u v - 2 * S.m u v * S.lam u v / S.r u v ^ 2 := by
        field_simp [hr]
      _ = _ := Local.Stab.outgoing_mu_derivative_identity_algebra hr hl rfl
  have dQ : HasDerivAt (S.Q u) (-e * S.r u v * S.lam u v * j) v := by
    apply hQv.congr_deriv
    dsimp [Fields.QV, j, y]
    rw [← mul_div_assoc, Complex.div_ofReal_im]
    field_simp [hl]
  apply (dmu.sub ((dQ.pow 2).div (hrv.pow 2) (pow_ne_zero _ hr))).congr_deriv
  simp only [q, y, j, Pi.pow_apply]
  field_simp [hr]
  ring

/-- [node eq:charged-exterior-derivative]
The exact differentiated equation of `charged_SF_new_version.tex:L1254–L1274`, for
the prescribed density. Its ordinary derivative includes `-ieA W`; adding
that connection term gives `DᵤW = aW + rawDensitySource`. The characteristic
AC proof includes the electromagnetic commutator. There are no constants. -/
theorem charged_exterior_derivative (hS : IsSolution e S D)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hrect : Icc a b ×ˢ Icc c d ⊆ D ∩ {p | p.1 < p.2}) :
    ∀ v ∈ Icc c d,
      AbsolutelyContinuousOnInterval (fun u => densityRepresentative e S a u v) a b ∧
      ∀ᵐ u ∂volume.restrict (Icc a b),
        HasDerivAt (fun x => densityRepresentative e S a x v)
          (((-S.nu u v / ((1 - S.mu u v) * S.r u v) *
              (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) : ℝ) - I * e * S.A u v) *
            densityRepresentative e S a u v + rawDensitySource e S u v) u :=
  Calculus.weak_outgoing_density_transport hS hab hcd hrect

/-- [node c:exterior#derivative-ac-representation]
The fixed-density representation on a proper positive-radius rectangle.
One exceptional label set precedes every incoming row. The multiplier and
continuous remainder are exactly the expansion-ratio/phase and source
integral in `densityRepresentative`; no pointwise bound on the AC derivative
is assumed. The two continuous factors and the everywhere primitive are
included. Local constants, when extracted from compactness, may depend on
the fixed solution and rectangle. -/
theorem derivative_ac_representation {ui : ℝ} (h : OriginalData ui e S)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hrect : Icc a b ×ˢ Icc c d ⊆ origDomain ui ∩ {p | p.1 < p.2}) :
    (∀ᵐ v ∂volume.restrict (Icc c d), ∀ u ∈ Icc a b,
      HasDerivAt (S.a u) (densityRepresentative e S a u v) v) ∧
    ∃ P R : ℝ → ℝ → ℂ,
      ContinuousOn P.uncurry (Icc a b ×ˢ Icc c d) ∧
      ContinuousOn R.uncurry (Icc a b ×ˢ Icc c d) ∧
      (∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
        densityRepresentative e S a u v = Density.fixedDensity P R (deriv (S.a a)) u v) ∧
      (∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
        S.a u v = S.a u c + ∫ t in c..v, Density.fixedDensity P R (deriv (S.a a)) u t) :=
  ⟨Calculus.fixed_density_representation _ _ _ h _ _ _ _ hab hcd hrect,
    Calculus.exists_density_factors h.solution hab hcd hrect⟩

end EmcsfAcExtension.Global.Exterior
