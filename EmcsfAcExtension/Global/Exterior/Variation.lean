module

public import EmcsfAcExtension.Global.Exterior.ScalarEnergy
import EmcsfAcExtension.Infra.AC.Variation

/-! # Exterior scalar comparison with outgoing variation

The comparison of `charged_SF_new_version.tex:L1231–L1250` is proved directly from
scalar energy on the exterior and variation of the two summands of the
normalized scalar. The constant is numerical, uniformly in the coupling,
solution and row. No estimate through the core is used.
-/

public section

open Set MeasureTheory Filter Topology

namespace EmcsfAcExtension.Global.Exterior

variable {ui e : ℝ} {S : Fields}

/-- [internal]
On an exterior row with radial length at least its inner radius, the scalar
energy supplies a point where the outgoing normalized field is small. The
coefficient `2` is numerical and uniform in the solution, coupling and row.
The gap premise is discharged by the adaptive exterior's late gap estimate. -/
theorem outgoing_field_witness_of_gap (h : OriginalData ui e S) {u a : ℝ}
    (hua : u < a) (ha : a ≤ 0) (hs : outSeg u a 0 ⊆ origDomain ui)
    (hg : ∀ v ∈ Icc a 0, 1 / 2 ≤ 1 - S.mu u v)
    (hwidth : 2 * S.r u a ≤ S.r u 0) :
    ∃ w ∈ Icc a 0, ‖S.theta u w / (S.lam u w : ℂ)‖ ≤
      2 * Real.sqrt (terminalMass S u / S.r u a) := by
  have hl (v : ℝ) (hv : v ∈ Icc a 0) :=
    h.solution.lam_pos (u, v) (hs ⟨rfl, hv⟩)
  have hr := h.solution.r_pos (u, a) (hs ⟨rfl, le_rfl, ha⟩) hua
  let f : ℝ → ℝ := fun v => ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2
  have cl := Calculus.continuousOn_out_section h.solution.cont_lam hs
  have cf : ContinuousOn f (Icc a 0) :=
    ((Calculus.continuousOn_out_section h.solution.cont_theta hs).div
      (Complex.continuous_ofReal.comp_continuousOn cl)
      (fun v hv => Complex.ofReal_ne_zero.mpr (hl v hv).ne')).norm.pow 2
  obtain ⟨w, hw, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr ha) cf
  have hle := intervalIntegral.integral_mono_on ha
    ((cl.const_mul (f w)).intervalIntegrable_of_Icc (μ := volume) ha)
    ((cf.mul cl).intervalIntegrable_of_Icc (μ := volume) ha)
    (fun v hv => mul_le_mul_of_nonneg_right (hmin hv) (hl v hv).le)
  have hrad := (h.solution.eq_out u a 0 hua ha hs).1
  rw [intervalIntegral.integral_const_mul, ← hrad.2] at hle
  have he := scalar_energy_le_of_gap h hua ha hs hg
  have hf : 0 ≤ f w := sq_nonneg _
  have hsmall : f w * S.r u a ≤ 4 * terminalMass S u := by
    have hwgt := mul_le_mul_of_nonneg_left (show S.r u a ≤ S.r u 0 - S.r u a by
      linarith only [hwidth]) hf
    exact hwgt.trans (hle.trans he)
  have hM : 0 ≤ terminalMass S u := mass_nonneg h (hs ⟨rfl, ha, le_rfl⟩)
  have hsqrt := Real.sq_sqrt (div_nonneg hM hr.le)
  have hsq : f w ≤ 4 * (terminalMass S u / S.r u a) := by
    simpa only [mul_div_assoc] using (le_div_iff₀ hr).2 hsmall
  refine ⟨w, hw, ?_⟩
  dsimp [f] at hsq
  nlinarith only [hsq, hsqrt, Real.sqrt_nonneg (terminalMass S u / S.r u a),
    norm_nonneg (S.theta u w / (S.lam u w : ℂ))]

/-- [internal]
Every outgoing field value is at most the normalized scalar variation plus
`4 sqrt(M/ell)` on a late exterior row. The coefficient `4` is numerical,
uniform in the coupling, solution and row. Taking a supremum gives E2 of
approved internal project record; no compactness or boundedness of a derivative is assumed.
The adaptive consumer supplies the late gap and `2 ell ≤ R`. -/
theorem charged_exterior_FV_of_gap (h : OriginalData ui e S) {u a : ℝ}
    (hua : u < a) (ha : a ≤ 0) (hs : outSeg u a 0 ⊆ origDomain ui)
    (hg : ∀ v ∈ Icc a 0, 1 / 2 ≤ 1 - S.mu u v)
    (hwidth : 2 * S.r u a ≤ S.r u 0) :
    ∀ v ∈ Icc a 0, ‖S.theta u v / (S.lam u v : ℂ)‖ ≤
      (eVariationOn (S.a u) (Icc a 0)).toReal +
        4 * Real.sqrt (terminalMass S u / S.r u a) := by
  obtain ⟨w, hw, hsmall⟩ := outgoing_field_witness_of_gap h hua ha hs hg hwidth
  have hac := h.solution.ac_out u a 0 ha hs
  have hbva := hac.2.2.2.2.boundedVariationOn_Icc ha
  have hbvp := hac.2.2.2.1.boundedVariationOn_Icc ha
  have hpv := scalar_variation_le_of_gap h hua ha hs hg
  have hpvr : (eVariationOn (S.phi u) (Icc a 0)).toReal ≤
      2 * Real.sqrt (terminalMass S u / S.r u a) := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hpv).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  intro v hv
  have had := hbva.dist_le hv hw
  have hpd := hbvp.dist_le hv hw
  have hid : S.theta u v / (S.lam u v : ℂ) =
      (S.a u v - S.a u w) - (S.phi u v - S.phi u w) +
        S.theta u w / (S.lam u w : ℂ) := by
    simp only [Fields.a]
    abel
  calc
    ‖S.theta u v / (S.lam u v : ℂ)‖ ≤
        ‖S.a u v - S.a u w‖ + ‖S.phi u v - S.phi u w‖ +
          ‖S.theta u w / (S.lam u w : ℂ)‖ := by
      rw [hid]
      exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (eVariationOn (S.a u) (Icc a 0)).toReal +
        4 * Real.sqrt (terminalMass S u / S.r u a) := by
      rw [dist_eq_norm] at had hpd
      linarith only [had, hpd, hpvr, hsmall]

end EmcsfAcExtension.Global.Exterior
