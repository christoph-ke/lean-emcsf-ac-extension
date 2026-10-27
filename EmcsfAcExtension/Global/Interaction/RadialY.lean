module

public import EmcsfAcExtension.Global.Interaction.Profiles
import EmcsfAcExtension.Global.Calculus.Normalized
import EmcsfAcExtension.Local.Calculus.Sections
import EmcsfAcExtension.Local.Calculus.Reconstruction
import EmcsfAcExtension.Infra.LinearTransport

/-! # Damped radial reconstruction of the outgoing scalar

The selected boundary and source pieces use the frozen density `weightedJ`
on each row. Integrals are in the outgoing label (`dr = λ dv`).
Source: `charged_SF_new_version.tex:L3369–L3383`; internal project record, auxiliary
reconstructions.
-/

public section

open Set MeasureTheory Filter Complex

namespace EmcsfAcExtension.Global

/-- [internal]
The positive radial integrating factor `H(a,b)` in internal project record's `(ysplit)`,
written in outgoing labels. It depends on the actual scalar field. -/
@[expose] noncomputable def radialDamping (S : Fields) (u a b : ℝ) : ℝ :=
  Real.exp (-∫ v in a..b, S.lam u v / S.r u v * (1 - ‖S.theta u v / S.lam u v‖ ^ 2))

/-- [internal] Selected boundary summand of the outgoing normalized scalar. -/
@[expose] noncomputable def radialYBoundary (S : Fields) (u a b : ℝ) : ℂ :=
  (radialDamping S u a b : ℂ) * (S.theta u a / S.lam u a)

/-- [internal] Selected derivative-source summand of the outgoing normalized
scalar; its radial source measure is `W dr / λ² = W dv / λ`. -/
@[expose] noncomputable def radialYSource (S : Fields) (u a b : ℝ) : ℂ :=
  ∫ v in a..b, (radialDamping S u v b : ℂ) * (weightedJ S u v / S.lam u v)

namespace Interaction

private theorem radius_deriv {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b v : ℝ} (hua : u < a)
    (hs : outSeg u a b ⊆ D) (hv : v ∈ Ioo a b) :
    HasDerivAt (S.r u) (S.lam u v) v := by
  apply Local.hasDerivAt_of_integralForm_interior hv
    ((Calculus.continuousOn_out_section hS.cont_lam hs).mono Ioo_subset_Icc_self)
  intro c d hac hcd hdb
  exact (hS.eq_out u c d (hua.trans hac) hcd (fun p hp =>
    hs ⟨hp.1, hac.le.trans hp.2.1, hp.2.2.trans hdb.le⟩)).1

/-- [internal]
Exact annular radius moments with their null Jacobian. The coefficient
`1 / (n + 1)` is universal; all radii are positive on the proper row. -/
theorem radial_moment {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) (n : ℕ) :
    (∫ v in a..b, S.lam u v * S.r u v ^ n) =
      (S.r u b ^ (n + 1) - S.r u a ^ (n + 1)) / (n + 1 : ℝ) := by
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have hi := (cl.mul (cr.pow n)).intervalIntegrable_of_Icc hab (μ := volume)
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab (cr.pow (n + 1))
    (f' := fun v => (n + 1 : ℝ) * (S.lam u v * S.r u v ^ n)) (fun v hv => ?_)
    (hi.const_mul (n + 1 : ℝ))
  · rw [intervalIntegral.integral_const_mul] at heq
    apply (eq_div_iff (by positivity : (n + 1 : ℝ) ≠ 0)).mpr
    simpa only [mul_comm, Pi.pow_apply] using! heq
  · apply ((radius_deriv hS hua hs hv).pow (n + 1)).congr_deriv
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    ring

private theorem radius_log_integral {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) :
    (∫ v in a..b, S.lam u v / S.r u v) = Real.log (S.r u b) - Real.log (S.r u a) := by
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have hr (v : ℝ) (hv : v ∈ Icc a b) : S.r u v ≠ 0 :=
    (hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)).ne'
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (cr.log (fun v hv => hr v hv))
    (fun v hv => (radius_deriv hS hua hs hv).log (hr v ⟨hv.1.le, hv.2.le⟩))
    ((cl.div cr hr).intervalIntegrable_of_Icc hab)

/-- [node sec:charged-terminal-interaction#radial-expansion-control]
Nonnegative radial expansion and its exact stopped power bound,
charged_SF_new_version.tex:L3277–L3283. The exponent is the fixed stop `ε`; the
relative-charge inequality is supplied by `ExteriorStops`, whose closure
consumer obtains it from the late full-core geometry. -/
theorem radial_expansion_control {e δ c Λ F ε : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hstop : ExteriorStops S D δ c Λ F ε)
    {u a b : ℝ} (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    (∀ v ∈ Icc a b,
      0 ≤ (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v) ∧
      (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v) ≤ ε) ∧
    1 ≤ (-S.nu u b) / (-S.nu u a) ∧
      (-S.nu u b) / (-S.nu u a) ≤ (S.r u b / S.r u a) ^ ε := by
  let κ := fun v => (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v)
  have hκ (v : ℝ) (hv : v ∈ Icc a b) : 0 ≤ κ v ∧ κ v ≤ ε :=
    radial_expansion_coefficient_of_stops hstop (hs ⟨rfl, hv⟩)
      (hS.one_sub_mu_pos (u, v) (hs ⟨rfl, hv⟩))
  refine ⟨hκ, ?_⟩
  have hout := Local.IsSolution.out_section hS hua hab hs
  have cn := Calculus.continuousOn_out_section hS.cont_nu hs
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have hn (v : ℝ) (hv : v ∈ Icc a b) : 0 < -S.nu u v :=
    neg_pos.mpr (hS.nu_neg (u, v) (hs ⟨rfl, hv⟩))
  have hr (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.r u v :=
    hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
  have cn' : ContinuousOn (fun v => -S.nu u v) (uIcc a b) := by
    simpa only [uIcc_of_le hab, Pi.neg_apply] using! cn.neg
  obtain ⟨vmin, hvmin, hmin⟩ := isCompact_uIcc.exists_isMinOn nonempty_uIcc cn'
  have hvmin' : vmin ∈ Icc a b := by simpa only [uIcc_of_le hab] using hvmin
  have hac := hout.2.1.1.neg.log_of_pos_le (hn vmin hvmin') hmin
  have hder : ∀ᵐ v ∂volume.restrict (uIcc a b),
      deriv (fun v => Real.log (-S.nu u v)) v = S.lam u v / S.r u v * κ v := by
    rw [uIcc_of_le hab]
    filter_upwards [hout.2.1.2, ae_restrict_mem measurableSet_Icc] with v hv hmem
    have hd : HasDerivAt (fun v => Real.log (-S.nu u v))
        (-S.rUV u v / (-S.nu u v)) v := by
      simpa only [Pi.neg_apply] using! hv.neg.log (hn v hmem).ne'
    rw [hd.deriv]
    dsimp [Fields.rUV, κ]
    field_simp [(hn v hmem).ne', (neg_ne_zero.mp (hn v hmem).ne')]
  have hlog := integralForm_of_ac_of_ae_deriv_eq hac hder
  have iw := (cl.div cr (fun v hv => (hr v hv).ne')).intervalIntegrable_of_Icc hab (μ := volume)
  have hupper := intervalIntegral.integral_mono_on hab hlog.1 (iw.const_mul ε)
    (fun v hv => by
      have hw : 0 ≤ S.lam u v / S.r u v :=
        div_nonneg (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)).le (hr v hv).le
      exact (mul_le_mul_of_nonneg_left (hκ v hv).2 hw).trans_eq (mul_comm _ _))
  have hlower := intervalIntegral.integral_nonneg hab (μ := volume) (fun v hv =>
    mul_nonneg (div_nonneg (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)).le (hr v hv).le) (hκ v hv).1)
  rw [intervalIntegral.integral_const_mul] at hupper
  dsimp only [Pi.div_apply] at hupper
  rw [radius_log_integral hS hua hab hs, ← hlog.2] at hupper
  rw [← hlog.2] at hlower
  have hratio : (-S.nu u b) / (-S.nu u a) =
      Real.exp (Real.log (-S.nu u b) - Real.log (-S.nu u a)) := by
    rw [← Real.log_div (hn b ⟨hab, le_rfl⟩).ne' (hn a ⟨le_rfl, hab⟩).ne',
      Real.exp_log (div_pos (hn b ⟨hab, le_rfl⟩) (hn a ⟨le_rfl, hab⟩))]
  rw [hratio]
  constructor
  · simpa only [Real.exp_zero, Pi.neg_apply] using! Real.exp_le_exp.mpr hlower
  · rw [Real.rpow_def_of_pos (div_pos (hr b ⟨hab, le_rfl⟩) (hr a ⟨le_rfl, hab⟩)),
      Real.log_div (hr b ⟨hab, le_rfl⟩).ne' (hr a ⟨le_rfl, hab⟩).ne']
    exact Real.exp_le_exp.mpr (by simpa only [mul_comm, Pi.neg_apply] using! hupper)

/-- [internal]
The radial damping factor is bounded by the stopped power decay.
The exponent `1 - F²` is exact and independent of the row and solution. -/
theorem radial_damping_le_power {e F : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) (hF : 0 ≤ F)
    (hy : ∀ v ∈ Icc a b, ‖S.theta u v / S.lam u v‖ ≤ F) :
    radialDamping S u a b ≤ (S.r u a / S.r u b) ^ (1 - F ^ 2) := by
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have ct := Calculus.continuousOn_out_section hS.cont_theta hs
  have hr (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.r u v :=
    hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
  have cy := ct.div (continuous_ofReal.comp_continuousOn cl)
    (fun v hv => Complex.ofReal_ne_zero.mpr (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)).ne')
  have cw := cl.div cr (fun v hv => (hr v hv).ne')
  have iw := cw.intervalIntegrable_of_Icc hab (μ := volume)
  have cdamp : ContinuousOn (fun v => 1 - ‖S.theta u v / S.lam u v‖ ^ 2) (Icc a b) :=
    continuousOn_const.sub (cy.norm.pow 2)
  have ik := (cw.mul cdamp).intervalIntegrable_of_Icc hab (μ := volume)
  have hi := intervalIntegral.integral_mono_on hab (iw.const_mul (1 - F ^ 2)) ik
    (fun v hv => by
      change (1 - F ^ 2) * (S.lam u v / S.r u v) ≤
        S.lam u v / S.r u v * (1 - ‖S.theta u v / S.lam u v‖ ^ 2)
      have hsq := (sq_le_sq₀ (norm_nonneg _) hF).mpr (hy v hv)
      have hw : 0 ≤ S.lam u v / S.r u v :=
        div_nonneg (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)).le (hr v hv).le
      nlinarith only [mul_le_mul_of_nonneg_left hsq hw])
  rw [intervalIntegral.integral_const_mul] at hi
  dsimp only [Pi.div_apply, Pi.mul_apply, Pi.pow_apply] at hi
  rw [radius_log_integral hS hua hab hs] at hi
  rw [radialDamping, Real.rpow_def_of_pos (div_pos (hr a ⟨le_rfl, hab⟩) (hr b ⟨hab, le_rfl⟩)),
    Real.log_div (hr a ⟨le_rfl, hab⟩).ne' (hr b ⟨hab, le_rfl⟩).ne']
  apply Real.exp_le_exp.mpr
  linarith only [hi]

/-- [internal]
The radial damping coefficient and its selected source are integrable on
each proper row. Source integrability follows from AC of the frozen `a`;
it is not an assumption about the rough outgoing derivative. -/
theorem radial_y_source_integrable {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) :
    IntervalIntegrable (fun v => weightedJ S u v / (S.lam u v : ℂ)) volume a b := by
  have ha := (hS.ac_out u a b hab hs).2.2.2.2
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have ct := Calculus.continuousOn_out_section hS.cont_theta hs
  have hr (v : ℝ) (hv : v ∈ Icc a b) :=
    (hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)).ne'
  have cy := ct.div (continuous_ofReal.comp_continuousOn cl)
    (fun v hv => Complex.ofReal_ne_zero.mpr (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)).ne')
  have cc : ContinuousOn (fun v => (S.lam u v / S.r u v *
      ‖S.theta u v / S.lam u v‖ ^ 2 : ℝ) * (S.theta u v / S.lam u v)) (Icc a b) :=
    (continuous_ofReal.comp_continuousOn
    ((cl.div cr hr).mul (cy.norm.pow 2))).mul cy
  apply (ha.intervalIntegrable_deriv_complex.sub (cc.intervalIntegrable_of_Icc hab)).congr
  intro v hv
  have hv : v ∈ Icc a b := by simpa only [uIcc_of_le hab] using uIoc_subset_uIcc hv
  have he := deriv_a_eq_weightedJ S u v (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)).ne'
    (hS.one_sub_mu_pos (u, v) (hs ⟨rfl, hv⟩)).ne'
  change deriv (S.a u) v - _ = _
  rw [he]
  ring

end Interaction

/-- [internal]
Joint endpoint selection on a fixed row: the damping factor is continuous
in its initial endpoint. No continuity of the rough derivative source is used. -/
theorem continuousOn_radialDamping_start {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) : ContinuousOn (fun v => radialDamping S u v b) (Icc a b) := by
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have ct := Calculus.continuousOn_out_section hS.cont_theta hs
  have hr (v : ℝ) (hv : v ∈ Icc a b) :=
    (hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)).ne'
  have cy := ct.div (continuous_ofReal.comp_continuousOn cl)
    (fun v hv => Complex.ofReal_ne_zero.mpr (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)).ne')
  let k := fun v => S.lam u v / S.r u v * (1 - ‖S.theta u v / S.lam u v‖ ^ 2)
  have ck : ContinuousOn k (Icc a b) := (cl.div cr hr).mul (continuousOn_const.sub (cy.norm.pow 2))
  have ik := ck.intervalIntegrable_of_Icc hab (μ := volume)
  have cp : ContinuousOn (fun v => ∫ x in a..v, k x) (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      (ik.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).continuousOn
  have ce : ContinuousOn (fun v => Real.exp (-((∫ x in a..b, k x) - ∫ x in a..v, k x))) (Icc a b) :=
    Real.continuous_exp.comp_continuousOn (continuousOn_const.sub cp).neg
  apply ce.congr
  intro v hv
  dsimp only [radialDamping]
  have iv := ik.mono_set (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc hv))
  rw [intervalIntegral.integral_interval_sub_left ik iv]

/-- [internal] The selected outgoing boundary summand is continuous in its
terminal endpoint, including the starting point of a proper row. -/
theorem continuousOn_radialYBoundary_end {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) : ContinuousOn (radialYBoundary S u a) (Icc a b) := by
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have ct := Calculus.continuousOn_out_section hS.cont_theta hs
  have hr (v : ℝ) (hv : v ∈ Icc a b) :=
    (hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)).ne'
  have cy := ct.div (continuous_ofReal.comp_continuousOn cl)
    (fun v hv => Complex.ofReal_ne_zero.mpr (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)).ne')
  have cdamp : ContinuousOn (fun v => 1 - ‖S.theta u v / S.lam u v‖ ^ 2) (Icc a b) :=
    continuousOn_const.sub (cy.norm.pow 2)
  have ik := ((cl.div cr hr).mul cdamp)
    |>.intervalIntegrable_of_Icc hab (μ := volume)
  have cp := (ik.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).continuousOn
  have ce := continuous_ofReal.comp_continuousOn (Real.continuous_exp.comp_continuousOn cp.neg)
  simpa only [uIcc_of_le hab, radialYBoundary, radialDamping] using! ce.mul continuousOn_const

/-- [node eq:ct-y-split]
Exact selection of the boundary and derivative-source pieces of `θ/λ`,
charged_SF_new_version.tex:L3369–L3383. The frozen AC equations supply the rough source
integrability. There are no constants or extra regularity assumptions. -/
theorem ct_y_split_identity {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) :
    S.theta u b / S.lam u b = radialYBoundary S u a b + radialYSource S u a b := by
  let y := fun v => S.theta u v / (S.lam u v : ℂ)
  let k := fun v => -(S.lam u v / S.r u v * (1 - ‖y v‖ ^ 2))
  let c := fun v => (k v : ℂ)
  let q := fun v => weightedJ S u v / (S.lam u v : ℂ)
  have hout := Local.IsSolution.out_section hS hua hab hs
  have ha := (hS.ac_out u a b hab hs).2.2.2.2
  have hy : AbsolutelyContinuousOnInterval y a b := by
    apply (ha.sub hout.2.2.2.2.2.1.1).congr
    intro v _
    change S.a u v - S.phi u v = S.theta u v / S.lam u v
    dsimp [Fields.a]
    ring
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have ct := Calculus.continuousOn_out_section hS.cont_theta hs
  have hr (v : ℝ) (hv : v ∈ Icc a b) :=
    (hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)).ne'
  have cy := ct.div (continuous_ofReal.comp_continuousOn cl)
    (fun v hv => Complex.ofReal_ne_zero.mpr (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)).ne')
  have ck : ContinuousOn k (Icc a b) :=
    ((cl.div cr hr).mul (continuousOn_const.sub (cy.norm.pow 2))).neg
  have ik := ck.intervalIntegrable_of_Icc hab (μ := volume)
  have ic : IntervalIntegrable c volume a b := ⟨ik.1.ofReal, ik.2.ofReal⟩
  have iq := Interaction.radial_y_source_integrable hS hua hab hs
  have hder : ∀ᵐ v ∂volume.restrict (Icc a b), deriv y v = c v * y v + q v := by
    have hda := ae_restrict_of_ae (μ := volume) (s := Icc a b) ha.ae_differentiableAt_of_mem_uIcc
    filter_upwards [hda, hout.2.2.2.2.2.1.2,
      ae_restrict_mem measurableSet_Icc] with v hav hpv hv
    have hd : HasDerivAt y (deriv (S.a u) v - S.phiV u v) v := by
      apply ((hav (by simpa only [uIcc_of_le hab] using hv)).hasDerivAt.sub
        hpv).congr_of_eventuallyEq
      exact Filter.Eventually.of_forall (fun x => by
        change S.theta u x / S.lam u x = S.a u x - S.phi u x
        dsimp [Fields.a]
        ring)
    rw [hd.deriv, Interaction.deriv_a_eq_weightedJ S u v
      (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)).ne'
      (hS.one_sub_mu_pos (u, v) (hs ⟨rfl, hv⟩)).ne']
    have hlC : (S.lam u v : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)).ne'
    dsimp [c, k, q, y, Fields.phiV]
    push_cast
    field_simp [hlC]
    ring
  have heq := eq_integratingFactor_of_ac_deriv_eq_complex hab hy ic iq hder b ⟨hab, le_rfl⟩
  have hexp (x z : ℝ) : Complex.exp (∫ v in x..z, c v) = (radialDamping S u x z : ℂ) := by
    dsimp [c, k, y, radialDamping]
    rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_neg, Complex.ofReal_exp]
  have he : Complex.exp (∫ v in a..b, c v) *
      (∫ v in a..b, Complex.exp (-(∫ x in a..v, c x)) * q v) = radialYSource S u a b := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v hv
    dsimp only
    rw [uIcc_of_le hab] at hv
    have hiav := ic.mono_set (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc hv))
    have hsub := intervalIntegral.integral_interval_sub_left ic hiav
    rw [← mul_assoc, ← Complex.exp_add, ← sub_eq_add_neg, hsub, hexp]
  rw [mul_add, he, hexp] at heq
  exact heq

/-- [internal]
The selected derivative-source summand is continuous along a proper row.
This follows from its exact reconstruction, without making the derivative
density continuous. -/
theorem continuousOn_radialYSource_end {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) : ContinuousOn (radialYSource S u a) (Icc a b) := by
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have ct := Calculus.continuousOn_out_section hS.cont_theta hs
  have cy := ct.div (continuous_ofReal.comp_continuousOn cl)
    (fun v hv => Complex.ofReal_ne_zero.mpr (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)).ne')
  apply (cy.sub (continuousOn_radialYBoundary_end hS hua hab hs)).congr
  intro v hv
  have heq := ct_y_split_identity hS hua hv.1
    (fun p hp => hs ⟨hp.1, hp.2.1, hp.2.2.trans hv.2⟩)
  change radialYSource S u a v = S.theta u v / S.lam u v - radialYBoundary S u a v
  linear_combination -heq

/-- [node eq:ct-y-split]
Boundary and derivative-source power bounds, charged_SF_new_version.tex:L3372–L3383.
The exponent is exactly `1 - F²`, and the source measure is the radial
measure `‖W‖ dr / λ²` written as `‖W‖ dv / λ`. There are no hidden constants. -/
theorem ct_y_split {e F : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) (hF : 0 ≤ F)
    (hy : ∀ v ∈ Icc a b, ‖S.theta u v / S.lam u v‖ ≤ F) :
    ‖radialYBoundary S u a b‖ ≤ ‖S.theta u a / S.lam u a‖ *
      (S.r u a / S.r u b) ^ (1 - F ^ 2) ∧
    ‖radialYSource S u a b‖ ≤ ∫ v in a..b,
      (S.r u v / S.r u b) ^ (1 - F ^ 2) * (‖weightedJ S u v‖ / S.lam u v) := by
  constructor
  · rw [radialYBoundary, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (show 0 < radialDamping S u a b from Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_right (Interaction.radial_damping_le_power hS hua hab hs hF hy)
      (norm_nonneg _)).trans_eq (mul_comm _ _)
  · have iq := Interaction.radial_y_source_integrable hS hua hab hs
    have cH := continuousOn_radialDamping_start hS hua hab hs
    have iH := iq.continuousOn_mul (continuous_ofReal.comp_continuousOn (by
      simpa only [uIcc_of_le hab] using cH))
    have cr := Calculus.continuousOn_out_section hS.cont_r hs
    have hr (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.r u v :=
      hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
    have cp : ContinuousOn (fun v => (S.r u v / S.r u b) ^ (1 - F ^ 2)) (Icc a b) :=
      (cr.div continuousOn_const (fun _ _ => (hr b ⟨hab, le_rfl⟩).ne')).rpow_const
        (fun v hv => Or.inl (div_pos (hr v hv) (hr b ⟨hab, le_rfl⟩)).ne')
    have ip := iq.norm.continuousOn_mul (by simpa only [uIcc_of_le hab] using cp)
    have hm := intervalIntegral.integral_mono_on hab iH.norm ip (fun v hv => by
      change ‖(radialDamping S u v b : ℂ) * (weightedJ S u v / S.lam u v)‖ ≤
        (S.r u v / S.r u b) ^ (1 - F ^ 2) * ‖weightedJ S u v / S.lam u v‖
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (show 0 < radialDamping S u v b from Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right
        (Interaction.radial_damping_le_power hS (hua.trans_le hv.1) hv.2
          (fun p hp => hs ⟨hp.1, hv.1.trans hp.2.1, hp.2.2⟩) hF
          (fun x hx => hy x ⟨hv.1.trans hx.1, hx.2⟩)) (norm_nonneg _))
    calc
      ‖radialYSource S u a b‖ ≤ ∫ v in a..b,
          ‖(radialDamping S u v b : ℂ) * (weightedJ S u v / S.lam u v)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hab
      _ ≤ _ := hm
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro v hv
        dsimp only
        rw [uIcc_of_le hab] at hv
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩))]

end EmcsfAcExtension.Global
