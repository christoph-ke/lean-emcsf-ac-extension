module

public import EmcsfAcExtension.Global.Interaction.RadialY
import EmcsfAcExtension.Local.Calculus.Sections
import EmcsfAcExtension.Local.Calculus.Reconstruction
import EmcsfAcExtension.Global.Calculus.Sections
import EmcsfAcExtension.Infra.Null.IntegralForm

/-! # Radial curvature reconstruction

The explicit electromagnetic primitive is separated from the term containing
the full incoming scalar and the rough derivative source. The curvature
transport identity is supplied by the renormalized packet.
Source: `charged_SF_new_version.tex:L3414–L3414`; internal project record, auxiliary
reconstructions.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global

/-- [internal] Boundary term in the annular curvature reconstruction. -/
@[expose] noncomputable def radialCurvatureBoundary (S : Fields) (u a b : ℝ) : ℂ :=
  (S.r u a / S.r u b : ℝ) * Local.curv S u a

/-- [internal]
The curvature source primitive with the full incoming normalized scalar.
The factor `λ` in `dr = λ dv` has already been included. -/
@[expose] noncomputable def radialCurvatureSource (S : Fields) (u a b : ℝ) : ℂ :=
  (S.r u b : ℂ)⁻¹ * ∫ v in a..b,
    (((1 - S.mu u v) * S.r u v / S.lam u v : ℝ) : ℂ) *
      starRingEnd ℂ (S.xi u v / S.nu u v) * weightedJ S u v

/-- [internal]
Explicit electromagnetic curvature primitive on an annulus. The mixed term
containing `zᵉᵐ j` belongs to `radialCurvatureSource`, not to this primitive. -/
@[expose] noncomputable def radialCurvatureEM (e : ℝ) (S : Fields) (u a b : ℝ) : ℂ :=
  (S.r u b : ℂ)⁻¹ * ∫ v in a..b,
    ((S.lam u v * S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) : ℂ) -
      I * e * S.Q u v * S.theta u v * starRingEnd ℂ (S.phi u v)

/-- [internal]
The reconstruction `eq:ct-C-reconstruction` from the renormalized packet's
annular transport identity, charged_SF_new_version.tex:L3414–L3425. Its consumer must
provide that identity from `eq:ct-C-trans`; this conditional helper closes
no unconditional curvature node. There are no constants. -/
private theorem curvature_reconstruction_algebra {e : ℝ} {S : Fields} {u a b : ℝ}
    (hr : S.r u b ≠ 0) (hl : ∀ v ∈ uIcc a b, S.lam u v ≠ 0)
    (hg : ∀ v ∈ uIcc a b, 1 - S.mu u v ≠ 0)
    (isrc : IntervalIntegrable (fun v =>
      (S.r u v : ℂ) * starRingEnd ℂ (S.xi u v / S.nu u v) * jOut S u v) volume a b)
    (iem : IntervalIntegrable (fun v =>
      ((S.lam u v * S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) : ℂ) -
        I * e * S.Q u v * S.theta u v * starRingEnd ℂ (S.phi u v)) volume a b)
    (htransport : IntegralForm (fun v => (S.r u v : ℂ) * Local.curv S u v)
      (fun v => (S.r u v : ℂ) * starRingEnd ℂ (S.xi u v / S.nu u v) * jOut S u v +
        (((S.lam u v * S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) : ℂ) -
          I * e * S.Q u v * S.theta u v * starRingEnd ℂ (S.phi u v))) a b) :
    Local.curv S u b = radialCurvatureBoundary S u a b +
      radialCurvatureSource S u a b + radialCurvatureEM e S u a b := by
  have heq := htransport.eq_add_integral
  rw [intervalIntegral.integral_add isrc iem] at heq
  have hsrc : (∫ v in a..b, (S.r u v : ℂ) *
      starRingEnd ℂ (S.xi u v / S.nu u v) * jOut S u v) =
      ∫ v in a..b, (((1 - S.mu u v) * S.r u v / S.lam u v : ℝ) : ℂ) *
        starRingEnd ℂ (S.xi u v / S.nu u v) * weightedJ S u v := by
    apply intervalIntegral.integral_congr
    intro v hv
    dsimp only
    have hlC := Complex.ofReal_ne_zero.mpr (hl v hv)
    have hgC : (1 - S.mu u v : ℂ) ≠ 0 := by exact_mod_cast hg v hv
    dsimp [weightedJ]
    push_cast
    field_simp
  rw [hsrc] at heq
  dsimp [radialCurvatureBoundary, radialCurvatureSource, radialCurvatureEM]
  have hrC := Complex.ofReal_ne_zero.mpr hr
  rw [Complex.ofReal_div]
  apply (mul_left_cancel₀ hrC)
  rw [mul_add, mul_add]
  field_simp
  linear_combination heq

/-- [internal]
The full curvature reconstruction `eq:ct-C-reconstruction` on a proper
row, charged_SF_new_version.tex:L3414–L3425. Its only pending identity is the exact
annular transport equation from internal project record. Both summands' integrability and
all denominator facts are derived from the frozen solution on the row.
There are no constants or additional original-data hypotheses. -/
theorem ct_c_reconstruction_of_transport {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D)
    (htransport : IntegralForm (fun v => (S.r u v : ℂ) * Local.curv S u v)
      (fun v => (S.r u v : ℂ) * starRingEnd ℂ (S.xi u v / S.nu u v) * jOut S u v +
        (((S.lam u v * S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) : ℂ) -
          I * e * S.Q u v * S.theta u v * starRingEnd ℂ (S.phi u v))) a b) :
    Local.curv S u b = radialCurvatureBoundary S u a b +
      radialCurvatureSource S u a b + radialCurvatureEM e S u a b := by
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have cq := Calculus.continuousOn_out_section hS.cont_Q hs
  have ct := Calculus.continuousOn_out_section hS.cont_theta hs
  have cp := Calculus.continuousOn_out_section hS.cont_phi hs
  have hr (v : ℝ) (hv : v ∈ Icc a b) :=
    (hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)).ne'
  have cfirst := continuous_ofReal.comp_continuousOn
    ((cl.mul (cq.pow 2)).div (cr.pow 2) (fun v hv => pow_ne_zero _ (hr v hv)))
  have csecond : ContinuousOn (fun v => I * e * S.Q u v * S.theta u v *
      starRingEnd ℂ (S.phi u v)) (Icc a b) :=
    (((continuousOn_const.mul (continuous_ofReal.comp_continuousOn cq)).mul ct).mul cp.star)
  have iem : IntervalIntegrable (fun v =>
      ((S.lam u v * S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) : ℂ) -
        I * e * S.Q u v * S.theta u v * starRingEnd ℂ (S.phi u v)) volume a b :=
    (cfirst.sub csecond).intervalIntegrable_of_Icc hab
  have isrc : IntervalIntegrable (fun v =>
      (S.r u v : ℂ) * starRingEnd ℂ (S.xi u v / S.nu u v) * jOut S u v) volume a b := by
    apply (htransport.1.sub iem).congr
    intro v _
    dsimp only [Pi.sub_apply]
    ring
  exact curvature_reconstruction_algebra (hr b ⟨hab, le_rfl⟩)
    (fun v hv => (hS.lam_pos (u, v)
      (hs ⟨rfl, by simpa only [uIcc_of_le hab, mem_Icc] using hv⟩)).ne')
    (fun v hv => (hS.one_sub_mu_pos (u, v)
      (hs ⟨rfl, by simpa only [uIcc_of_le hab, mem_Icc] using hv⟩)).ne')
    isrc iem htransport

/-- [internal]
The explicit electromagnetic curvature estimate at charged_SF_new_version.tex:L3431–L3431.
The positive constant is chosen from the charge-profile coefficient `Cq`
alone, before coupling, scalar amplitude, radius, and row. The scalar and
charge profiles are discharged by the stopped-geometry consumer; they are
not additional original-data hypotheses. -/
theorem ct_c_charge_of_profiles (Cq : ℝ) (hCq : 0 ≤ Cq) :
    ∃ C : ℝ, 0 < C ∧ ∀ (e M₀ F : ℝ) (S : Fields) (D : Set (ℝ × ℝ)) (u a b : ℝ),
      IsSolution e S D → u < a → a ≤ b → outSeg u a b ⊆ D → 0 ≤ M₀ → 0 ≤ F →
      (∀ v ∈ Icc a b, ‖S.phi u v‖ ≤ M₀) →
      (∀ v ∈ Icc a b, ‖S.theta u v / S.lam u v‖ ≤ F) →
      (∀ v ∈ Icc a b, |S.Q u v| / S.r u v ^ 2 ≤ Cq * |e| * M₀ * F) →
      ‖radialCurvatureEM e S u a b‖ ≤ C * e ^ 2 * M₀ ^ 2 * F ^ 2 * S.r u b ^ 2 := by
  refine ⟨Cq ^ 2 + Cq + 1, by positivity, ?_⟩
  intro e M₀ F S D u a b hS hua hab hs hM hF hphi hy hcharge
  let A := Cq * |e| * M₀ * F
  let K := (Cq ^ 2 + Cq) * e ^ 2 * M₀ ^ 2 * F ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hp (v : ℝ) (hv : v ∈ Icc a b) : (u, v) ∈ D := hs ⟨rfl, hv⟩
  have hr (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.r u v :=
    hS.r_pos (u, v) (hp v hv) (hua.trans_le hv.1)
  have hl (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.lam u v := hS.lam_pos (u, v) (hp v hv)
  have hpoint (v : ℝ) (hv : v ∈ Icc a b) :
      ‖((S.lam u v * S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) : ℂ) -
        I * e * S.Q u v * S.theta u v * starRingEnd ℂ (S.phi u v)‖ ≤
        K * (S.lam u v * S.r u v ^ 2) := by
    have hq : |S.Q u v| ≤ A * S.r u v ^ 2 :=
      (div_le_iff₀ (sq_pos_of_pos (hr v hv))).mp (hcharge v hv)
    have hq2 : S.Q u v ^ 2 / S.r u v ^ 2 ≤ A ^ 2 * S.r u v ^ 2 := by
      apply (div_le_iff₀ (sq_pos_of_pos (hr v hv))).mpr
      have hh := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hA (sq_nonneg _))).mpr hq
      rw [sq_abs] at hh
      convert hh using 1
      ring
    have ht : ‖S.theta u v‖ ≤ S.lam u v * F := by
      have hh := hy v hv
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hl v hv)] at hh
      have hh' := (div_le_iff₀ (hl v hv)).mp hh
      simpa only [mul_comm] using hh'
    calc
      _ ≤ ‖((S.lam u v * S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) : ℂ)‖ +
          ‖I * e * S.Q u v * S.theta u v * starRingEnd ℂ (S.phi u v)‖ := norm_sub_le _ _
      _ = S.lam u v * (S.Q u v ^ 2 / S.r u v ^ 2) +
          |e| * |S.Q u v| * ‖S.theta u v‖ * ‖S.phi u v‖ := by
        simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_conj, abs_of_nonneg
            (div_nonneg (mul_nonneg (hl v hv).le (sq_nonneg _)) (sq_nonneg _))]
        ring
      _ ≤ S.lam u v * (A ^ 2 * S.r u v ^ 2) +
          |e| * (A * S.r u v ^ 2) * (S.lam u v * F) * M₀ := by
        apply add_le_add (mul_le_mul_of_nonneg_left hq2 (hl v hv).le)
        apply mul_le_mul _ (hphi v hv) (norm_nonneg _)
          (mul_nonneg (mul_nonneg (abs_nonneg e) (mul_nonneg hA (sq_nonneg _)))
            (mul_nonneg (hl v hv).le hF))
        apply mul_le_mul _ ht (norm_nonneg _)
          (mul_nonneg (abs_nonneg e) (mul_nonneg hA (sq_nonneg _)))
        exact mul_le_mul_of_nonneg_left hq (abs_nonneg e)
      _ = _ := by dsimp [A, K]; rw [← sq_abs e]; ring
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have cq := Calculus.continuousOn_out_section hS.cont_Q hs
  have ct := Calculus.continuousOn_out_section hS.cont_theta hs
  have cp := Calculus.continuousOn_out_section hS.cont_phi hs
  have cfirst := continuous_ofReal.comp_continuousOn
    ((cl.mul (cq.pow 2)).div (cr.pow 2) (fun v hv => pow_ne_zero _ (hr v hv).ne'))
  have csecond : ContinuousOn (fun v => I * e * S.Q u v * S.theta u v *
      starRingEnd ℂ (S.phi u v)) (Icc a b) :=
    (((continuousOn_const.mul (continuous_ofReal.comp_continuousOn cq)).mul ct).mul cp.star)
  have iem := (cfirst.sub csecond).intervalIntegrable_of_Icc hab (μ := volume)
  have im := (cl.mul (cr.pow 2)).intervalIntegrable_of_Icc hab (μ := volume)
  have hi := intervalIntegral.integral_mono_on hab iem.norm (im.const_mul K) hpoint
  rw [intervalIntegral.integral_const_mul] at hi
  dsimp only [Pi.mul_apply, Pi.pow_apply] at hi
  rw [Interaction.radial_moment hS hua hab hs 2] at hi
  norm_num only [Nat.reduceAdd] at hi
  have him : (∫ v in a..b,
      ‖((S.lam u v * S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) : ℂ) -
        I * e * S.Q u v * S.theta u v * starRingEnd ℂ (S.phi u v)‖) ≤ K * (S.r u b ^ 3 / 3) :=
    hi.trans (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
      (sub_le_self _ (pow_nonneg (hr a ⟨le_rfl, hab⟩).le 3)) (by norm_num)) hK)
  rw [radialCurvatureEM, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (hr b ⟨hab, le_rfl⟩)]
  calc
    _ ≤ (S.r u b)⁻¹ * (K * (S.r u b ^ 3 / 3)) :=
      mul_le_mul_of_nonneg_left ((intervalIntegral.norm_integral_le_integral_norm hab).trans him)
        (inv_nonneg.mpr (hr b ⟨hab, le_rfl⟩).le)
    _ = (K / 3) * S.r u b ^ 2 := by field_simp [(hr b ⟨hab, le_rfl⟩).ne']
    _ ≤ K * S.r u b ^ 2 := mul_le_mul_of_nonneg_right (by linarith only [hK]) (sq_nonneg _)
    _ ≤ _ := by
      dsimp [K]
      have hn : 0 ≤ e ^ 2 * M₀ ^ 2 * F ^ 2 * S.r u b ^ 2 := by positivity
      nlinarith only [hn]

end EmcsfAcExtension.Global
