/- Copyright (c) 2026. All rights reserved. -/

module

public import EmcsfAcExtension.Frozen.IsSolution
public import EmcsfAcExtension.Global.Interaction.RadialY
import EmcsfAcExtension.Global.Calculus.Endpoint
import EmcsfAcExtension.Global.Interaction.PairKernel
import EmcsfAcExtension.Global.Interaction.PairTonelli
import EmcsfAcExtension.Global.Interaction.OutgoingOptics
import EmcsfAcExtension.Global.Interaction.PairSource
import EmcsfAcExtension.Infra.Mixed.MomentKernel
import EmcsfAcExtension.Local.Calculus.RelativeCharge
import EmcsfAcExtension.Local.Calculus.Sections
import Mathlib.Tactic

/-!
# Incoming optical mass and finite-endpoint kernels

The mass estimate and incoming optical kernels at
`charged_SF_new_version.tex:L3747–L3773`. Radial integrals are expressed in the original
null labels, including their Jacobian. No scalar reconstruction is assumed.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension.Global.InteractionEstimate

/-- [internal]
The outgoing radius controls label separation with the exact lower
expansion bound `c`, independently of the radius at the first label. -/
theorem source_label_radius_bound {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u s v c : ℝ} (hus : u < s) (hsv : s ≤ v)
    (hs : outSeg u s v ⊆ D) (hc : ∀ x ∈ Icc s v, c ≤ S.lam u x) :
    c * (v - s) ≤ S.r u v := by
  have he := (hS.eq_out u s v hus hsv hs).1
  have hi := intervalIntegral.integral_mono_on hsv
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => c) volume s v) he.1 hc
  rw [intervalIntegral.integral_const, smul_eq_mul] at hi
  rw [← he.2] at hi
  have hr := hS.r_pos (u, s) (hs ⟨rfl, le_rfl, hsv⟩) hus
  nlinarith only [hi, hr]

/-- [internal]
The doubled boundary scalar upper mass from internal project record `(boundary-mass)`.
It is the boundary mass plus the radial square of the actual selected
boundary scalar, with the null Jacobian written in outgoing labels. -/
@[expose] noncomputable def radialBoundaryMass (S : Fields) (u a b : ℝ) : ℝ :=
  S.m u a + ∫ v in a..b, S.lam u v * ‖radialYBoundary S u a v‖ ^ 2

/-- [internal]
The actual boundary scalar has radial square at most
`r_a |y_a|²/(2(1-F²)-1)`. Its exact coefficient depends only on the fixed
amplitude `F`, uniformly in the solution and both row radii and labels.
Source: charged_SF_new_version.tex:L3754–L3756; internal project record `(boundary-mass)`. -/
theorem boundary_scalar_mass_le {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b F : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) (hF : 0 ≤ F) (hp : 1 / 2 < 1 - F ^ 2)
    (hy : ∀ v ∈ Icc a b, ‖S.theta u v / S.lam u v‖ ≤ F) :
    (∫ v in a..b, S.lam u v * ‖radialYBoundary S u a v‖ ^ 2) ≤
      S.r u a * ‖S.theta u a / S.lam u a‖ ^ 2 / (2 * (1 - F ^ 2) - 1) := by
  let p := 1 - F ^ 2
  let q := 2 * p - 1
  have hq : 0 < q := by dsimp [q, p]; linarith only [hp]
  have hr (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.r u v :=
    hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
  have hl (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.lam u v :=
    hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)
  have hra := hr a ⟨le_rfl, hab⟩
  let A := ‖S.theta u a / S.lam u a‖ ^ 2 * S.r u a
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hpoint (v : ℝ) (hv : v ∈ Icc a b) :
      S.lam u v * ‖radialYBoundary S u a v‖ ^ 2 ≤
        A * (S.lam u v / S.r u v * (S.r u a / S.r u v) ^ q) := by
    have hY := (ct_y_split hS hua hv.1
      (fun z hz => hs ⟨hz.1, hz.2.1, hz.2.2.trans hv.2⟩) hF
      (fun x hx => hy x ⟨hx.1, hx.2.trans hv.2⟩)).1
    have hrat := div_pos hra (hr v hv)
    have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _)
      (Real.rpow_nonneg hrat.le p))).mpr hY
    calc
      _ ≤ S.lam u v * (‖S.theta u a / S.lam u a‖ * (S.r u a / S.r u v) ^ p) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (hl v hv).le
      _ = _ := by
        rw [mul_pow, pow_two ((S.r u a / S.r u v) ^ p), ← Real.rpow_add hrat,
          show p + p = q + 1 by dsimp [q]; ring, Real.rpow_add hrat, Real.rpow_one]
        dsimp [A]
        ring
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have cY := continuousOn_radialYBoundary_end hS hua hab hs
  have iY : IntervalIntegrable (fun v => S.lam u v * ‖radialYBoundary S u a v‖ ^ 2) volume a b :=
    (cl.mul (cY.norm.pow 2)).intervalIntegrable_of_Icc hab
  have hreal : ENNReal.ofReal (∫ v in a..b, S.lam u v * ‖radialYBoundary S u a v‖ ^ 2) =
      ∫⁻ v in Icc a b, ENNReal.ofReal (S.lam u v * ‖radialYBoundary S u a v‖ ^ 2) := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    exact ofReal_integral_eq_lintegral_ofReal
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp iY)
      (ae_restrict_of_forall_mem measurableSet_Icc (fun v hv => mul_nonneg (hl v hv).le
        (sq_nonneg _)))
  have hrow := (Calculus.out_section hS hua.le hab hs).1
  have hm := (outgoing_radius_calculus hS hua.le hab hs).2.monotoneOn
  have hkernel := Mixed.lintegral_radial_moment_mass_le hab hq hrow.1 hra hm
    (fun v hv => (hl v hv).le) (hrow.2.mono fun _ h => h.deriv)
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
  rw [hreal]
  calc
    _ ≤ ∫⁻ v in Icc a b, ENNReal.ofReal A *
        (ENNReal.ofReal (S.lam u v / S.r u v) * ENNReal.ofReal ((S.r u a / S.r u v) ^ q)) := by
      apply setLIntegral_mono' measurableSet_Icc
      intro v hv
      rw [← ENNReal.ofReal_mul (div_nonneg (hl v hv).le (hr v hv).le), ← ENNReal.ofReal_mul hA]
      exact ENNReal.ofReal_le_ofReal (hpoint v hv)
    _ = ENNReal.ofReal A * (∫⁻ v in Icc a b,
        ENNReal.ofReal (S.lam u v / S.r u v) * ENNReal.ofReal ((S.r u a / S.r u v) ^ q)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal A * ENNReal.ofReal (1 / q) := by gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_mul hA]
      congr 1
      dsimp [A, q, p]
      ring

/-- [node prop:ct-interaction#boundary-incoming-optical-cost]
Incoming optical cost of the actual boundary upper mass on every measurable
stage history with radii in `[ρB,B]`. The positive constant depends only on
`δ,ρ,F`, before coupling, solution, stage radius, budget, labels, and duration.
It is `2(1+(2(1-F²)-1)⁻¹)/(δρ)` and includes the doubled scalar upper mass
required after separating the outgoing scalar square. No duration or
inverse stage energy appears. Source: charged_SF_new_version.tex:L3754–L3756. -/
theorem boundary_incoming_optical_cost (δ ρ F : ℝ)
    (hδ : 0 < δ) (hρ : 0 < ρ) (hF : 0 ≤ F) (hp : 1 / 2 < 1 - F ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (e a b v B E : ℝ) (S : Fields) (D : Set (ℝ × ℝ))
      (vb : ℝ → ℝ) (U : Set ℝ), IsSolution e S D → a ≤ b → b ≤ v → inSeg a b v ⊆ D →
      MeasurableSet U → U ⊆ Icc a b → 0 < B → 0 ≤ E →
      (∀ u ∈ U, u < vb u ∧ vb u ≤ v ∧ outSeg u (vb u) v ⊆ D) →
      (∀ u ∈ U, ρ * B ≤ S.r u (vb u) ∧ S.r u (vb u) ≤ B) →
      (∀ u ∈ U, 0 ≤ S.mu u (vb u) ∧ δ ≤ 1 - S.mu u v) →
      (∀ u ∈ U, S.m u (vb u) / S.r u (vb u) +
        ‖S.theta u (vb u) / S.lam u (vb u)‖ ^ 2 ≤ E) →
      (∀ u ∈ U, ∀ w ∈ Icc (vb u) v, ‖S.theta u w / S.lam u w‖ ≤ F) →
      (∫⁻ u in U, ENNReal.ofReal
        (2 * (-S.nu u v) * radialBoundaryMass S u (vb u) v /
          ((1 - S.mu u v) * S.r u v ^ 2))) ≤ ENNReal.ofReal (C * E) := by
  let q := 2 * (1 - F ^ 2) - 1
  let K := 1 + q⁻¹
  have hq : 0 < q := by dsimp [q]; linarith only [hp]
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨2 * K / (δ * ρ), by positivity, ?_⟩
  intro e a b v B E S D vb U hS hab hbv hin hU hsub hB hE hrows hrange hstop hbudget hy
  let β := 2 * K * B * E / δ
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hmass (u : ℝ) (hu : u ∈ U) : radialBoundaryMass S u (vb u) v ≤ K * B * E := by
    obtain ⟨huv, hvs, hs⟩ := hrows u hu
    have hrb := hS.r_pos (u, vb u) (hs ⟨rfl, le_rfl, hvs⟩) huv
    have hμ : S.mu u (vb u) = 2 * (S.m u (vb u) / S.r u (vb u)) := by dsimp [Fields.mu]; ring
    have hm0 : 0 ≤ S.m u (vb u) / S.r u (vb u) := by
      have hh := (hstop u hu).1
      rw [hμ] at hh
      linarith only [hh]
    have hmE : S.m u (vb u) / S.r u (vb u) ≤ E := by
      linarith only [hbudget u hu, sq_nonneg ‖S.theta u (vb u) / S.lam u (vb u)‖]
    have hyE : ‖S.theta u (vb u) / S.lam u (vb u)‖ ^ 2 ≤ E := by
      linarith only [hbudget u hu, hm0]
    have hmb : S.m u (vb u) ≤ S.r u (vb u) * E := by
      simpa only [mul_comm] using (div_le_iff₀ hrb).mp hmE
    have hscalar := boundary_scalar_mass_le hS huv hvs hs hF hp (hy u hu)
    have hscalar' : (∫ w in (vb u)..v, S.lam u w * ‖radialYBoundary S u (vb u) w‖ ^ 2) ≤
        S.r u (vb u) * E / q := hscalar.trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hyE hrb.le) hq.le)
    calc
      _ ≤ S.r u (vb u) * E + S.r u (vb u) * E / q := add_le_add hmb hscalar'
      _ = K * S.r u (vb u) * E := by dsimp [K]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hrange u hu).2 hK.le) hE
  have hradius (u : ℝ) (hu : u ∈ U) : ρ * B ≤ S.r u v := by
    obtain ⟨huv, hvs, hs⟩ := hrows u hu
    exact (hrange u hu).1.trans
      ((outgoing_radius_calculus hS huv.le hvs hs).2.monotoneOn
        ⟨le_rfl, hvs⟩ ⟨hvs, le_rfl⟩ hvs)
  calc
    _ ≤ ∫⁻ u in U, ENNReal.ofReal β * ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 2) := by
      apply setLIntegral_mono' hU
      intro u hu
      obtain ⟨huv, hvs, hs⟩ := hrows u hu
      have hr := hS.r_pos (u, v) (hs ⟨rfl, hvs, le_rfl⟩) (huv.trans_le hvs)
      have hn := (neg_pos.mpr (hS.nu_neg (u, v) (hs ⟨rfl, hvs, le_rfl⟩))).le
      have hg := hδ.trans_le (hstop u hu).2
      rw [← ENNReal.ofReal_mul hβ]
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ (2 * (-S.nu u v) * (K * B * E)) / ((1 - S.mu u v) * S.r u v ^ 2) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hmass u hu) (by positivity))
            (by positivity)
        _ = (2 * K * B * E * ((-S.nu u v) / S.r u v ^ 2)) / (1 - S.mu u v) := by
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring
        _ ≤ (2 * K * B * E * ((-S.nu u v) / S.r u v ^ 2)) / δ :=
          div_le_div_of_nonneg_left (by positivity) hδ (hstop u hu).2
        _ = _ := by dsimp [β]; ring
    _ = ENNReal.ofReal β * (∫⁻ u in U, ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 2)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal β * ENNReal.ofReal (1 / (ρ * B)) := by
      gcongr
      exact incoming_inverse_square_kernel hS hab hbv hin hU hsub (mul_pos hρ hB) hradius
    _ = _ := by
      rw [← ENNReal.ofReal_mul hβ]
      congr 1
      dsimp only [β]
      field_simp [hB.ne', hδ.ne', hρ.ne']


/-- [node prop:ct-interaction#incoming-optical-separation-kernel]
The finite endpoint `v - max s t` is retained through incoming integration.
The explicit final coefficient is `c⁻¹`, uniformly in both source labels,
every measurable contributing history, and its duration. The strict lower
label condition excludes only the coincident terminal pair `s = t = v`.
Source: `charged_SF_new_version.tex:L3766–L3773`. -/
theorem incoming_optical_separation_kernel {e : ℝ} {S : Fields}
    {D : Set (ℝ × ℝ)} (hS : IsSolution e S D)
    {a b v s t c : ℝ} (hab : a ≤ b) (hbv : b ≤ v)
    (hin : inSeg a b v ⊆ D) {U : Set ℝ} (hU : MeasurableSet U)
    (hsub : U ⊆ Icc a b) (hc : 0 < c) (hmin : min s t < v)
    (hmax : max s t ≤ v)
    (hlabels : ∀ u ∈ U, u < min s t ∧ outSeg u (min s t) v ⊆ D)
    (hlam : ∀ u ∈ U, ∀ x ∈ Icc (min s t) v, c ≤ S.lam u x) :
    (∀ u ∈ U, c * (v - min s t) ≤ S.r u v) ∧
      ENNReal.ofReal (v - max s t) *
          (∫⁻ u in U, ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 2)) ≤
        ENNReal.ofReal ((v - max s t) / (c * (v - min s t))) ∧
      ENNReal.ofReal ((v - max s t) / (c * (v - min s t))) ≤
        ENNReal.ofReal c⁻¹ := by
  have hr (u : ℝ) (hu : u ∈ U) := source_label_radius_bound hS
    (hlabels u hu).1 hmin.le (hlabels u hu).2 (hlam u hu)
  refine ⟨hr, ?_, ?_⟩
  · calc
      _ ≤ ENNReal.ofReal (v - max s t) *
          ENNReal.ofReal (1 / (c * (v - min s t))) := by
        gcongr
        exact incoming_inverse_square_kernel hS hab hbv hin hU hsub
          (mul_pos hc (sub_pos.mpr hmin)) hr
      _ = _ := by
        rw [← ENNReal.ofReal_mul (sub_nonneg.mpr hmax)]
        congr 1
        ring
  · apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ (mul_pos hc (sub_pos.mpr hmin))).mpr
    rw [inv_mul_cancel_left₀ hc.ne']
    exact sub_le_sub_left min_le_max v

private theorem radius_cube_moment {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) :
    (∫ v in a..b, S.lam u v * S.r u v ^ 2) =
      (S.r u b ^ 3 - S.r u a ^ 3) / 3 := by
  have h := (Local.IsSolution.out_section hS hua hab hs).1
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have hi := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab (cl.mul (cr.pow 2))
  have hd : ∀ᵐ v, v ∈ uIcc a b → HasDerivAt
      (fun x => S.r u x ^ 3 / 3) (S.lam u v * S.r u v ^ 2) v := by
    rw [← ae_restrict_iff' measurableSet_uIcc, uIcc_of_le hab]
    exact h.2.mono fun v hv => by
      convert (hv.pow 3).div_const 3 using 1
      ring
  have hac : AbsolutelyContinuousOnInterval (fun x => S.r u x ^ 3 / 3) a b := by
    convert ((h.1.mul h.1).mul h.1).const_mul (1 / 3 : ℝ) using 1
    funext x
    dsimp
    ring
  have he := hac.integral_eq_sub_of_ae_hasDerivAt_normed hi hd
  simpa only [Pi.mul_apply, Pi.pow_apply, sub_div] using he

/-- [internal]
The ordinary radial mass estimate with an explicit electric coefficient.
Conditional support for `prop:ct-interaction#radial-mass-reconstruction`;
its production consumer must derive and substitute the charge profile.
Here `A` is the charge profile coefficient `|Q| ≤ A r²`; in the stopped
exterior it is `Cq |e| M₀ F`. The coefficient `1/6` is universal, with no
dependence on the row length, stage duration, or physical data.
Source: `charged_SF_new_version.tex:L3747–L3751`. -/
theorem radial_mass_reconstruction_of_charge_profile {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b A : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D)
    (hmu : ∀ v ∈ Icc a b, 0 ≤ S.mu u v)
    (hA : 0 ≤ A) (hQ : ∀ v ∈ Icc a b, |S.Q u v| ≤ A * S.r u v ^ 2) :
    S.m u b ≤ S.m u a +
      (1 / 2) * (∫ v in a..b, S.lam u v * ‖S.theta u v / S.lam u v‖ ^ 2) +
      A ^ 2 / 6 * S.r u b ^ 3 := by
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have ct := Calculus.continuousOn_out_section hS.cont_theta hs
  have hl (v : ℝ) (hv : v ∈ Icc a b) := hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)
  have hr (v : ℝ) (hv : v ∈ Icc a b) :=
    hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
  have cy := ct.div (Complex.continuous_ofReal.comp_continuousOn cl)
    (fun v hv => Complex.ofReal_ne_zero.mpr (hl v hv).ne')
  have iy : IntervalIntegrable
      (fun v => S.lam u v * ‖S.theta u v / S.lam u v‖ ^ 2) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab (cl.mul (cy.norm.pow 2))
  have ir : IntervalIntegrable (fun v => S.lam u v * S.r u v ^ 2) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab (cl.mul (cr.pow 2))
  have he := (hS.eq_out u a b hua hab hs).2.2.1
  have hi := intervalIntegral.integral_mono_on hab he.1
    ((iy.const_mul (1 / 2)).add (ir.const_mul (A ^ 2 / 2))) (fun v hv => ?_)
  · rw [intervalIntegral.integral_add (iy.const_mul (1 / 2))
      (ir.const_mul (A ^ 2 / 2)), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, radius_cube_moment hS hua hab hs,
      ← he.2] at hi
    have hr0 := hr a ⟨le_rfl, hab⟩
    have hnonneg : 0 ≤ A ^ 2 * S.r u a ^ 3 := mul_nonneg (sq_nonneg _) (by positivity)
    nlinarith only [hi, hnonneg]
  · have hmass := Local.RelCharge.radial_mass_equation hS (hs ⟨rfl, hv⟩)
    have hq : S.Q u v ^ 2 ≤ A ^ 2 * S.r u v ^ 4 := by
      have hh := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hA (sq_nonneg _))).mpr (hQ v hv)
      simpa only [sq_abs, mul_pow, ← pow_mul] using hh
    have hqdiv : S.Q u v ^ 2 / S.r u v ^ 2 ≤ A ^ 2 * S.r u v ^ 2 := by
      apply (div_le_iff₀ (sq_pos_of_pos (hr v hv))).mpr
      calc
        _ ≤ A ^ 2 * S.r u v ^ 4 := hq
        _ = _ := by ring
    have hy : (1 - S.mu u v) * ‖S.theta u v / S.lam u v‖ ^ 2 ≤
        ‖S.theta u v / S.lam u v‖ ^ 2 := by
      nlinarith only [hmu v hv, sq_nonneg ‖S.theta u v / S.lam u v‖,
        mul_nonneg (hmu v hv) (sq_nonneg ‖S.theta u v / S.lam u v‖)]
    have hz := add_le_add hy hqdiv
    have hm := mul_le_mul_of_nonneg_left hz (hl v hv).le
    have hmass' := (div_eq_iff (hl v hv).ne').mp hmass
    nlinarith only [hm, hmass']

/-- [internal]
The electric upper mass `A² r³ / 6` has incoming optical cost at most
`A² R₀² / (6 δ)`. The coefficient depends only on the gap `δ`, uniformly
in the solution, charge profile coefficient, radius scale, history and
duration. Substituting `A = Cq |e| M₀ F` gives the stated `C ζ² F²` cost.
Conditional support for `prop:ct-interaction#electromagnetic-incoming-optical-cost`;
its production consumer must supply that charge profile substitution.
Source: `charged_SF_new_version.tex:L3752–L3753`. -/
theorem electromagnetic_incoming_optical_cost_of_radius_bound {e : ℝ} {S : Fields}
    {D : Set (ℝ × ℝ)} (hS : IsSolution e S D)
    {a b v R₀ A δ : ℝ} (hab : a ≤ b) (hbv : b ≤ v)
    (hs : inSeg a b v ⊆ D) {U : Set ℝ} (hU : MeasurableSet U)
    (hsub : U ⊆ Icc a b) (hR : 0 ≤ R₀) (hδ : 0 < δ)
    (hr : ∀ u ∈ U, 0 < S.r u v ∧ S.r u v ≤ R₀)
    (hgap : ∀ u ∈ U, δ ≤ 1 - S.mu u v) :
    (∫⁻ u in U, ENNReal.ofReal
      (2 * (-S.nu u v) * (A ^ 2 / 6 * S.r u v ^ 3) /
        ((1 - S.mu u v) * S.r u v ^ 2))) ≤
      ENNReal.ofReal (A ^ 2 * R₀ ^ 2 / (6 * δ)) := by
  have hk : 0 ≤ A ^ 2 / (3 * δ) := by positivity
  calc
    _ ≤ ∫⁻ u in U, ENNReal.ofReal
        (A ^ 2 / (3 * δ) * ((-S.nu u v) * S.r u v)) := by
      apply setLIntegral_mono' hU
      intro u hu
      apply ENNReal.ofReal_le_ofReal
      have hn : 0 ≤ -S.nu u v :=
        (neg_pos.mpr (hS.nu_neg (u, v)
          (hs ⟨(hsub hu).1, (hsub hu).2, rfl⟩))).le
      have hg : 0 < 1 - S.mu u v := hδ.trans_le (hgap u hu)
      calc
        _ = (A ^ 2 / 3 * ((-S.nu u v) * S.r u v)) / (1 - S.mu u v) := by
          field_simp [hg.ne', (hr u hu).1.ne']
          ring
        _ ≤ (A ^ 2 / 3 * ((-S.nu u v) * S.r u v)) / δ :=
          div_le_div_of_nonneg_left
            (mul_nonneg (by positivity) (mul_nonneg hn (hr u hu).1.le)) hδ (hgap u hu)
        _ = _ := by ring
    _ = ENNReal.ofReal (A ^ 2 / (3 * δ)) *
        ∫⁻ u in U, ENNReal.ofReal ((-S.nu u v) * S.r u v) := by
      simp_rw [ENNReal.ofReal_mul hk]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (A ^ 2 / (3 * δ)) * ENNReal.ofReal (R₀ ^ 2 / 2) := by
      gcongr
      exact fixed_label_radius_moment hS hab hbv hs hU hsub hR
        (fun u hu => ⟨(hr u hu).1.le, (hr u hu).2⟩)
    _ = _ := by
      rw [← ENNReal.ofReal_mul hk]
      congr 1
      ring

end EmcsfAcExtension.Global.InteractionEstimate

namespace EmcsfAcExtension.Global.InteractionEstimate

/-- [internal]
The actual derivative-source scalar mass retains the finite label endpoint
`b - max s t`. Its exact coefficient is `Λ c⁻²`, chosen before the
coupling, fields, row, envelope, radii, and durations. The envelope needs
only its given rowwise integrability and a.e. majorization; its measurable
representative is selected inside the proof and changes no integral.
Source: charged_SF_new_version.tex:L3756–L3765. -/
theorem source_mass_finite_endpoint (c Λ F : ℝ) (hc : 0 < c) (hΛ : 0 < Λ)
    (hF : 0 ≤ F) (hF1 : F ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (e : ℝ) (S : Fields) (D : Set (ℝ × ℝ))
      (u a b : ℝ) (g : ℝ → ℝ), IsSolution e S D → u < a → a ≤ b → outSeg u a b ⊆ D →
      (∀ v ∈ Icc a b, c ≤ S.lam u v ∧ S.lam u v ≤ Λ) →
      (∀ v ∈ Icc a b, ‖S.theta u v / S.lam u v‖ ≤ F) →
      IntervalIntegrable g volume a b →
      (∀ᵐ v ∂volume.restrict (Icc a b), ‖weightedJ S u v‖ ≤ g v) →
      (∫⁻ x in Icc a b, ENNReal.ofReal (S.lam u x * ‖radialYSource S u a x‖ ^ 2)) ≤
        ENNReal.ofReal C * (∫⁻ s in Icc a b, ∫⁻ t in Icc a b,
          ENNReal.ofReal (b - max s t) * ENNReal.ofReal (g s) * ENNReal.ofReal (g t)) := by
  refine ⟨Λ * c⁻¹ ^ 2, by positivity, ?_⟩
  intro e S D u a b g hS hua hab hs hlam hy hg hmajor
  let μ := volume.restrict (Icc a b)
  have ig : Integrable g μ := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hg
  have hmeas : AEMeasurable (fun v => ENNReal.ofReal (g v)) μ :=
    ENNReal.continuous_ofReal.measurable.comp_aemeasurable ig.aestronglyMeasurable.aemeasurable
  let G := hmeas.mk (fun v => ENNReal.ofReal (g v))
  have hG : Measurable G := hmeas.measurable_mk
  have hGeq : (fun v => ENNReal.ofReal (g v)) =ᵐ[μ] G := hmeas.ae_eq_mk
  have hg0 : ∀ᵐ v ∂μ, 0 ≤ g v := hmajor.mono fun _ h => (norm_nonneg _).trans h
  have hprefix (x : ℝ) (hx : x ∈ Icc a b) :
      ENNReal.ofReal (∫ t in a..x, g t) = ∫⁻ t in Icc a x, G t := by
    have hsub : Icc a x ⊆ Icc a b := Icc_subset_Icc le_rfl hx.2
    have hsub' : uIcc a x ⊆ uIcc a b := by
      simpa only [uIcc_of_le hx.1, uIcc_of_le hab] using hsub
    have igx := (intervalIntegrable_iff_integrableOn_Icc_of_le hx.1).mp (hg.mono_set hsub')
    have h0x := hg0.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
    rw [intervalIntegral.integral_of_le hx.1, ← integral_Icc_eq_integral_Ioc,
      ofReal_integral_eq_lintegral_ofReal igx h0x]
    exact lintegral_congr_ae (hGeq.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)))
  have hdouble : (∫⁻ s in Icc a b, ∫⁻ t in Icc a b,
      ENNReal.ofReal (b - max s t) * G s * G t) =
      ∫⁻ s in Icc a b, ∫⁻ t in Icc a b,
        ENNReal.ofReal (b - max s t) * ENNReal.ofReal (g s) * ENNReal.ofReal (g t) := by
    apply lintegral_congr_ae
    filter_upwards [hGeq] with s hs
    apply lintegral_congr_ae
    filter_upwards [hGeq] with t ht
    rw [hs, ht]
  calc
    _ ≤ ∫⁻ x in Icc a b, ENNReal.ofReal (Λ * c⁻¹ ^ 2) *
        (∫⁻ t in Icc a x, G t) ^ 2 := by
      apply setLIntegral_mono' measurableSet_Icc
      intro x hx
      have hsub : Icc a x ⊆ Icc a b := Icc_subset_Icc le_rfl hx.2
      have hsub' : uIcc a x ⊆ uIcc a b := by
        simpa only [uIcc_of_le hx.1, uIcc_of_le hab] using hsub
      have hsrc := (outgoing_scalar_pointwise hS hua hx.1
        (fun p hp => hs ⟨hp.1, hp.2.1, hp.2.2.trans hx.2⟩) hc hF hF1
        (fun v hv => (hlam v (hsub hv)).1) (fun v hv => hy v (hsub hv)) g
        (hg.mono_set hsub')
        (hmajor.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)))).1
      have hnorm : ENNReal.ofReal ‖radialYSource S u a x‖ ≤
          ENNReal.ofReal c⁻¹ * (∫⁻ t in Icc a x, G t) := by
        apply (ENNReal.ofReal_le_ofReal hsrc).trans_eq
        rw [ENNReal.ofReal_mul (inv_nonneg.mpr hc.le), hprefix x hx]
      have hl := (hS.lam_pos (u, x) (hs ⟨rfl, hx⟩)).le
      rw [ENNReal.ofReal_mul hl, ENNReal.ofReal_pow (norm_nonneg _) 2,
        ENNReal.ofReal_mul hΛ.le, ENNReal.ofReal_pow (inv_nonneg.mpr hc.le) 2]
      calc
        _ ≤ ENNReal.ofReal Λ * (ENNReal.ofReal c⁻¹ * (∫⁻ t in Icc a x, G t)) ^ 2 := by
          gcongr
          exact (hlam x hx).2
        _ = _ := by ring
    _ = ENNReal.ofReal (Λ * c⁻¹ ^ 2) *
        (∫⁻ x in Icc a b, (∫⁻ t in Icc a x, G t) ^ 2) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by rw [lintegral_prefix_square_eq hab G hG, hdouble]

end EmcsfAcExtension.Global.InteractionEstimate

namespace EmcsfAcExtension.Global.InteractionEstimate

/-- [internal]
The ordinary mass reconstruction under the stopped charge profile.
The positive coefficient depends only on `Cq` and is chosen before coupling,
scalar background, solution, row, and all physical scales.
Source: charged_SF_new_version.tex:L3747–L3751. -/
theorem radial_mass_reconstruction (Cq : ℝ) (hCq : 0 ≤ Cq) :
    ∃ C : ℝ, 0 < C ∧ ∀ (e M F : ℝ) (S : Fields) (D : Set (ℝ × ℝ))
      (u a b : ℝ), IsSolution e S D → u < a → a ≤ b → outSeg u a b ⊆ D →
      0 ≤ M → 0 ≤ F → (∀ v ∈ Icc a b, 0 ≤ S.mu u v) →
      (∀ v ∈ Icc a b, |S.Q u v| / S.r u v ^ 2 ≤ Cq * |e| * M * F) →
      S.m u b ≤ S.m u a +
        (1 / 2) * (∫ v in a..b, S.lam u v * ‖S.theta u v / S.lam u v‖ ^ 2) +
        C * e ^ 2 * M ^ 2 * F ^ 2 * S.r u b ^ 3 := by
  refine ⟨Cq ^ 2 / 6 + 1, by positivity, ?_⟩
  intro e M F S D u a b hS hua hab hs hM hF hmu hQ
  have hr := hS.r_pos (u, b) (hs ⟨rfl, hab, le_rfl⟩) (hua.trans_le hab)
  have hbound := radial_mass_reconstruction_of_charge_profile hS hua hab hs hmu
    (by positivity : 0 ≤ Cq * |e| * M * F) (fun v hv =>
      (div_le_iff₀ (sq_pos_of_pos (hS.r_pos (u, v) (hs ⟨rfl, hv⟩)
        (hua.trans_le hv.1)))).mp (hQ v hv))
  apply hbound.trans
  apply add_le_add le_rfl
  have heq : (Cq * |e| * M * F) ^ 2 / 6 * S.r u b ^ 3 =
      (Cq ^ 2 / 6) * e ^ 2 * M ^ 2 * F ^ 2 * S.r u b ^ 3 := by
    rw [mul_pow, mul_pow, mul_pow, sq_abs]
    ring
  rw [heq]
  have hnonneg : 0 ≤ e ^ 2 * M ^ 2 * F ^ 2 * S.r u b ^ 3 := by positivity
  nlinarith only [hnonneg]

/-- [node prop:ct-interaction#electromagnetic-incoming-optical-cost]
Incoming cost of the explicit electric upper mass from the charge profile.
The positive constant depends only on `δ,Cq`, before coupling, scalar
background, radius scale, solution, measurable history, and its duration.
The remainder is the exact `A²r³/6` from radial mass reconstruction, with
`A = Cq |e| M F`; its cost has no duration factor.
Source: charged_SF_new_version.tex:L3752–L3753. -/
theorem electromagnetic_incoming_optical_cost (δ Cq : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (e M F R₀ a b v : ℝ) (S : Fields)
      (D : Set (ℝ × ℝ)) (U : Set ℝ), IsSolution e S D → a ≤ b → b ≤ v →
      inSeg a b v ⊆ D → MeasurableSet U → U ⊆ Icc a b → 0 ≤ R₀ →
      (∀ u ∈ U, 0 < S.r u v ∧ S.r u v ≤ R₀) →
      (∀ u ∈ U, δ ≤ 1 - S.mu u v) →
      (∫⁻ u in U, ENNReal.ofReal
        (2 * (-S.nu u v) * ((Cq * |e| * M * F) ^ 2 / 6 * S.r u v ^ 3) /
          ((1 - S.mu u v) * S.r u v ^ 2))) ≤
        ENNReal.ofReal (C * Local.sigma e M (2 * R₀) * F ^ 2) := by
  refine ⟨Cq ^ 2 / (6 * δ) + 1, by positivity, ?_⟩
  intro e M F R₀ a b v S D U hS hab hbv hs hU hsub hR hr hg
  apply (electromagnetic_incoming_optical_cost_of_radius_bound hS hab hbv hs
    hU hsub hR hδ hr hg).trans
  apply ENNReal.ofReal_le_ofReal
  rw [ct_zeta]
  have heq : (Cq * |e| * M * F) ^ 2 * R₀ ^ 2 / (6 * δ) =
      (Cq ^ 2 / (6 * δ)) * (e ^ 2 * M ^ 2 * R₀ ^ 2 * F ^ 2) := by
    rw [mul_pow, mul_pow, mul_pow, sq_abs]
    ring
  rw [heq]
  have hnonneg : 0 ≤ e ^ 2 * M ^ 2 * R₀ ^ 2 * F ^ 2 := by positivity
  nlinarith only [hnonneg]

end EmcsfAcExtension.Global.InteractionEstimate
