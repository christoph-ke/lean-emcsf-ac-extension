/- Copyright (c) 2026. All rights reserved. -/

module

public import EmcsfAcExtension.Frozen.IsSolution
import EmcsfAcExtension.Global.Calculus.Endpoint
import EmcsfAcExtension.Infra.Level.Substitution
import EmcsfAcExtension.Infra.Level.Clock
import EmcsfAcExtension.Global.Gap.AnnularFlux
import EmcsfAcExtension.Global.Interaction.PairSource
import EmcsfAcExtension.Infra.Mixed.MomentKernel
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-!
# Incoming radius kernels on measurable histories

Radius substitution is performed on the actual contributing set, which may
be disconnected. This proves the incoming kernel and radius moment used at
`charged_SF_new_version.tex:L3649–L3656`, `L3739–L3742`, and `L3766–L3773`.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension.Global.InteractionEstimate

/-- [internal]
The incoming radius is differentiable within a proper closed characteristic
segment, including existing axis endpoints, and is nonincreasing there.
The derivative and its sign follow from the frozen integral equations. -/
theorem incoming_radius_calculus {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a b v : ℝ} (hab : a ≤ b) (hbv : b ≤ v)
    (hs : inSeg a b v ⊆ D) :
    (∀ u ∈ Icc a b, HasDerivWithinAt (fun t => S.r t v) (S.nu u v) (Icc a b) u) ∧
      AntitoneOn (fun u => S.r u v) (Icc a b) := by
  have hc := Calculus.continuousOn_in_section hS.cont_nu hs
  have hform (x : ℝ) (hx : x ∈ Icc a b) :=
    (Calculus.in_integralForm hS hx.1 (hx.2.trans hbv)
      (fun p hp => hs ⟨hp.1, hp.2.1.trans hx.2, hp.2.2⟩)).1
  constructor
  · intro u hu
    have hd := (Level.hasDerivWithinAt_integralClock hab hc hu).const_add (S.r a v)
    apply hd.congr_of_mem _ hu
    intro x hx
    exact (hform x hx).eq_add_integral
  · intro x hx y hy hxy
    have hseg : inSeg x y v ⊆ D :=
      fun p hp => hs ⟨hx.1.trans hp.1, hp.2.1.trans hy.2, hp.2.2⟩
    have he := (Calculus.in_integralForm hS hxy (hy.2.trans hbv) hseg).1
    have hn : 0 ≤ ∫ u in x..y, -S.nu u v :=
      intervalIntegral.integral_nonneg hxy (fun u hu =>
        (neg_pos.mpr (hS.nu_neg (u, v) (hseg ⟨hu.1, hu.2, rfl⟩))).le)
    rw [intervalIntegral.integral_neg, ← he.2] at hn
    exact sub_nonpos.mp (neg_nonneg.mp hn)

private theorem lintegral_radius_moment (R : ℝ) (hR : 0 ≤ R) :
    (∫⁻ x in Icc (0 : ℝ) R, ENNReal.ofReal x) = ENNReal.ofReal (R ^ 2 / 2) := by
  have hi : Integrable (fun x : ℝ => x) (volume.restrict (Icc (0 : ℝ) R)) :=
    continuous_id.continuousOn.integrableOn_Icc
  have hn : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) R)] (fun x : ℝ => x) :=
    ae_restrict_of_forall_mem measurableSet_Icc (fun x hx => hx.1)
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hR]
  congr 1
  norm_num [integral_id]

/-- [node prop:ct-interaction#fixed-label-radius-moment]
On any measurable contributing history in a proper incoming segment, the
radius moment is bounded by `R₀² / 2`. The coefficient is universal and is
independent of the history, its number of components, and its duration.
Source: `charged_SF_new_version.tex:L3739–L3742`. -/
theorem fixed_label_radius_moment {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a b v R₀ : ℝ} (hab : a ≤ b) (hbv : b ≤ v)
    (hs : inSeg a b v ⊆ D) {U : Set ℝ} (hU : MeasurableSet U)
    (hsub : U ⊆ Icc a b) (hR : 0 ≤ R₀)
    (hr : ∀ u ∈ U, 0 ≤ S.r u v ∧ S.r u v ≤ R₀) :
    (∫⁻ u in U, ENNReal.ofReal ((-S.nu u v) * S.r u v)) ≤
      ENNReal.ofReal (R₀ ^ 2 / 2) := by
  obtain ⟨hd, hm⟩ := incoming_radius_calculus hS hab hbv hs
  have he := Level.lintegral_image_anti hU
    (fun u hu => (hd u (hsub hu)).mono hsub) (hm.mono hsub)
    (fun x => ENNReal.ofReal x)
  calc
    _ = ∫⁻ u in U, ENNReal.ofReal (-S.nu u v) * ENNReal.ofReal (S.r u v) := by
      apply setLIntegral_congr_fun hU
      intro u hu
      exact ENNReal.ofReal_mul (by
        exact (neg_pos.mpr (hS.nu_neg (u, v)
          (hs ⟨(hsub hu).1, (hsub hu).2, rfl⟩))).le)
    _ = ∫⁻ x in (fun u => S.r u v) '' U, ENNReal.ofReal x := he.symm
    _ ≤ ∫⁻ x in Icc (0 : ℝ) R₀, ENNReal.ofReal x := by
      apply lintegral_mono_set
      rintro x ⟨u, hu, rfl⟩
      exact hr u hu
    _ = _ := lintegral_radius_moment R₀ hR

private theorem lintegral_inv_sq_tail {L : ℝ} (hL : 0 < L) :
    (∫⁻ x in Ici L, ENNReal.ofReal (1 / x ^ 2)) = ENNReal.ofReal (1 / L) := by
  have hi : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ioi L) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hL
  have heq : (fun x : ℝ => 1 / x ^ 2) = fun x : ℝ => x ^ (-2 : ℝ) := by
    funext x
    norm_num [Real.rpow_neg_natCast]
  rw [Measure.restrict_congr_set Ioi_ae_eq_Ici.symm]
  simp_rw [show ∀ x : ℝ, 1 / x ^ 2 = x ^ (-2 : ℝ) from fun x => congrFun heq x]
  rw [
    ← ofReal_integral_eq_lintegral_ofReal hi
      (ae_restrict_of_forall_mem measurableSet_Ioi
        (fun x hx => Real.rpow_nonneg (hL.trans hx).le _)),
    integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hL]
  congr 1
  norm_num [Real.rpow_neg_one]

/-- [internal]
Inverse-square incoming kernel on an arbitrary measurable history whose
radii are at least `L > 0`. Its exact coefficient is `1 / L`, independent of
the history and duration. This is the substitution step in the ordered pair
and finite-endpoint optical kernels. -/
theorem incoming_inverse_square_kernel {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a b v L : ℝ} (hab : a ≤ b) (hbv : b ≤ v)
    (hs : inSeg a b v ⊆ D) {U : Set ℝ} (hU : MeasurableSet U)
    (hsub : U ⊆ Icc a b) (hL : 0 < L) (hr : ∀ u ∈ U, L ≤ S.r u v) :
    (∫⁻ u in U, ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 2)) ≤
      ENNReal.ofReal (1 / L) := by
  obtain ⟨hd, hm⟩ := incoming_radius_calculus hS hab hbv hs
  have he := Level.lintegral_image_anti hU
    (fun u hu => (hd u (hsub hu)).mono hsub) (hm.mono hsub)
    (fun x => ENNReal.ofReal (1 / x ^ 2))
  calc
    _ = ∫⁻ u in U, ENNReal.ofReal (-S.nu u v) *
        ENNReal.ofReal (1 / S.r u v ^ 2) := by
      apply setLIntegral_congr_fun hU
      intro u hu
      dsimp only
      rw [← ENNReal.ofReal_mul (by
        exact (neg_pos.mpr (hS.nu_neg (u, v)
          (hs ⟨(hsub hu).1, (hsub hu).2, rfl⟩))).le)]
      congr 1
      ring
    _ = ∫⁻ x in (fun u => S.r u v) '' U, ENNReal.ofReal (1 / x ^ 2) := he.symm
    _ ≤ ∫⁻ x in Ici L, ENNReal.ofReal (1 / x ^ 2) := by
      apply lintegral_mono_set
      rintro x ⟨u, hu, rfl⟩
      exact hr u hu
    _ = _ := lintegral_inv_sq_tail hL

/-- [internal]
The incoming half of the ordered two-label kernel retains `s - t` until
after substitution. The explicit coefficient `c⁻¹` is uniform in both
labels, all measurable histories, and all stage durations.
Source: `charged_SF_new_version.tex:L3649–L3656`. -/
theorem ordered_incoming_kernel {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a b s t c : ℝ} (hab : a ≤ b) (hbs : b ≤ s)
    (hs : inSeg a b s ⊆ D) {U : Set ℝ} (hU : MeasurableSet U)
    (hsub : U ⊆ Icc a b) (hc : 0 < c) (hts : t < s)
    (hr : ∀ u ∈ U, c * (s - t) ≤ S.r u s) :
    ENNReal.ofReal (s - t) *
        (∫⁻ u in U, ENNReal.ofReal ((-S.nu u s) / S.r u s ^ 2)) ≤
      ENNReal.ofReal c⁻¹ := by
  calc
    _ ≤ ENNReal.ofReal (s - t) * ENNReal.ofReal (1 / (c * (s - t))) := by
      gcongr
      exact incoming_inverse_square_kernel hS hab hbs hs hU hsub
        (mul_pos hc (sub_pos.mpr hts)) hr
    _ = _ := by
      rw [← ENNReal.ofReal_mul (sub_pos.mpr hts).le]
      congr 1
      field_simp [hc.ne', (sub_pos.mpr hts).ne']

/-- [internal]
The actual incoming expansion grows by at most the radius ratio to the
power `ε`. The estimate follows from the frozen logarithmic equations and
`μ / (1 - μ) ≤ ε`; no growth bound is assumed. The coefficient is exactly
one, uniformly in the solution, coupling and both row endpoints.
Source: `charged_SF_new_version.tex:L3647–L3650`; internal project record (growth). -/
theorem outgoing_expansion_growth {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b ε : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D)
    (hμ : ∀ v ∈ Icc a b, S.mu u v / (1 - S.mu u v) ≤ ε) :
    -S.nu u b ≤ (-S.nu u a) * (S.r u b / S.r u a) ^ ε := by
  have hn := Gap.log_neg_nu_integralForm hS hua hab hs
  have hr := Gap.log_radius_integralForm hS hua hab hs
  have hi := intervalIntegral.integral_mono_on hab hn.1 (hr.1.const_mul ε)
    (fun v hv => ?_)
  · rw [intervalIntegral.integral_const_mul, ← hn.2, ← hr.2] at hi
    have hna := neg_pos.mpr (hS.nu_neg (u, a) (hs ⟨rfl, le_rfl, hab⟩))
    have hnb := neg_pos.mpr (hS.nu_neg (u, b) (hs ⟨rfl, hab, le_rfl⟩))
    have hra := hS.r_pos (u, a) (hs ⟨rfl, le_rfl, hab⟩) hua
    have hrb := hS.r_pos (u, b) (hs ⟨rfl, hab, le_rfl⟩) (hua.trans_le hab)
    have hquot : (-S.nu u b) / (-S.nu u a) ≤ (S.r u b / S.r u a) ^ ε := by
      calc
        _ = Real.exp (Real.log (-S.nu u b) - Real.log (-S.nu u a)) := by
          rw [Real.exp_sub, Real.exp_log hna, Real.exp_log hnb]
        _ ≤ Real.exp (ε * (Real.log (S.r u b) - Real.log (S.r u a))) :=
          Real.exp_le_exp.mpr hi
        _ = _ := by
          rw [Real.rpow_def_of_pos (div_pos hrb hra), Real.log_div hrb.ne' hra.ne']
          congr 1
          ring
    simpa only [mul_comm] using (div_le_iff₀ hna).mp hquot
  · have hp : (u, v) ∈ D := hs ⟨rfl, hv⟩
    have hvpos := hS.r_pos (u, v) hp (hua.trans_le hv.1)
    have hl := hS.lam_pos (u, v) hp
    have hg := hS.one_sub_mu_pos (u, v) hp
    have hq : 0 ≤ S.Q u v ^ 2 / S.r u v ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
    have hnum : (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) /
        (1 - S.mu u v) ≤ ε :=
      (div_le_div_of_nonneg_right (sub_le_self _ hq) hg.le).trans (hμ v hv)
    calc
      _ = (S.lam u v / S.r u v) *
          ((S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v)) := by
        field_simp [hg.ne', hvpos.ne']
      _ ≤ (S.lam u v / S.r u v) * ε :=
        mul_le_mul_of_nonneg_left hnum (div_nonneg hl.le hvpos.le)
      _ = _ := mul_comm _ _

private theorem outer_kernel_power_identity {x y ε : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (x / y) ^ ε / x ^ 3 =
      (1 / y ^ 2) * (1 / x) * (y / x) ^ (2 - ε) := by
  rw [Real.rpow_sub (div_pos hy hx), Real.rpow_two,
    Real.div_rpow hx.le hy.le, Real.div_rpow hy.le hx.le]
  field_simp [(Real.rpow_pos_of_pos hx ε).ne', (Real.rpow_pos_of_pos hy ε).ne']

/-- [internal]
The actual outgoing inverse-cube kernel has coefficient
`1 / (c * (2 - ε))` times `(-ν_a) / r_a²`, uniformly in the solution,
coupling, radius scale and row duration. Expansion growth is derived from
the frozen equations before the radial moment with exponent `2 - ε` is
used. Source: `charged_SF_new_version.tex:L3647–L3653`. -/
theorem outgoing_inverse_cube_kernel {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b c ε : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) (hc : 0 < c) (hε : ε < 2)
    (hlam : ∀ v ∈ Icc a b, c ≤ S.lam u v)
    (hμ : ∀ v ∈ Icc a b, S.mu u v / (1 - S.mu u v) ≤ ε) :
    (∫⁻ v in Icc a b, ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 3)) ≤
      ENNReal.ofReal ((-S.nu u a) / (c * (2 - ε) * S.r u a ^ 2)) := by
  have hp : 0 < 2 - ε := sub_pos.mpr hε
  have hra := hS.r_pos (u, a) (hs ⟨rfl, le_rfl, hab⟩) hua
  have hna := neg_pos.mpr (hS.nu_neg (u, a) (hs ⟨rfl, le_rfl, hab⟩))
  have hk : 0 ≤ (-S.nu u a) / (c * S.r u a ^ 2) := by positivity
  obtain ⟨_, hm⟩ := outgoing_radius_calculus hS hua.le hab hs
  have hrow := (Calculus.out_section hS hua.le hab hs).1
  have hmoment := Mixed.lintegral_radial_moment_mass_le hab hp hrow.1 hra hm.monotoneOn
    (fun v hv => (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)).le) (hrow.2.mono fun _ hv => hv.deriv)
  calc
    _ ≤ ∫⁻ v in Icc a b, ENNReal.ofReal ((-S.nu u a) / (c * S.r u a ^ 2)) *
        (ENNReal.ofReal (S.lam u v / S.r u v) *
          ENNReal.ofReal ((S.r u a / S.r u v) ^ (2 - ε))) := by
      apply setLIntegral_mono' measurableSet_Icc
      intro v hv
      have hr := hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
      have hl := hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)
      have hs' : outSeg u a v ⊆ D :=
        fun p hp' => hs ⟨hp'.1, hp'.2.1, hp'.2.2.trans hv.2⟩
      have hgrowth := outgoing_expansion_growth hS hua hv.1 hs'
        (fun x hx => hμ x ⟨hx.1, hx.2.trans hv.2⟩)
      rw [← ENNReal.ofReal_mul (div_nonneg hl.le hr.le), ← ENNReal.ofReal_mul hk]
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ (-S.nu u a) * (S.r u v / S.r u a) ^ ε / S.r u v ^ 3 :=
          div_le_div_of_nonneg_right hgrowth (by positivity)
        _ = (-S.nu u a) / S.r u a ^ 2 * (1 / S.r u v) *
            (S.r u a / S.r u v) ^ (2 - ε) := by
          rw [mul_div_assoc, outer_kernel_power_identity hr hra]
          ring
        _ ≤ _ := by
          have hle : 1 ≤ S.lam u v / c := (le_div_iff₀ hc).mpr (by simpa using hlam v hv)
          have hnonneg : 0 ≤ (-S.nu u a) / S.r u a ^ 2 * (1 / S.r u v) *
              (S.r u a / S.r u v) ^ (2 - ε) := by positivity
          have hh := mul_le_mul_of_nonneg_left hle hnonneg
          convert hh using 1 <;> ring
    _ = ENNReal.ofReal ((-S.nu u a) / (c * S.r u a ^ 2)) *
        ∫⁻ v in Icc a b, ENNReal.ofReal (S.lam u v / S.r u v) *
          ENNReal.ofReal ((S.r u a / S.r u v) ^ (2 - ε)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((-S.nu u a) / (c * S.r u a ^ 2)) * ENNReal.ofReal (1 / (2 - ε)) := by
      gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_mul hk]
      congr 1
      field_simp [hc.ne', hp.ne', hra.ne']

/-- [node prop:ct-interaction#ordered-two-label-kernels]
Both kernels for the actual contributing histories of an ordered source
pair `t ≤ s`, including coincident labels. The outgoing coefficient is `1 / (c * (2 - ε))`; the
incoming coefficient is `c⁻¹`. They are uniform in the solution, coupling,
labels, measurable history, number of its components and stage duration.
The radius separation and expansion growth are derived from the frozen
equations before either radial kernel is used.
Source: `charged_SF_new_version.tex:L3647–L3656`. -/
theorem ordered_two_label_kernels {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a b s t c ε : ℝ} (hab : a ≤ b) (hbs : b ≤ s)
    (hin : inSeg a b s ⊆ D) {U : Set ℝ} (hU : MeasurableSet U)
    (hsub : U ⊆ Icc a b) (hc : 0 < c) (hε : ε < 2) (hts : t ≤ s) (hs0 : s ≤ 0)
    (hgeom : ∀ u ∈ U, u < t ∧ outSeg u t 0 ⊆ D)
    (hlam : ∀ u ∈ U, ∀ v ∈ Icc t 0, c ≤ S.lam u v)
    (hμ : ∀ u ∈ U, ∀ v ∈ Icc t 0, S.mu u v / (1 - S.mu u v) ≤ ε) :
    (∀ u ∈ U,
      (∫⁻ v in Icc s 0, ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 3)) ≤
        ENNReal.ofReal ((-S.nu u s) / (c * (2 - ε) * S.r u s ^ 2))) ∧
      ENNReal.ofReal (s - t) *
        (∫⁻ u in U, ENNReal.ofReal ((-S.nu u s) / S.r u s ^ 2)) ≤
          ENNReal.ofReal c⁻¹ := by
  constructor
  · intro u hu
    exact outgoing_inverse_cube_kernel hS ((hgeom u hu).1.trans_le hts) hs0
      (fun p hp => (hgeom u hu).2 ⟨hp.1, hts.trans hp.2.1, hp.2.2⟩) hc hε
      (fun v hv => hlam u hu v ⟨hts.trans hv.1, hv.2⟩)
      (fun v hv => hμ u hu v ⟨hts.trans hv.1, hv.2⟩)
  · rcases hts.eq_or_lt with heq | hlt
    · simp only [heq, sub_self, ENNReal.ofReal_zero, zero_mul]
      exact zero_le
    apply ordered_incoming_kernel hS hab hbs hin hU hsub hc hlt
    intro u hu
    have hs : outSeg u t s ⊆ D :=
      fun p hp => (hgeom u hu).2 ⟨hp.1, hp.2.1, hp.2.2.trans hs0⟩
    have he := (hS.eq_out u t s (hgeom u hu).1 hts hs).1
    have hi := intervalIntegral.integral_mono_on hts
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => c) volume t s)
      he.1 (fun v hv => hlam u hu v ⟨hv.1, hv.2.trans hs0⟩)
    rw [intervalIntegral.integral_const, smul_eq_mul, ← he.2] at hi
    have hr := hS.r_pos (u, t) (hs ⟨rfl, le_rfl, hts⟩) (hgeom u hu).1
    nlinarith only [hi, hr]

end EmcsfAcExtension.Global.InteractionEstimate

namespace EmcsfAcExtension.Global.InteractionEstimate

/-- [internal]
Incoming power tail on an arbitrary measurable contributing history.
The coefficient `1/(-k-1)` depends only on the fixed exponent `k < -1`;
the lower radius occurs with its exact homogeneous power. There is no
component count or duration factor. This is the substitution used by
internal project record's source/boundary curvature kernel `(K3)`. -/
theorem incoming_power_tail {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a b v L k : ℝ} (hab : a ≤ b) (hbv : b ≤ v)
    (hs : inSeg a b v ⊆ D) {U : Set ℝ} (hU : MeasurableSet U)
    (hsub : U ⊆ Icc a b) (hL : 0 < L) (hk : k < -1)
    (hr : ∀ u ∈ U, L ≤ S.r u v) :
    (∫⁻ u in U, ENNReal.ofReal ((-S.nu u v) * (S.r u v) ^ k)) ≤
      ENNReal.ofReal (L ^ (k + 1) / (-k - 1)) := by
  obtain ⟨hd, hm⟩ := incoming_radius_calculus hS hab hbv hs
  have he := Level.lintegral_image_anti hU
    (fun u hu => (hd u (hsub hu)).mono hsub) (hm.mono hsub)
    (fun x => ENNReal.ofReal (x ^ k))
  calc
    _ = ∫⁻ u in U, ENNReal.ofReal (-S.nu u v) * ENNReal.ofReal ((S.r u v) ^ k) := by
      apply setLIntegral_congr_fun hU
      intro u hu
      dsimp only
      exact ENNReal.ofReal_mul (neg_pos.mpr (hS.nu_neg (u, v)
        (hs ⟨(hsub hu).1, (hsub hu).2, rfl⟩))).le
    _ = ∫⁻ x in (fun u => S.r u v) '' U, ENNReal.ofReal (x ^ k) := he.symm
    _ ≤ ∫⁻ x in Ici L, ENNReal.ofReal (x ^ k) := by
      apply lintegral_mono_set
      rintro x ⟨u, hu, rfl⟩
      exact hr u hu
    _ = _ := by
      rw [Measure.restrict_congr_set Ioi_ae_eq_Ici.symm,
        ← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt hk hL)
          (ae_restrict_of_forall_mem measurableSet_Ioi
            (fun x hx => Real.rpow_nonneg (hL.trans hx).le _)),
        integral_Ioi_rpow_of_lt hk hL]
      congr 1
      rw [show -k - 1 = -(k + 1) by ring, div_neg, neg_div]

end EmcsfAcExtension.Global.InteractionEstimate

namespace EmcsfAcExtension.Global.InteractionEstimate

/-- [internal]
The outgoing kernel retaining any fixed radial decay exponent `α`.
Its exact coefficient is `1/(c(2+α-ε))`, uniform in all physical data,
positive radii, row lengths, and durations. The expansion growth is
derived from the frozen equations before applying the radial moment.
Source: internal project record auxiliary formula `(outer)`. -/
theorem outgoing_inverse_cube_power_kernel {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b c ε α : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) (hc : 0 < c) (hp : 0 < 2 + α - ε)
    (hlam : ∀ v ∈ Icc a b, c ≤ S.lam u v)
    (hμ : ∀ v ∈ Icc a b, S.mu u v / (1 - S.mu u v) ≤ ε) :
    (∫⁻ v in Icc a b, ENNReal.ofReal
      (((-S.nu u v) / S.r u v ^ 3) * (S.r u a / S.r u v) ^ α)) ≤
      ENNReal.ofReal ((-S.nu u a) / (c * (2 + α - ε) * S.r u a ^ 2)) := by
  have hra := hS.r_pos (u, a) (hs ⟨rfl, le_rfl, hab⟩) hua
  have hna := neg_pos.mpr (hS.nu_neg (u, a) (hs ⟨rfl, le_rfl, hab⟩))
  have hk : 0 ≤ (-S.nu u a) / (c * S.r u a ^ 2) := by positivity
  obtain ⟨_, hm⟩ := outgoing_radius_calculus hS hua.le hab hs
  have hrow := (Calculus.out_section hS hua.le hab hs).1
  have hmoment := Mixed.lintegral_radial_moment_mass_le hab hp hrow.1 hra hm.monotoneOn
    (fun v hv => (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)).le) (hrow.2.mono fun _ hv => hv.deriv)
  calc
    _ ≤ ∫⁻ v in Icc a b, ENNReal.ofReal ((-S.nu u a) / (c * S.r u a ^ 2)) *
        (ENNReal.ofReal (S.lam u v / S.r u v) *
          ENNReal.ofReal ((S.r u a / S.r u v) ^ (2 + α - ε))) := by
      apply setLIntegral_mono' measurableSet_Icc
      intro v hv
      have hr := hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
      have hl := hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)
      have hgrowth := outgoing_expansion_growth hS hua hv.1
        (fun p hp' => hs ⟨hp'.1, hp'.2.1, hp'.2.2.trans hv.2⟩)
        (fun x hx => hμ x ⟨hx.1, hx.2.trans hv.2⟩)
      rw [← ENNReal.ofReal_mul (div_nonneg hl.le hr.le), ← ENNReal.ofReal_mul hk]
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ ((-S.nu u a) * (S.r u v / S.r u a) ^ ε / S.r u v ^ 3) *
            (S.r u a / S.r u v) ^ α :=
          mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right hgrowth (by positivity)) (Real.rpow_nonneg (by
              positivity) _)
        _ = (-S.nu u a) / S.r u a ^ 2 * (1 / S.r u v) *
            (S.r u a / S.r u v) ^ (2 + α - ε) := by
          rw [mul_div_assoc, outer_kernel_power_identity hr hra,
            show 2 + α - ε = (2 - ε) + α by ring,
            Real.rpow_add (div_pos hra hr)]
          ring
        _ ≤ _ := by
          have hle : 1 ≤ S.lam u v / c := (le_div_iff₀ hc).mpr (by simpa using hlam v hv)
          have hnonneg : 0 ≤ (-S.nu u a) / S.r u a ^ 2 * (1 / S.r u v) *
              (S.r u a / S.r u v) ^ (2 + α - ε) := by positivity
          have hh := mul_le_mul_of_nonneg_left hle hnonneg
          convert hh using 1 <;> ring
    _ = ENNReal.ofReal ((-S.nu u a) / (c * S.r u a ^ 2)) *
        ∫⁻ v in Icc a b, ENNReal.ofReal (S.lam u v / S.r u v) *
          ENNReal.ofReal ((S.r u a / S.r u v) ^ (2 + α - ε)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((-S.nu u a) / (c * S.r u a ^ 2)) *
        ENNReal.ofReal (1 / (2 + α - ε)) := by gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_mul hk]
      congr 1
      field_simp [hc.ne', hp.ne', hra.ne']

end EmcsfAcExtension.Global.InteractionEstimate
