module

public import EmcsfAcExtension.Global.Terminal.Flux
import EmcsfAcExtension.Global.Calculus.Sections
import EmcsfAcExtension.Local.Calculus.Sections
import EmcsfAcExtension.Infra.AC.Quotient
import EmcsfAcExtension.Infra.AC.Complex

/-! # Scalar growth from the finite terminal flux

Unitary parallel transport on proper sections removes the connection from
the scalar FTC. Weighted Cauchy–Schwarz and the radius logarithm give the
bound in charged_SF_new_version.tex:L939–942 and approved internal project record (T3).
-/

public section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global.Terminal

/-- [internal] Real Cauchy–Schwarz on a compact interval for continuous
functions, with its exact universal coefficient one. -/
theorem integral_cauchy_schwarz {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b)) :
    (∫ x in a..b, f x * g x) ^ 2 ≤
      (∫ x in a..b, f x ^ 2) * (∫ x in a..b, g x ^ 2) := by
  have iff : IntervalIntegrable (fun x => f x ^ 2) volume a b :=
    (hf.pow 2).intervalIntegrable_of_Icc hab
  have ifg : IntervalIntegrable (fun x => f x * g x) volume a b :=
    (hf.mul hg).intervalIntegrable_of_Icc hab
  have igg : IntervalIntegrable (fun x => g x ^ 2) volume a b :=
    (hg.pow 2).intervalIntegrable_of_Icc hab
  have h (t : ℝ) : 0 ≤ (∫ x in a..b, g x ^ 2) * (t * t) +
      (2 * ∫ x in a..b, f x * g x) * t + ∫ x in a..b, f x ^ 2 := by
    have hp := intervalIntegral.integral_nonneg (μ := volume) hab
      (fun x _ => sq_nonneg (f x + t * g x))
    have he : (∫ x in a..b, (f x + t * g x) ^ 2) =
        (∫ x in a..b, f x ^ 2) + 2 * t * (∫ x in a..b, f x * g x) +
          t ^ 2 * (∫ x in a..b, g x ^ 2) := by
      calc
        _ = ∫ x in a..b, (f x ^ 2 + (2 * t) * (f x * g x)) + t ^ 2 * g x ^ 2 :=
          intervalIntegral.integral_congr (fun x _ => by ring)
        _ = _ := by
          rw [intervalIntegral.integral_add (iff.add (ifg.const_mul (2 * t)))
            (igg.const_mul (t ^ 2)), intervalIntegral.integral_add iff (ifg.const_mul (2 * t))]
          simp only [intervalIntegral.integral_const_mul]
    rw [he] at hp
    nlinarith only [hp]
  have hd := discrim_le_zero h
  dsimp [discrim] at hd
  nlinarith only [hd]

/-- [internal] Cauchy–Schwarz for arbitrary integrable real squares, with
universal coefficient one. This form also applies to improper terminal tails. -/
theorem integral_cauchy_schwarz_of_integrable_sq {μ : Measure ℝ} {f g : ℝ → ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hff : Integrable (fun x => f x ^ 2) μ) (hgg : Integrable (fun x => g x ^ 2) μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  have hfg : Integrable (fun x => f x * g x) μ :=
    ((memLp_two_iff_integrable_sq hf).2 hff).integrable_mul
      ((memLp_two_iff_integrable_sq hg).2 hgg)
  have h (t : ℝ) : 0 ≤ (∫ x, g x ^ 2 ∂μ) * (t * t) +
      (2 * ∫ x, f x * g x ∂μ) * t + ∫ x, f x ^ 2 ∂μ := by
    have hp := integral_nonneg (μ := μ) (fun x => sq_nonneg (f x + t * g x))
    have he : (∫ x, (f x + t * g x) ^ 2 ∂μ) =
        (∫ x, f x ^ 2 ∂μ) + 2 * t * (∫ x, f x * g x ∂μ) +
          t ^ 2 * (∫ x, g x ^ 2 ∂μ) := by
      calc
        _ = ∫ x, (f x ^ 2 + (2 * t) * (f x * g x)) + t ^ 2 * g x ^ 2 ∂μ := by
          congr 1
          funext x
          ring
        _ = _ := by
          rw [integral_add (f := fun x => f x ^ 2 + (2 * t) * (f x * g x))
            (g := fun x => t ^ 2 * g x ^ 2)
            (hff.add (hfg.const_mul (2 * t))) (hgg.const_mul (t ^ 2)),
            integral_add (f := fun x => f x ^ 2) (g := fun x => (2 * t) * (f x * g x))
              hff (hfg.const_mul (2 * t))]
          simp only [integral_const_mul]
    rw [he] at hp
    nlinarith only [hp]
  have hd := discrim_le_zero h
  dsimp [discrim] at hd
  nlinarith only [hd]

/-- [internal] The product of the square roots of two nonnegative integrable
densities is integrable and satisfies Cauchy–Schwarz with coefficient one. -/
theorem sqrt_cauchy_schwarz {μ : Measure ℝ} {f g : ℝ → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfn : ∀ᵐ x ∂μ, 0 ≤ f x) (hgn : ∀ᵐ x ∂μ, 0 ≤ g x) :
    Integrable (fun x => Real.sqrt (f x) * Real.sqrt (g x)) μ ∧
      (∫ x, Real.sqrt (f x) * Real.sqrt (g x) ∂μ) ^ 2 ≤
        (∫ x, f x ∂μ) * (∫ x, g x ∂μ) := by
  have hfm := Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable
  have hgm := Real.continuous_sqrt.comp_aestronglyMeasurable hg.aestronglyMeasurable
  have hfe : (fun x => Real.sqrt (f x) ^ 2) =ᵐ[μ] f :=
    hfn.mono fun x hx => Real.sq_sqrt hx
  have hge : (fun x => Real.sqrt (g x) ^ 2) =ᵐ[μ] g :=
    hgn.mono fun x hx => Real.sq_sqrt hx
  have hfi := hf.congr hfe.symm
  have hgi := hg.congr hge.symm
  refine ⟨((memLp_two_iff_integrable_sq hfm).2 hfi).integrable_mul
    ((memLp_two_iff_integrable_sq hgm).2 hgi), ?_⟩
  simpa only [integral_congr_ae hfe, integral_congr_ae hge] using
    integral_cauchy_schwarz_of_integrable_sq hfm hgm hfi hgi

/-- [internal] The modulus of the scalar changes by at most the integral of
the covariant scalar derivative. The coefficient one is universal and no
bound on the real connection is required. -/
theorem scalar_norm_le_integral {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a b v : ℝ} (hab : a ≤ b) (hbv : b < v)
    (hseg : inSeg a b v ⊆ D) :
    ‖S.phi b v‖ ≤ ‖S.phi a v‖ + ∫ s in a..b, ‖S.xi s v‖ / S.r s v := by
  have cA := Calculus.continuousOn_in_section hS.cont_A hseg
  have cr := Calculus.continuousOn_in_section hS.cont_r hseg
  have cx := Calculus.continuousOn_in_section hS.cont_xi hseg
  have hr : ∀ s ∈ Icc a b, 0 < S.r s v := fun s hs =>
    hS.r_pos (s, v) (hseg ⟨hs.1, hs.2, rfl⟩) (hs.2.trans_lt hbv)
  have iA := cA.intervalIntegrable_of_Icc (μ := volume) hab
  let P (s : ℝ) := Complex.exp (I * ((e * ∫ t in a..s, S.A t v : ℝ) : ℂ))
  have hP : AbsolutelyContinuousOnInterval P a b :=
    ((iA.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).const_mul e).unit_phase
  have hnorm (s : ℝ) : ‖P s‖ = 1 := by simp [P, Complex.norm_exp]
  have hPc : ContinuousOn P (Icc a b) := by
    simpa only [uIcc_of_le hab] using hP.continuousOn
  have hs := Local.IsSolution.in_section hS hab hbv hseg
  have hq := hP.mul_normed_ring (hS.ac_in a b v hab hseg).2.2.2
  have ci := hPc.mul (cx.div (continuous_ofReal.comp_continuousOn cr)
    (fun s hs' => Complex.ofReal_ne_zero.mpr (hr s hs').ne'))
  have he : IntegralForm (fun s => P s * S.phi s v)
      (fun s => P s * (S.xi s v / (S.r s v : ℂ))) a b := by
    apply integralForm_of_ac_of_ae_hasDerivAt hq (ci.intervalIntegrable_of_Icc hab)
    rw [uIcc_of_le hab]
    apply (ae_restrict_iff' measurableSet_Icc).mp
    filter_upwards [ae_restrict_of_ae iA.ae_hasDerivAt_integral,
      hs.2.2.2.2.1.2, ae_restrict_mem measurableSet_Icc] with s hIA hphi hmem
    have hIA' := hIA (show s ∈ uIcc a b by simpa only [uIcc_of_le hab] using hmem)
      a left_mem_uIcc
    have hdp := ((hIA'.const_mul e).ofReal_comp.const_mul I).cexp
    apply (hdp.mul hphi).congr_deriv
    dsimp [P, Fields.phiU, Pi.mul_apply, Pi.add_apply]
    push_cast
    ring
  have hn : ‖∫ s in a..b, P s * (S.xi s v / (S.r s v : ℂ))‖ ≤
      ∫ s in a..b, ‖S.xi s v‖ / S.r s v := by
    apply (intervalIntegral.norm_integral_le_integral_norm hab).trans_eq
    apply intervalIntegral.integral_congr
    intro s hs'
    have hs'' : s ∈ Icc a b := by simpa only [uIcc_of_le hab] using hs'
    change ‖P s * (S.xi s v / (S.r s v : ℂ))‖ = ‖S.xi s v‖ / S.r s v
    rw [norm_mul, hnorm, one_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hr s hs'')]
  calc
    ‖S.phi b v‖ = ‖P b * S.phi b v‖ := by rw [norm_mul, hnorm, one_mul]
    _ = ‖P a * S.phi a v + ∫ s in a..b, P s * (S.xi s v / (S.r s v : ℂ))‖ :=
      congrArg norm he.eq_add_integral
    _ ≤ ‖P a * S.phi a v‖ + ‖∫ s in a..b, P s * (S.xi s v / (S.r s v : ℂ))‖ :=
      norm_add_le _ _
    _ ≤ _ := by
      rw [norm_mul, hnorm, one_mul]
      exact add_le_add le_rfl hn

/-- [internal] The radius logarithm integrates the positive incoming density
`(-ν)/r` exactly on a proper section. -/
theorem incoming_radius_log {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a b v : ℝ} (hab : a ≤ b) (hbv : b < v)
    (hseg : inSeg a b v ⊆ D) :
    (∫ s in a..b, -S.nu s v / S.r s v) = Real.log (S.r a v / S.r b v) := by
  have cr := Calculus.continuousOn_in_section hS.cont_r hseg
  have cn := Calculus.continuousOn_in_section hS.cont_nu hseg
  have hr : ∀ s ∈ Icc a b, 0 < S.r s v := fun s hs =>
    hS.r_pos (s, v) (hseg ⟨hs.1, hs.2, rfl⟩) (hs.2.trans_lt hbv)
  obtain ⟨c, hc, hcl⟩ := isCompact_Icc.exists_forall_le' cr hr
  have hs := Local.IsSolution.in_section hS hab hbv hseg
  have hac := (hs.1.1.log_of_pos_le hc (by simpa only [uIcc_of_le hab] using hcl)).neg
  have hi := (cn.neg.div cr (fun s hs' => (hr s hs').ne')).intervalIntegrable_of_Icc
    (μ := volume) hab
  have he : IntegralForm (fun s => -Real.log (S.r s v)) (fun s => -S.nu s v / S.r s v) a b := by
    apply integralForm_of_ac_of_ae_hasDerivAt hac hi
    rw [uIcc_of_le hab]
    apply (ae_restrict_iff' measurableSet_Icc).mp
    filter_upwards [hs.1.2, ae_restrict_mem measurableSet_Icc] with s hd hmem
    apply ((hd.log (hr s hmem).ne').neg).congr_deriv
    change -(S.nu s v / S.r s v) = -S.nu s v / S.r s v
    simp only [neg_div]
  rw [Real.log_div (hr a ⟨le_rfl, hab⟩).ne' (hr b ⟨hab, le_rfl⟩).ne']
  linarith only [he.2]

/-- [internal] Weighted scalar Cauchy–Schwarz. Both factors are real proper
integrals, so no improper-integral conversion is involved. -/
theorem scalar_weighted_cauchy_schwarz {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a b v : ℝ} (hab : a ≤ b) (hbv : b < v)
    (hseg : inSeg a b v ⊆ D) :
    (∫ s in a..b, ‖S.xi s v‖ / S.r s v) ^ 2 ≤
      (∫ s in a..b, ‖S.xi s v‖ ^ 2 / ((-S.nu s v) * S.r s v)) *
        Real.log (S.r a v / S.r b v) := by
  have cr := Calculus.continuousOn_in_section hS.cont_r hseg
  have cn := Calculus.continuousOn_in_section hS.cont_nu hseg
  have cx := Calculus.continuousOn_in_section hS.cont_xi hseg
  have hr : ∀ s ∈ Icc a b, 0 < S.r s v := fun s hs =>
    hS.r_pos (s, v) (hseg ⟨hs.1, hs.2, rfl⟩) (hs.2.trans_lt hbv)
  have hn : ∀ s ∈ Icc a b, 0 < -S.nu s v := fun s hs =>
    neg_pos.mpr (hS.nu_neg (s, v) (hseg ⟨hs.1, hs.2, rfl⟩))
  let f := fun s => ‖S.xi s v‖ / (Real.sqrt (-S.nu s v) * Real.sqrt (S.r s v))
  let g := fun s => Real.sqrt (-S.nu s v) / Real.sqrt (S.r s v)
  have cf : ContinuousOn f (Icc a b) := cx.norm.div (cn.neg.sqrt.mul cr.sqrt)
    (fun s hs => mul_ne_zero (Real.sqrt_pos.mpr (hn s hs)).ne'
      (Real.sqrt_pos.mpr (hr s hs)).ne')
  have cg : ContinuousOn g (Icc a b) := cn.neg.sqrt.div cr.sqrt
    (fun s hs => (Real.sqrt_pos.mpr (hr s hs)).ne')
  have hfg : (∫ s in a..b, f s * g s) = ∫ s in a..b, ‖S.xi s v‖ / S.r s v := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hab] at hs
    have hns := (Real.sqrt_pos.mpr (hn s hs)).ne'
    have hrs := (Real.sqrt_pos.mpr (hr s hs)).ne'
    dsimp [f, g]
    field_simp [hns, hrs]
    rw [Real.sq_sqrt (hr s hs).le, mul_div_cancel_right₀ _ (hr s hs).ne']
  have hff : (∫ s in a..b, f s ^ 2) =
      ∫ s in a..b, ‖S.xi s v‖ ^ 2 / ((-S.nu s v) * S.r s v) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hab] at hs
    dsimp [f]
    rw [div_pow, mul_pow, Real.sq_sqrt (hn s hs).le, Real.sq_sqrt (hr s hs).le]
  have hgg : (∫ s in a..b, g s ^ 2) = Real.log (S.r a v / S.r b v) := by
    rw [← incoming_radius_log hS hab hbv hseg]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hab] at hs
    dsimp [g]
    rw [div_pow, Real.sq_sqrt (hn s hs).le, Real.sq_sqrt (hr s hs).le]
  simpa only [hfg, hff, hgg] using integral_cauchy_schwarz hab cf cg

/-- [internal]
The logarithmic terminal scalar bound, charged_SF_new_version.tex:L939–942. The positive
constant may depend on the fixed development, its initial scalar value,
and its signed terminal bound, uniformly in the proper terminal label. -/
theorem scalar_log_bound (ui e : ℝ) (S : Fields) (hui : ui < 0)
    (hS : IsSolution e S (origDomain ui))
    (hgauge : ∀ t, ui ≤ t → t < 0 → S.A t t = 0)
    (hmu : ∀ p ∈ origDomain ui, 0 ≤ S.mu p.1 p.2 ∧ S.mu p.1 p.2 < 1)
    (hr : ∀ v ∈ Icc ui 0, S.r ui v = (v - ui) / 2)
    (hdata : AbsolutelyContinuousOnInterval (S.a ui) ui 0)
    (hs : BddAbove ((fun u => ∫ s in ui..u, signedExpIntegrand S s 0) '' Ioo ui 0)) :
    ∃ C : ℝ, 0 < C ∧ ∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
      C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0))) := by
  have hF := (terminal_gap_and_flux ui e S hui hS hgauge hmu hr hdata hs).2
  let E := (∫⁻ u in Ico ui 0, ENNReal.ofReal
    (‖S.xi u 0‖ ^ 2 / ((-S.nu u 0) * S.r u 0))).toReal
  have hEn : 0 ≤ E := ENNReal.toReal_nonneg
  let C := 1 + ‖S.phi ui 0‖ + Real.sqrt E
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro u hu
  have hr0 := hS.r_pos (ui, 0) ⟨le_rfl, hui, hui.le, le_rfl⟩ hui
  rcases eq_or_lt_of_le hu.1 with rfl | hui'
  · rw [div_self hr0.ne', Real.log_one, Real.sqrt_zero, add_zero, mul_one]
    dsimp [C]
    linarith only [Real.sqrt_nonneg E]
  have hseg : inSeg ui u 0 ⊆ origDomain ui :=
    (inSeg_subset_origDomain_iff hui'.le).2 ⟨le_rfl, hu.2, hu.2.le, le_rfl⟩
  have hnonneg (s : ℝ) (hs' : s ∈ Icc ui u) :
      0 ≤ ‖S.xi s 0‖ ^ 2 / ((-S.nu s 0) * S.r s 0) := by
    have hp := hseg (show (s, 0) ∈ inSeg ui u 0 from ⟨hs'.1, hs'.2, rfl⟩)
    exact div_nonneg (sq_nonneg _) (mul_nonneg (neg_pos.mpr (hS.nu_neg _ hp)).le
      (hS.r_pos _ hp (hs'.2.trans_lt hu.2)).le)
  have hproper : (∫ s in ui..u, ‖S.xi s 0‖ ^ 2 / ((-S.nu s 0) * S.r s 0)) ≤ E := by
    have he := ofReal_intervalIntegral_eq_lintegral_of_continuousOn hui'.le
      (incoming_flux_continuousOn hS hu.2 hseg) hnonneg
    have hle : ENNReal.ofReal (∫ s in ui..u, ‖S.xi s 0‖ ^ 2 / ((-S.nu s 0) * S.r s 0)) ≤
        ∫⁻ s in Ico ui 0, ENNReal.ofReal (‖S.xi s 0‖ ^ 2 / ((-S.nu s 0) * S.r s 0)) := by
      rw [he]
      exact lintegral_mono_set (Ico_subset_Ico_right hu.2.le)
    have hh := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hF.ne).2 hle
    rw [ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg hui'.le hnonneg)] at hh
    exact hh
  have hLn : 0 ≤ Real.log (S.r ui 0 / S.r u 0) := by
    rw [← incoming_radius_log hS hui'.le hu.2 hseg]
    apply intervalIntegral.integral_nonneg hui'.le
    intro s hs'
    have hp := hseg (show (s, 0) ∈ inSeg ui u 0 from ⟨hs'.1, hs'.2, rfl⟩)
    exact div_nonneg (neg_pos.mpr (hS.nu_neg _ hp)).le
      (hS.r_pos _ hp (hs'.2.trans_lt hu.2)).le
  have hcs := (scalar_weighted_cauchy_schwarz hS hui'.le hu.2 hseg).trans
    (mul_le_mul_of_nonneg_right hproper hLn)
  have hroot := Real.le_sqrt_of_sq_le hcs
  rw [Real.sqrt_mul hEn] at hroot
  calc
    ‖S.phi u 0‖ ≤ ‖S.phi ui 0‖ + ∫ s in ui..u, ‖S.xi s 0‖ / S.r s 0 :=
      scalar_norm_le_integral hS hui'.le hu.2 hseg
    _ ≤ ‖S.phi ui 0‖ + Real.sqrt E * Real.sqrt (Real.log (S.r ui 0 / S.r u 0)) :=
      add_le_add le_rfl hroot
    _ ≤ C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0))) := by
      dsimp [C]
      nlinarith only [norm_nonneg (S.phi ui 0), Real.sqrt_nonneg E,
        Real.sqrt_nonneg (Real.log (S.r ui 0 / S.r u 0))]

end EmcsfAcExtension.Global.Terminal

namespace EmcsfAcExtension.Global

/-- [node eq:charged-terminal-log-bound]
Canonical logarithmic scalar estimate, charged_SF_new_version.tex:L939–942. The positive
constant depends on the fixed development and signed bound, uniformly in the label. -/
theorem charged_terminal_log_bound (ui e : ℝ) (S : Fields) (hui : ui < 0)
    (hS : IsSolution e S (origDomain ui))
    (hgauge : ∀ t, ui ≤ t → t < 0 → S.A t t = 0)
    (hmu : ∀ p ∈ origDomain ui, 0 ≤ S.mu p.1 p.2 ∧ S.mu p.1 p.2 < 1)
    (hr : ∀ v ∈ Icc ui 0, S.r ui v = (v - ui) / 2)
    (hdata : AbsolutelyContinuousOnInterval (S.a ui) ui 0)
    (hs : BddAbove ((fun u => ∫ s in ui..u, signedExpIntegrand S s 0) '' Ioo ui 0)) :
    ∃ C : ℝ, 0 < C ∧ ∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
      C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0))) := by
  exact Terminal.scalar_log_bound ui e S hui hS hgauge hmu hr hdata hs

end EmcsfAcExtension.Global
