module

public import EmcsfAcExtension.Global.Defs.Curves
public import EmcsfAcExtension.Frozen.IsSolution
public import EmcsfAcExtension.Frozen.OrigDomain
public import EmcsfAcExtension.Global.Defs.Renormalized
import EmcsfAcExtension.Global.Observation.Energy
import EmcsfAcExtension.Global.Renormalized.WeakTransfer
import EmcsfAcExtension.Global.Calculus.CurveTrace

/-! # The covariant boundary chain rule

The rough derivative is the selected characteristic representative, with a
fixed initial incoming row. The landed timelike chain rule supplies its AC
trace on a proper cylinder. Source: `charged_SF_new_version.tex:L3805–L3814` and the
approved internal project record boundary-forcing proof.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Interaction

/-- [internal] The renormalized fixed density equals the prescribed weighted
representative throughout the proper original characteristic wedge, including
its initial row. This is a pointwise identity of selected representatives,
not a trace of an arbitrary a.e. derivative. Constants: none. -/
theorem weighted_density_eq_representative_on_orig {ui e : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) {a u v : ℝ}
    (hia : ui ≤ a) (hau : a ≤ u) (huv : u < v) (hv : v ≤ 0) :
    (S.lam u v : ℂ) * densityRepresentative e S a u v -
      (S.lam u v ^ 2 / S.r u v : ℝ) *
        (‖S.theta u v / S.lam u v‖ : ℂ) ^ 2 * (S.theta u v / S.lam u v) =
      weightedJRepresentative e S a u v := by
  by_cases heq : a = u
  · subst a
    have hp : (u, v) ∈ origDomain ui := ⟨hia, huv.trans_le hv, huv.le, hv⟩
    rw [Renormalized.weighted_density_initial e S u v
      (hS.lam_pos _ hp).ne' (hS.one_sub_mu_pos _ hp).ne']
    simp [weightedJRepresentative]
  · have hau := lt_of_le_of_ne hau heq
    have hmid : u < (u + v) / 2 ∧ (u + v) / 2 < v := ⟨by linarith, by linarith⟩
    apply Renormalized.weighted_density_eq_representative hS hau hmid.2 ?_
      u ⟨hau.le, le_rfl⟩ v ⟨hmid.2.le, le_rfl⟩
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    have hxy := hx.2.trans_lt (hmid.1.trans_le hy.1)
    exact ⟨⟨hia.trans hx.1, hxy.trans_le (hy.2.trans hv), hxy.le, hy.2.trans hv⟩, hxy⟩

end EmcsfAcExtension.Global.Interaction

namespace EmcsfAcExtension.Global

/-- [node eq:ct-boundary-chain]
The exact covariant AC chain rule on a proper positive-radius cylinder.
The first term is `j/((1-μ)λ) = W/λ²`, with `W` the selected weighted
representative anchored at the cylinder's initial incoming row. All
coefficients are exact, uniform in the coupling and data. -/
theorem ct_boundary_chain {ui e b s t : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (γ : ClockCylinder S (origDomain ui) b s t)
    (hb : 0 < b) (hst : s ≤ t) :
    AbsolutelyContinuousOnInterval (fun x => S.a (γ.U x) (γ.V x)) s t ∧
      ∀ᵐ τ ∂volume.restrict (Icc s t),
        deriv (fun x => S.a (γ.U x) (γ.V x)) τ +
          I * e * S.A (γ.U τ) (γ.V τ) * deriv γ.U τ * S.a (γ.U τ) (γ.V τ) =
        weightedJRepresentative e S (γ.U s) (γ.U τ) (γ.V τ) /
          (S.lam (γ.U τ) (γ.V τ) : ℂ) ^ 2 +
        ((‖S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)‖ : ℂ) ^ 2 *
            (S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)) +
          (((S.mu (γ.U τ) (γ.V τ) : ℂ) -
              S.Q (γ.U τ) (γ.V τ) ^ 2 / (S.r (γ.U τ) (γ.V τ) : ℂ) ^ 2) /
            (1 - S.mu (γ.U τ) (γ.V τ)) *
            (S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ))) +
          I * e * S.Q (γ.U τ) (γ.V τ) * S.phi (γ.U τ) (γ.V τ) /
            (1 - S.mu (γ.U τ) (γ.V τ))) / (b : ℂ) := by
  refine ⟨Cylinder.ac_a hS γ hb hst, ?_⟩
  rcases hst.eq_or_lt with rfl | hst
  · simp
  obtain ⟨KU, KV, LU, LV, hU, hV, hUa, hVa⟩ := γ.exists_biLipschitz_labels hS
  have hproper (x : ℝ) (hx : x ∈ Icc s t) : γ.U x < γ.V x := by
    have hp := γ.mem x hx
    refine lt_of_le_of_ne hp.2.2.1 ?_
    intro heq
    have ha := (hS.axis (γ.U x) (by simpa only [← heq] using hp)).1
    have hr := γ.radius x hx
    rw [← heq, ha] at hr
    exact hb.ne' hr.symm
  have hUa' : AntilipschitzWith LU ((uIcc s t).domRestrict γ.U) := by
    intro x y
    exact hUa ⟨x, by simpa only [uIcc_of_le hst.le] using x.property⟩
      ⟨y, by simpa only [uIcc_of_le hst.le] using y.property⟩
  have hVa' : AntilipschitzWith LV ((uIcc s t).domRestrict γ.V) := by
    intro x y
    exact hVa ⟨x, by simpa only [uIcc_of_le hst.le] using x.property⟩
      ⟨y, by simpa only [uIcc_of_le hst.le] using y.property⟩
  have hc := Calculus.timelike_ac_chain_rule hS (U := γ.U) (V := γ.V)
    (KU := KU) (KV := KV) hst
    (by simpa only [uIcc_of_le hst.le] using hU)
    (by simpa only [uIcc_of_le hst.le] using hV)
    (by simpa only [uIcc_of_le hst.le] using (γ.strictMonoOn_U hS).monotoneOn)
    (by simpa only [uIcc_of_le hst.le] using (γ.strictMonoOn_V hS).monotoneOn)
    hUa' hVa' (by simpa only [uIcc_of_le hst.le] using γ.mem)
    (by simpa only [uIcc_of_le hst.le] using hproper)
  dsimp only at hc
  rw [uIcc_of_le hst.le] at hc
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [hc.2.filter_mono (ae_mono (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)),
    ae_restrict_mem measurableSet_Ioo] with τ hd hτ
  have hm := Ioo_subset_Icc_self hτ
  have hp := γ.mem τ hm
  have hn := Complex.ofReal_ne_zero.mpr (hS.nu_neg _ hp).ne
  have hl := Complex.ofReal_ne_zero.mpr (hS.lam_pos _ hp).ne'
  have hg : (1 - (S.mu (γ.U τ) (γ.V τ) : ℂ)) ≠ 0 := by
    exact_mod_cast (hS.one_sub_mu_pos _ hp).ne'
  have hrep := Interaction.weighted_density_eq_representative_on_orig hS
    (γ.mem s ⟨le_rfl, hst.le⟩).1
    ((γ.strictMonoOn_U hS).monotoneOn ⟨le_rfl, hst.le⟩ hm hτ.1.le)
    (hproper τ hm) hp.2.2.2
  rw [hd.deriv, (γ.hasDerivAt_U hτ).deriv, (γ.hasDerivAt_V hτ).deriv,
    ← hrep]
  simp only [Fields.a, add_sub_cancel_left, Complex.real_smul, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_inv,
    Complex.ofReal_pow, Complex.ofReal_one, γ.radius τ hm]
  field_simp [hn, hl, hg, Complex.ofReal_ne_zero.mpr hb.ne']
  ring

end EmcsfAcExtension.Global

namespace EmcsfAcExtension.Global.Interaction

/-- [internal] Conversion of a nonnegative integrable clock density, including
equal endpoints. This exact identity introduces no finiteness assumption on
any other density. -/
theorem ofReal_interval_integral {a b : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (h0 : ∀ x ∈ Icc a b, 0 ≤ f x) :
    ENNReal.ofReal (∫ x in a..b, f x) = ∫⁻ x in Icc a b, ENNReal.ofReal (f x) := by
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  exact ofReal_integral_eq_lintegral_ofReal
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hf)
    (ae_restrict_of_forall_mem measurableSet_Icc h0)

/-- [internal] The selected derivative forcing is integrable on a proper
cylinder, and the covariant speed is bounded by its three actual forcing
contributions. Integrability follows from the proved AC chain rule. No
integrability or trace of an arbitrary spacetime derivative is assumed.
All coefficients are exact and independent of the data. -/
theorem cylinder_forcing_integrals {ui e b s t : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (γ : ClockCylinder S (origDomain ui) b s t)
    (hb : 0 < b) (hst : s ≤ t)
    (hq : ∀ τ ∈ Icc s t,
      S.Q (γ.U τ) (γ.V τ) ^ 2 / b ^ 2 ≤ S.mu (γ.U τ) (γ.V τ)) :
    IntervalIntegrable (fun τ =>
      ‖weightedJRepresentative e S (γ.U s) (γ.U τ) (γ.V τ)‖ /
        S.lam (γ.U τ) (γ.V τ) ^ 2) volume s t ∧
    (∫ τ in s..t, ‖deriv (fun x => S.a (γ.U x) (γ.V x)) τ +
        I * e * S.A (γ.U τ) (γ.V τ) * deriv γ.U τ * S.a (γ.U τ) (γ.V τ)‖) ≤
      (∫ τ in s..t, ‖weightedJRepresentative e S (γ.U s) (γ.U τ) (γ.V τ)‖ /
        S.lam (γ.U τ) (γ.V τ) ^ 2) +
      (∫ τ in s..t, (‖S.theta (γ.U τ) (γ.V τ) / S.lam (γ.U τ) (γ.V τ)‖ ^ 3 +
        ((S.mu (γ.U τ) (γ.V τ) - S.Q (γ.U τ) (γ.V τ) ^ 2 / b ^ 2) /
          (1 - S.mu (γ.U τ) (γ.V τ))) *
          ‖S.theta (γ.U τ) (γ.V τ) / S.lam (γ.U τ) (γ.V τ)‖) / b) +
      (∫ τ in s..t, ‖I * (e : ℂ) * S.Q (γ.U τ) (γ.V τ) * S.phi (γ.U τ) (γ.V τ) /
        (((1 - S.mu (γ.U τ) (γ.V τ)) * b : ℝ) : ℂ)‖) := by
  obtain ⟨ha, hchain⟩ := ct_boundary_chain hS γ hb hst
  obtain ⟨cy, _, cμ⟩ := Cylinder.continuousOn_normalized_traces hS γ
  have cQ := γ.continuousOn_trace hS.cont_Q
  have cφ := γ.continuousOn_trace hS.cont_phi
  let κ := fun τ => (S.mu (γ.U τ) (γ.V τ) - S.Q (γ.U τ) (γ.V τ) ^ 2 / b ^ 2) /
    (1 - S.mu (γ.U τ) (γ.V τ))
  let y := fun τ => S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)
  let em := fun τ => I * (e : ℂ) * S.Q (γ.U τ) (γ.V τ) * S.phi (γ.U τ) (γ.V τ) /
    (((1 - S.mu (γ.U τ) (γ.V τ)) * b : ℝ) : ℂ)
  let neutral := fun τ => (((‖y τ‖ : ℂ) ^ 2 * y τ + (κ τ : ℂ) * y τ) / (b : ℂ))
  let w := fun τ => weightedJRepresentative e S (γ.U s) (γ.U τ) (γ.V τ) /
    (S.lam (γ.U τ) (γ.V τ) : ℂ) ^ 2
  let d := fun τ => deriv (fun x => S.a (γ.U x) (γ.V x)) τ +
    I * e * S.A (γ.U τ) (γ.V τ) * deriv γ.U τ * S.a (γ.U τ) (γ.V τ)
  have cκ : ContinuousOn κ (Icc s t) :=
    (cμ.sub ((cQ.pow 2).div_const (b ^ 2))).div (continuousOn_const.sub cμ)
      (fun τ hτ => (hS.one_sub_mu_pos _ (γ.mem τ hτ)).ne')
  have cem : ContinuousOn em (Icc s t) :=
    ((continuousOn_const.mul (continuous_ofReal.comp_continuousOn cQ)).mul cφ).div
      (continuous_ofReal.comp_continuousOn ((continuousOn_const.sub cμ).mul_const b))
      (fun τ hτ => Complex.ofReal_ne_zero.mpr
        (mul_ne_zero (hS.one_sub_mu_pos _ (γ.mem τ hτ)).ne' hb.ne'))
  have cneutral : ContinuousOn neutral (Icc s t) :=
    ((((continuous_ofReal.comp_continuousOn cy.norm).pow 2).mul cy).add
      ((continuous_ofReal.comp_continuousOn cκ).mul cy)).div_const (b : ℂ)
  have id : IntervalIntegrable d volume s t := by
    have hp := Cylinder.intervalIntegrable_potential_clock hS γ hst
    have hpC' : IntervalIntegrable
        (fun x => ((S.A (γ.U x) (γ.V x) * deriv γ.U x : ℝ) : ℂ)) volume s t :=
      ⟨hp.1.ofReal, hp.2.ofReal⟩
    have hmul := hpC'.mul_continuousOn ha.continuousOn
    convert ha.intervalIntegrable_deriv_complex.add (hmul.const_mul (I * e)) using 1
    funext τ
    dsimp only [d]
    push_cast
    ring
  have hsplit : ∀ᵐ τ ∂volume.restrict (Icc s t), d τ = w τ + neutral τ + em τ := by
    filter_upwards [hchain, ae_restrict_mem measurableSet_Icc] with τ hτ hmem
    dsimp only [d, w, neutral, em, κ, y]
    rw [hτ, γ.radius τ hmem]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hb.ne',
      Complex.ofReal_ne_zero.mpr (hS.lam_pos _ (γ.mem τ hmem)).ne',
      show (1 - (S.mu (γ.U τ) (γ.V τ) : ℂ)) ≠ 0 from by
        exact_mod_cast (hS.one_sub_mu_pos _ (γ.mem τ hmem)).ne']
    ring
  have iw : IntervalIntegrable w volume s t :=
    ((id.sub (cneutral.intervalIntegrable_of_Icc hst)).sub
      (cem.intervalIntegrable_of_Icc hst)).congr_ae
      (by
        rw [uIoc_of_le hst]
        filter_upwards [hsplit.filter_mono (ae_mono
          (Measure.restrict_mono Ioc_subset_Icc_self le_rfl))] with τ hτ
        linear_combination hτ)
  have hn0 τ (hτ : τ ∈ Icc s t) : 0 ≤ κ τ :=
    div_nonneg (sub_nonneg.mpr (hq τ hτ)) (hS.one_sub_mu_pos _ (γ.mem τ hτ)).le
  have hnormw τ : ‖w τ‖ = ‖weightedJRepresentative e S (γ.U s) (γ.U τ) (γ.V τ)‖ /
      S.lam (γ.U τ) (γ.V τ) ^ 2 := by
    dsimp only [w]
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hneutral τ (hτ : τ ∈ Icc s t) :
      ‖neutral τ‖ ≤ (‖y τ‖ ^ 3 + κ τ * ‖y τ‖) / b := by
    dsimp only [neutral]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb]
    apply div_le_div_of_nonneg_right _ hb.le
    calc
      _ ≤ ‖(‖y τ‖ : ℂ) ^ 2 * y τ‖ + ‖(κ τ : ℂ) * y τ‖ := norm_add_le _ _
      _ = _ := by
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg _), norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (hn0 τ hτ)]
        ring
  have iw' : IntervalIntegrable (fun τ =>
      ‖weightedJRepresentative e S (γ.U s) (γ.U τ) (γ.V τ)‖ /
        S.lam (γ.U τ) (γ.V τ) ^ 2) volume s t := by
    simpa only [hnormw] using iw.norm
  have ineutral := (((cy.norm.pow 3).add (cκ.mul cy.norm)).div_const b).intervalIntegrable_of_Icc
    (μ := volume) hst
  refine ⟨iw', ?_⟩
  have hi := intervalIntegral.integral_mono_ae_restrict hst id.norm
    ((iw'.add ineutral).add (cem.norm.intervalIntegrable_of_Icc hst)) (by
      filter_upwards [hsplit, ae_restrict_mem measurableSet_Icc] with τ hτ hmem
      rw [hτ]
      exact (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (le_of_eq (hnormw τ)) (hneutral τ hmem))) le_rfl))
  rwa [intervalIntegral.integral_add (iw'.add ineutral) (cem.norm.intervalIntegrable_of_Icc hst),
    intervalIntegral.integral_add iw' ineutral] at hi

end EmcsfAcExtension.Global.Interaction
