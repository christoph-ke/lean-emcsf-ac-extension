module

public import EmcsfAcExtension.Global.Exterior.ScalarEnergy

/-! # Annular charge control outside the core

The electromagnetic part of the ordinary Hawking mass is nonnegative.
Its integral on a proper annulus is controlled without integrating
Maxwell through the core (`charged_SF_new_version.tex:L1162–L1182`).
-/

public section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace EmcsfAcExtension.Global.Exterior

variable {ui e : ℝ} {S : Fields}

private theorem electromagnetic_density_le (h : OriginalData ui e S) {u v : ℝ}
    (hp : (u, v) ∈ origDomain ui) :
    S.Q u v ^ 2 / S.r u v ^ 2 * S.lam u v ≤ 2 * S.mV u v := by
  have hl := h.solution.lam_pos (u, v) hp
  have hg := h.solution.one_sub_mu_pos (u, v) hp
  have hn : 0 ≤ (1 - S.mu u v) * ‖S.theta u v‖ ^ 2 / (2 * S.lam u v) := by positivity
  have he : S.Q u v ^ 2 / S.r u v ^ 2 * S.lam u v =
      2 * (S.Q u v ^ 2 * S.lam u v / (2 * S.r u v ^ 2)) := by ring
  rw [he]
  unfold Fields.mV
  linarith only [hn]

/-- [internal]
Every proper exterior annulus has electromagnetic energy at most twice
the terminal mass. The coefficient `2` is numerical and uniform in the
solution, coupling and annulus. No core gap or core amplitude is used. -/
theorem electromagnetic_energy_le (h : OriginalData ui e S) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (_hb : b ≤ 0)
    (hs : outSeg u a b ⊆ origDomain ui) :
    (∫ v in a..b, S.Q u v ^ 2 / S.r u v ^ 2 * S.lam u v) ≤
      2 * terminalMass S u := by
  have hr (v : ℝ) (hv : v ∈ Icc a b) : S.r u v ≠ 0 :=
    (h.solution.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)).ne'
  have cq := Calculus.continuousOn_out_section h.solution.cont_Q hs
  have cr := Calculus.continuousOn_out_section h.solution.cont_r hs
  have cl := Calculus.continuousOn_out_section h.solution.cont_lam hs
  have hi := (((cq.pow 2).div (cr.pow 2)
    (fun v hv => pow_ne_zero 2 (hr v hv))).mul cl).intervalIntegrable_of_Icc
    (μ := volume) hab
  have hm := (h.solution.eq_out u a b hua hab hs).2.2.1
  have he := intervalIntegral.integral_mono_on hab hi (hm.1.const_mul 2)
    (fun v hv => electromagnetic_density_le h (hs ⟨rfl, hv⟩))
  rw [intervalIntegral.integral_const_mul, ← hm.2] at he
  change (∫ v in a..b, S.Q u v ^ 2 / S.r u v ^ 2 * S.lam u v) ≤
    2 * (S.m u b - S.m u a) at he
  have hma := mass_nonneg h (hs ⟨rfl, le_rfl, hab⟩)
  have hmb := mass_le_terminal h (hs ⟨rfl, hab, le_rfl⟩)
  linarith only [he, hma, hmb]

/-- [internal]
A comparable annulus contains a small-charge point. The annulus has
radial length at least `r/2` and outer radius at most `2r`.
The coefficient `4` is numerical and uniform in all data and annuli.
The consumer constructs one of the two annuli in `charged_SF_new_version.tex:L1162–L1164`. -/
theorem annular_charge_witness_of_annulus (h : OriginalData ui e S) {u a b r : ℝ}
    (hr : 0 < r) (hua : u < a) (hab : a ≤ b) (hb : b ≤ 0)
    (hs : outSeg u a b ⊆ origDomain ui)
    (hrb : ∀ v ∈ Icc a b, S.r u v ≤ 2 * r)
    (hlen : r / 2 ≤ S.r u b - S.r u a) :
    (∫ v in a..b, S.Q u v ^ 2 / S.r u v ^ 2 * S.lam u v) ≤
      2 * terminalMass S u ∧
    ∃ v ∈ Icc a b, |S.Q u v| ≤ 4 * Real.sqrt (terminalMass S u * r) := by
  have henergy := electromagnetic_energy_le h hua hab hb hs
  refine ⟨henergy, ?_⟩
  have hrpos (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.r u v :=
    h.solution.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
  have cq := Calculus.continuousOn_out_section h.solution.cont_Q hs
  have cr := Calculus.continuousOn_out_section h.solution.cont_r hs
  have cl := Calculus.continuousOn_out_section h.solution.cont_lam hs
  let f := fun v => S.Q u v ^ 2 / S.r u v ^ 2
  have cf : ContinuousOn f (Icc a b) := (cq.pow 2).div (cr.pow 2)
    (fun v hv => pow_ne_zero 2 (hrpos v hv).ne')
  obtain ⟨w, hw, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) cf
  have hmin0 : 0 ≤ f w := by dsimp [f]; positivity
  have hil : IntervalIntegrable (fun v => f w * S.lam u v) volume a b :=
    (cl.const_mul _).intervalIntegrable_of_Icc hab
  have hiq : IntervalIntegrable (fun v => f v * S.lam u v) volume a b :=
    (cf.mul cl).intervalIntegrable_of_Icc hab
  have hle := intervalIntegral.integral_mono_on hab hil hiq
    (fun v hv => mul_le_mul_of_nonneg_right (hmin hv)
      (h.solution.lam_pos (u, v) (hs ⟨rfl, hv⟩)).le)
  have hrad := (h.solution.eq_out u a b hua hab hs).1
  rw [intervalIntegral.integral_const_mul, ← hrad.2] at hle
  have hwgt : f w * (S.r u b - S.r u a) ≤ 2 * terminalMass S u := hle.trans henergy
  have hmr : f w * r ≤ 4 * terminalMass S u := by
    nlinarith only [hwgt, mul_nonneg hmin0 (sub_nonneg.mpr hlen)]
  have hqeq : S.Q u w ^ 2 = f w * S.r u w ^ 2 := by
    dsimp [f]
    field_simp [(hrpos w hw).ne']
  have hradsq : S.r u w ^ 2 ≤ (2 * r) ^ 2 :=
    pow_le_pow_left₀ (hrpos w hw).le (hrb w hw) 2
  have hqsq : S.Q u w ^ 2 ≤ 16 * (terminalMass S u * r) := by
    have hqrad := mul_le_mul_of_nonneg_left hradsq hmin0
    have hscaled := mul_le_mul_of_nonneg_right hmr hr.le
    nlinarith only [hqeq, hqrad, hscaled]
  have hbp : (u, b) ∈ origDomain ui := hs ⟨rfl, hab, le_rfl⟩
  have hM : 0 ≤ terminalMass S u := mass_nonneg h
    (show (u, 0) ∈ origDomain ui from
      ⟨hbp.1, hbp.2.1, hbp.2.1.le, le_rfl⟩)
  have hsqrt := Real.sq_sqrt (mul_nonneg hM hr.le)
  refine ⟨w, hw, ?_⟩
  nlinarith only [hqsq, hsqrt, Real.sqrt_nonneg (terminalMass S u * r),
    sq_abs (S.Q u w), abs_nonneg (S.Q u w)]

private theorem charge_endpoint_oscillation (h : OriginalData ui e S) {u a b r L : ℝ}
    (hr : 0 < r) (hL : 0 ≤ L) (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ origDomain ui)
    (hrb : ∀ v ∈ Icc a b, S.r u v ≤ 2 * r)
    (hlen : S.r u b - S.r u a ≤ r)
    (hphi : ∀ v ∈ Icc a b, ‖S.phi u v‖ ≤ L)
    (hE : (∫ v in a..b, ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v) ≤
      4 * terminalMass S u) :
    |S.Q u a - S.Q u b| ≤ 4 * |e| * L * r * Real.sqrt (terminalMass S u * r) := by
  have hrpos (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.r u v :=
    h.solution.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
  have hl (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.lam u v :=
    h.solution.lam_pos (u, v) (hs ⟨rfl, hv⟩)
  have cr := Calculus.continuousOn_out_section h.solution.cont_r hs
  have cl := Calculus.continuousOn_out_section h.solution.cont_lam hs
  have ct := Calculus.continuousOn_out_section h.solution.cont_theta hs
  let f := fun v => ‖S.theta u v‖ / Real.sqrt (S.lam u v)
  let g := fun v => S.r u v * Real.sqrt (S.lam u v)
  have hf : ContinuousOn f (Icc a b) := ct.norm.div cl.sqrt
    (fun v hv => (Real.sqrt_pos.mpr (hl v hv)).ne')
  have hg : ContinuousOn g (Icc a b) := cr.mul cl.sqrt
  have hc := integral_cauchy_schwarz hab hf hg
  have heq : (∫ v in a..b, f v ^ 2) =
      ∫ v in a..b, ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v := by
    apply intervalIntegral.integral_congr
    intro v hv
    have hv' : v ∈ Icc a b := by simpa only [uIcc_of_le hab] using hv
    dsimp [f]
    rw [div_pow, Real.sq_sqrt (hl v hv').le,
      norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hl v hv'), div_pow]
    field_simp [(hl v hv').ne']
  have hgeq : (∫ v in a..b, g v ^ 2) = ∫ v in a..b, S.r u v ^ 2 * S.lam u v := by
    apply intervalIntegral.integral_congr
    intro v hv
    have hv' : v ∈ Icc a b := by simpa only [uIcc_of_le hab] using hv
    dsimp [g]
    rw [mul_pow, Real.sq_sqrt (hl v hv').le]
  have hfg : (∫ v in a..b, f v * g v) = ∫ v in a..b, S.r u v * ‖S.theta u v‖ := by
    apply intervalIntegral.integral_congr
    intro v hv
    have hv' : v ∈ Icc a b := by simpa only [uIcc_of_le hab] using hv
    dsimp [f, g]
    field_simp [(Real.sqrt_pos.mpr (hl v hv')).ne']
  rw [heq, hgeq, hfg] at hc
  have hiB : IntervalIntegrable (fun v => S.r u v ^ 2 * S.lam u v) volume a b :=
    ((cr.pow 2).mul cl).intervalIntegrable_of_Icc hab
  have hiB' : IntervalIntegrable (fun v => (2 * r) ^ 2 * S.lam u v) volume a b :=
    (cl.const_mul _).intervalIntegrable_of_Icc hab
  have hB := intervalIntegral.integral_mono_on hab hiB hiB'
    (fun v hv => mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (hrpos v hv).le (hrb v hv) 2) (hl v hv).le)
  have hrad := (h.solution.eq_out u a b hua hab hs).1
  rw [intervalIntegral.integral_const_mul, ← hrad.2] at hB
  have hB' : (∫ v in a..b, S.r u v ^ 2 * S.lam u v) ≤ 4 * r ^ 3 := by
    nlinarith only [hB, mul_nonneg (sq_nonneg (2 * r)) (sub_nonneg.mpr hlen)]
  have hB0 : 0 ≤ ∫ v in a..b, S.r u v ^ 2 * S.lam u v :=
    intervalIntegral.integral_nonneg (μ := volume) hab
      (fun v hv => mul_nonneg (sq_nonneg _) (hl v hv).le)
  have hbp : (u, b) ∈ origDomain ui := hs ⟨rfl, hab, le_rfl⟩
  have hM : 0 ≤ terminalMass S u := mass_nonneg h
    (show (u, 0) ∈ origDomain ui from
      ⟨hbp.1, hbp.2.1, hbp.2.1.le, le_rfl⟩)
  have hprod := mul_le_mul hE hB' hB0 (mul_nonneg (by norm_num) hM)
  have hsqrt := Real.sq_sqrt (mul_nonneg hM hr.le)
  have hsqrtR : (4 * r * Real.sqrt (terminalMass S u * r)) ^ 2 =
      16 * terminalMass S u * r ^ 3 := by
    rw [mul_pow, hsqrt]
    ring
  have hI : (∫ v in a..b, S.r u v * ‖S.theta u v‖) ≤
      4 * r * Real.sqrt (terminalMass S u * r) := by
    have hsq := hc.trans hprod
    nlinarith only [hsq, hsqrtR,
      mul_nonneg hr.le (Real.sqrt_nonneg (terminalMass S u * r))]
  have hcurrent (v : ℝ) (hv : v ∈ Icc a b) :
      ‖S.QV e u v‖ ≤ (|e| * L) * (S.r u v * ‖S.theta u v‖) := by
    have him := Complex.abs_im_le_norm (starRingEnd ℂ (S.phi u v) * S.theta u v)
    rw [norm_mul, Complex.norm_conj] at him
    simp only [Fields.QV, Real.norm_eq_abs, abs_mul, abs_neg,
      abs_of_pos (hrpos v hv)]
    calc
      _ ≤ |e| * S.r u v * (‖S.phi u v‖ * ‖S.theta u v‖) :=
        mul_le_mul_of_nonneg_left him (mul_nonneg (abs_nonneg _) (hrpos v hv).le)
      _ ≤ |e| * S.r u v * (L * ‖S.theta u v‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hphi v hv) (norm_nonneg _))
          (mul_nonneg (abs_nonneg _) (hrpos v hv).le)
      _ = _ := by ring
  have hQ := (h.solution.eq_out u a b hua hab hs).2.2.2.1
  have hib := ((cr.mul ct.norm).const_mul (|e| * L)).intervalIntegrable_of_Icc
    (μ := volume) hab
  rw [abs_sub_comm, ← Real.norm_eq_abs, hQ.2]
  calc
    _ ≤ ∫ v in a..b, ‖S.QV e u v‖ := intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ v in a..b, (|e| * L) * (S.r u v * ‖S.theta u v‖) :=
      intervalIntegral.integral_mono_on hab hQ.1.norm hib hcurrent
    _ = (|e| * L) * ∫ v in a..b, S.r u v * ‖S.theta u v‖ :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ (|e| * L) * (4 * r * Real.sqrt (terminalMass S u * r)) :=
      mul_le_mul_of_nonneg_left hI (mul_nonneg (abs_nonneg _) hL)
    _ = _ := by ring

/-- [internal]
Maxwell oscillation between any two points of one comparable annulus,
`charged_SF_new_version.tex:L1170–L1177`. The numerical coefficient `4` is uniform in
all data. The scalar bound and radial energy are supplied by the preceding
terminal consumers; no information from the core is assumed. -/
theorem annular_charge_oscillation_of_energy (h : OriginalData ui e S) {u a b r L : ℝ}
    (hr : 0 < r) (hL : 0 ≤ L) (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ origDomain ui)
    (hrb : ∀ v ∈ Icc a b, S.r u v ≤ 2 * r)
    (hlen : S.r u b - S.r u a ≤ r)
    (hphi : ∀ v ∈ Icc a b, ‖S.phi u v‖ ≤ L)
    (hE : (∫ v in a..b, ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v) ≤
      4 * terminalMass S u) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      |S.Q u s - S.Q u t| ≤ 4 * |e| * L * r * Real.sqrt (terminalMass S u * r) := by
  have cl := Calculus.continuousOn_out_section h.solution.cont_lam hs
  have ct := Calculus.continuousOn_out_section h.solution.cont_theta hs
  have hp (v : ℝ) (hv : v ∈ Icc a b) : S.lam u v ≠ 0 :=
    (h.solution.lam_pos (u, v) (hs ⟨rfl, hv⟩)).ne'
  have hi : IntervalIntegrable (fun v =>
      ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v) volume a b :=
    (((ct.div (Complex.continuous_ofReal.comp_continuousOn cl)
      (fun v hv => Complex.ofReal_ne_zero.mpr (hp v hv))).norm.pow 2).mul
      cl).intervalIntegrable_of_Icc hab
  have hnonneg : ∀ᵐ v ∂volume.restrict (Ioc a b),
      0 ≤ ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact mul_nonneg (sq_nonneg _)
      (h.solution.lam_pos (u, v) (hs ⟨rfl, hv.1.le, hv.2⟩)).le
  have hlocal {s t : ℝ} (hs' : s ∈ Icc a b) (ht' : t ∈ Icc a b) (hst : s ≤ t) :
      |S.Q u s - S.Q u t| ≤ 4 * |e| * L * r * Real.sqrt (terminalMass S u * r) := by
    have hsub : outSeg u s t ⊆ origDomain ui :=
      fun _ hx => hs (outSeg_subset_outSeg hs'.1 ht'.2 hx)
    have hEsub : (∫ v in s..t, ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v) ≤
        4 * terminalMass S u :=
      (intervalIntegral.integral_mono_interval hs'.1 hst ht'.2 hnonneg hi).trans hE
    have hras := outgoing_radius_mono h hua.le hs'.1
      (fun _ hx => hs (outSeg_subset_outSeg le_rfl hs'.2 hx))
    have hrtb := outgoing_radius_mono h (hua.trans_le ht'.1).le ht'.2
      (fun _ hx => hs (outSeg_subset_outSeg ht'.1 le_rfl hx))
    apply charge_endpoint_oscillation h hr hL (hua.trans_le hs'.1) hst hsub
      (fun v hv => hrb v ⟨hs'.1.trans hv.1, hv.2.trans ht'.2⟩) (by linarith) _ hEsub
    exact fun v hv => hphi v ⟨hs'.1.trans hv.1, hv.2.trans ht'.2⟩
  intro s hs' t ht'
  rcases le_total s t with hst | hts
  · exact hlocal hs' ht' hst
  · simpa only [abs_sub_comm] using hlocal ht' hs' hts

/-- [internal]
Every intermediate radius on a proper outgoing segment has a label.
Only continuity and the endpoint radius values are used. -/
theorem exists_outgoing_radius_between (h : OriginalData ui e S) {u a b ρ : ℝ}
    (hab : a ≤ b) (hs : outSeg u a b ⊆ origDomain ui)
    (hρa : S.r u a ≤ ρ) (hρb : ρ ≤ S.r u b) :
    ∃ v ∈ Icc a b, S.r u v = ρ :=
  intermediate_value_Icc hab (Calculus.continuousOn_out_section h.solution.cont_r hs)
    ⟨hρa, hρb⟩

/-- [internal]
Construct exactly the two annuli of `charged_SF_new_version.tex:L1162–L1164`.
Their label interval contains the specified point, remains above `ℓ`,
has radial length between `r/2` and `r`, and outer radius at most `2r`.
No selected inverse function or additional regularity is assumed. -/
theorem annulus_labels (h : OriginalData ui e S) {u v ℓ : ℝ}
    (hp : (u, v) ∈ origDomain ui) (huv : u < v)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ S.r u v) (hℓR : 2 * ℓ ≤ terminalRadius S u) :
    ∃ a b, u < a ∧ a ≤ v ∧ v ≤ b ∧ b ≤ 0 ∧ ℓ ≤ S.r u a ∧
      S.r u v / 2 ≤ S.r u a ∧ S.r u b ≤ 2 * S.r u v ∧
      S.r u v / 2 ≤ S.r u b - S.r u a ∧ S.r u b - S.r u a ≤ S.r u v ∧
      ((a = v ∧ S.r u b = 2 * S.r u v) ∨
        (b = 0 ∧ S.r u a = terminalRadius S u / 2)) := by
  have hr := hℓ.trans_le hℓr
  have htop : S.r u v ≤ S.r u 0 := radius_le_terminal h hp
  have hs : outSeg u v 0 ⊆ origDomain ui :=
    (outSeg_subset_origDomain_iff hp.2.2.2).2 ⟨hp.1, hp.2.1, huv.le, le_rfl⟩
  by_cases hsmall : 2 * S.r u v ≤ S.r u 0
  · obtain ⟨b, hb, hbr⟩ := exists_outgoing_radius_between h hp.2.2.2 hs
      (by linarith : S.r u v ≤ 2 * S.r u v) hsmall
    refine ⟨v, b, huv, le_rfl, hb.1, hb.2, hℓr, ?_, ?_, ?_, ?_, Or.inl ⟨rfl, hbr⟩⟩
    · linarith
    · rw [hbr]
    · rw [hbr]; linarith
    · rw [hbr]; linarith
  · have htoppos : 0 < S.r u 0 := hr.trans_le htop
    have hs' : outSeg u u v ⊆ origDomain ui :=
      (outSeg_subset_origDomain_iff hp.2.2.1).2 ⟨hp.1, hp.2.1, le_rfl, hp.2.2.2⟩
    have haxis := (h.solution.axis u (hs' ⟨rfl, le_rfl, huv.le⟩)).1
    obtain ⟨a, ha, har⟩ := exists_outgoing_radius_between h huv.le hs'
      (by rw [haxis]; linarith : S.r u u ≤ S.r u 0 / 2)
      (by linarith : S.r u 0 / 2 ≤ S.r u v)
    have hua : u < a := by
      rcases ha.1.eq_or_lt with heq | hlt
      · rw [← heq, haxis] at har
        linarith
      · exact hlt
    refine ⟨a, 0, hua, ha.2, hp.2.2.2, le_rfl, ?_, ?_, ?_, ?_, ?_,
      Or.inr ⟨rfl, har⟩⟩
    all_goals dsimp only [terminalRadius] at hℓR ⊢
    all_goals linarith [har]

/-- [node c:exterior#annular-charge-witness]
Select the source's comparable annulus around each exterior point and
obtain its electric energy and charge witness (charged_SF_new_version.tex:L1162–1170).
The coefficient `4` is universal, uniformly in the solution and annulus.
The supplied positive core radius is any admissible adaptive radius. -/
theorem annular_charge_witness_at_point (h : OriginalData ui e S) {u v ℓ : ℝ}
    (hp : (u, v) ∈ origDomain ui) (huv : u < v)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ S.r u v) (hℓR : 2 * ℓ ≤ terminalRadius S u) :
    ∃ a b, u < a ∧ a ≤ v ∧ v ≤ b ∧ b ≤ 0 ∧ ℓ ≤ S.r u a ∧
      S.r u v / 2 ≤ S.r u a ∧ S.r u b ≤ 2 * S.r u v ∧
      S.r u v / 2 ≤ S.r u b - S.r u a ∧ S.r u b - S.r u a ≤ S.r u v ∧
      ((a = v ∧ S.r u b = 2 * S.r u v) ∨
        (b = 0 ∧ S.r u a = terminalRadius S u / 2)) ∧
      (∫ w in a..b, S.Q u w ^ 2 / S.r u w ^ 2 * S.lam u w) ≤
        2 * terminalMass S u ∧
      ∃ w ∈ Icc a b, |S.Q u w| ≤ 4 * Real.sqrt (terminalMass S u * S.r u v) := by
  obtain ⟨a, b, hua, hav, hvb, hb, hℓa, hra, hrb, hlo, hhi, hcase⟩ :=
    annulus_labels h hp huv hℓ hℓr hℓR
  have hab := hav.trans hvb
  have hs : outSeg u a b ⊆ origDomain ui :=
    (outSeg_subset_origDomain_iff hab).2 ⟨hp.1, hp.2.1, hua.le, hb⟩
  have hw := annular_charge_witness_of_annulus h (h.solution.r_pos _ hp huv) hua hab hb hs
    (fun w hw => (outgoing_radius_mono h (hua.le.trans hw.1) hw.2
      (fun p hq => hs (outSeg_subset_outSeg hw.1 le_rfl hq))).trans hrb) hlo
  exact ⟨a, b, hua, hav, hvb, hb, hℓa, hra, hrb, hlo, hhi, hcase, hw⟩

/-- [internal]
The annular witness and Maxwell oscillation imply the pointwise charge
estimate of `charged_SF_new_version.tex:L1156–L1162`. The coefficient `32` is numerical
and uniform in all data. All scalar and energy hypotheses concern only
the displayed exterior annulus and are discharged by the terminal consumer. -/
theorem charge_pointwise_of_annulus (h : OriginalData ui e S) {u a b v L : ℝ}
    (hL : 0 ≤ L) (hua : u < a) (hab : a ≤ b) (hb : b ≤ 0)
    (hs : outSeg u a b ⊆ origDomain ui) (hv : v ∈ Icc a b)
    (hrb : ∀ s ∈ Icc a b, S.r u s ≤ 2 * S.r u v)
    (hlenlo : S.r u v / 2 ≤ S.r u b - S.r u a)
    (hlenhi : S.r u b - S.r u a ≤ S.r u v)
    (hphi : ∀ s ∈ Icc a b, ‖S.phi u s‖ ≤ L)
    (hE : (∫ s in a..b, ‖S.theta u s / (S.lam u s : ℂ)‖ ^ 2 * S.lam u s) ≤
      4 * terminalMass S u) :
    S.Q u v ^ 2 / S.r u v ^ 2 ≤ 32 * (terminalMass S u / S.r u v) *
      (1 + e ^ 2 * L ^ 2 * S.r u v ^ 2) := by
  have hr : 0 < S.r u v := h.solution.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
  obtain ⟨_, w, hw, hQw⟩ := annular_charge_witness_of_annulus h hr hua hab hb hs hrb hlenlo
  have hosc := annular_charge_oscillation_of_energy h hr hL hua hab hs hrb hlenhi hphi hE v hv w hw
  have hpoint : |S.Q u v| ≤ 4 * Real.sqrt (terminalMass S u * S.r u v) *
      (1 + |e| * L * S.r u v) := by
    calc
      _ = |(S.Q u v - S.Q u w) + S.Q u w| := by rw [sub_add_cancel]
      _ ≤ |S.Q u v - S.Q u w| + |S.Q u w| := by
        simpa only [Real.norm_eq_abs] using norm_add_le (S.Q u v - S.Q u w) (S.Q u w)
      _ ≤ 4 * |e| * L * S.r u v * Real.sqrt (terminalMass S u * S.r u v) +
          4 * Real.sqrt (terminalMass S u * S.r u v) := add_le_add hosc hQw
      _ = _ := by ring
  have hbp : (u, b) ∈ origDomain ui := hs ⟨rfl, hab, le_rfl⟩
  have hM : 0 ≤ terminalMass S u := mass_nonneg h
    ⟨hbp.1, hbp.2.1, hbp.2.1.le, le_rfl⟩
  have hsqrt := Real.sq_sqrt (mul_nonneg hM hr.le)
  have hsq := pow_le_pow_left₀ (abs_nonneg (S.Q u v)) hpoint 2
  have hYoung : (1 + |e| * L * S.r u v) ^ 2 ≤
      2 * (1 + (|e| * L * S.r u v) ^ 2) := by
    nlinarith only [sq_nonneg (1 - |e| * L * S.r u v)]
  have hscaled := mul_le_mul_of_nonneg_left hYoung
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16)
      (sq_nonneg (Real.sqrt (terminalMass S u * S.r u v))))
  have hbound : S.Q u v ^ 2 ≤ 32 * (terminalMass S u * S.r u v) *
      (1 + e ^ 2 * L ^ 2 * S.r u v ^ 2) := by
    simp only [mul_pow, show (4 : ℝ) ^ 2 = 16 by norm_num, hsqrt, sq_abs] at hsq
    rw [hsqrt, mul_pow, mul_pow, sq_abs] at hscaled
    nlinarith only [hsq, hscaled]
  apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
  convert hbound using 1
  field_simp

/-- [internal]
Absorb the charged scalar scale in the pointwise annular estimate.
The numerical coefficient `64` is uniform in all data. -/
theorem charge_pointwise_absorb {Q M r e L : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hQ : Q ^ 2 / r ^ 2 ≤ 32 * (M / r) * (1 + e ^ 2 * L ^ 2 * r ^ 2))
    (hscale : e ^ 2 * L ^ 2 * r ^ 2 ≤ 1) : Q ^ 2 / r ^ 2 ≤ 64 * (M / r) := by
  have hm := div_nonneg hM hr.le
  nlinarith only [hQ, mul_nonneg hm (sub_nonneg.mpr hscale)]

end EmcsfAcExtension.Global.Exterior

namespace EmcsfAcExtension.Global

open Exterior

/-- [internal]
Conditional terminal consumer for `eq:charged-exterior-charge-pointwise`,
`charged_SF_new_version.tex:L1156–L1182`. It constructs the two annuli, their charge
witnesses and Maxwell oscillation bounds from the original equations.
The coefficients `32` and `64` are numerical and uniform in all data;
the logarithmic envelope coefficient and late cutoff depend on the fixed
terminal inputs and adaptive radius. No core gap is required. -/
theorem charged_exterior_charge_pointwise_of_terminal {ui e C : ℝ} {S : Fields}
    (h : OriginalData ui e S) (M ell : ℝ → ℝ) {R₀ : ℝ} (hR : 0 < R₀) (hC : 0 < C)
    (hcollapse : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0))
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0))
    (hphi : ∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
      C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) :
    ∃ u₀ ∈ Ioo ui 0, ∀ p ∈ adaptiveExterior S ui u₀ ell,
      let L := (C + 2) * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r p.1 0)))
      S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 ≤
          32 * (terminalMass S p.1 / S.r p.1 p.2) *
            (1 + e ^ 2 * L ^ 2 * S.r p.1 p.2 ^ 2) ∧
        S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 ≤
          64 * (terminalMass S p.1 / S.r p.1 p.2) := by
  obtain ⟨ul, hul, hlog⟩ := (scalar_log_envelope_of_terminal h M ell hR hC
    hcollapse hmass hell hsmall hphi).2
  obtain ⟨ue, hue, henergy⟩ := charged_exterior_scalar_energy_of_terminal h M ell hR
    hcollapse hmass hell hsmall
  have hRi : 0 < S.r ui 0 := h.solution.r_pos (ui, 0)
    ⟨le_rfl, h.ui_neg, h.ui_neg.le, le_rfl⟩ h.ui_neg
  have hrpos : ∀ᶠ u in 𝓝[<] (0 : ℝ), 0 < S.r u 0 := by
    filter_upwards [Ioo_mem_nhdsLT h.ui_neg] with u hu
    exact h.solution.r_pos (u, 0) ⟨hu.1.le, hu.2, hu.2.le, le_rfl⟩ hu.2
  have hRt : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hcollapse, hrpos⟩
  have hscale := (logarithmic_scale_tendsto_zero (S.r ui 0) (C + 2) e hRi).comp hRt
  have he : ∀ᶠ u in 𝓝[<] (0 : ℝ), u ∈ Ioo ui 0 ∧
      0 < S.r u 0 ∧ S.r u 0 < R₀ ∧ ell (S.r u 0) / S.r u 0 < 1 / 2 ∧
      e ^ 2 * ((C + 2) * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) ^ 2 *
        S.r u 0 ^ 2 < 1 := by
    filter_upwards [Ioo_mem_nhdsLT h.ui_neg, hrpos,
      hcollapse.eventually (Iio_mem_nhds hR),
      (hellsmall.comp hRt).eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      hscale.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with u hu hr hrR hℓ hs
    exact ⟨hu, hr, hrR, hℓ, hs⟩
  obtain ⟨d, hd, hdb⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp he
  let uc := max d ui / 2
  have huc : uc ∈ Ioo ui 0 := by
    have hm0 := max_lt hd h.ui_neg
    dsimp [uc]
    constructor <;> linarith [le_max_right d ui]
  let u₀ := max ul (max ue uc)
  have hu₀ : u₀ ∈ Ioo ui 0 :=
    ⟨lt_max_of_lt_left hul.1, max_lt hul.2 (max_lt hue.2 huc.2)⟩
  refine ⟨u₀, hu₀, ?_⟩
  intro p hp
  have hup : p.1 ∈ Ioo d 0 := by
    refine ⟨?_, hp.1.2.1⟩
    have hb : uc ≤ p.1 := (le_max_right ue uc).trans ((le_max_right ul (max ue uc)).trans hp.2.1)
    dsimp [uc] at hb
    have hm0 := max_lt hd h.ui_neg
    linarith [le_max_left d ui]
  have hc := hdb hup
  have hℓ := hell (S.r p.1 0) ⟨hc.2.1, hc.2.2.1.le⟩
  have hℓR : 2 * ell (terminalRadius S p.1) ≤ terminalRadius S p.1 := by
    have hh := (div_lt_iff₀ hc.2.1).mp hc.2.2.2.1
    dsimp [terminalRadius]
    linarith
  have hr : 0 < S.r p.1 p.2 := hℓ.trans_le hp.2.2
  have huv : p.1 < p.2 := by
    rcases hp.1.2.2.1.eq_or_lt with heq | hlt
    · have hpaxis : (p.1, p.1) ∈ origDomain ui :=
        ⟨hp.1.1, hp.1.2.1, le_rfl, hp.1.2.1.le⟩
      rw [← heq, (h.solution.axis p.1 hpaxis).1] at hr
      exact False.elim (lt_irrefl _ hr)
    · exact hlt
  obtain ⟨a, b, hua, hav, hvb, hb, hℓa, _, hrb, hlenlo, hlenhi, _⟩ :=
    annulus_labels h hp.1 huv hℓ hp.2.2 hℓR
  have hab := hav.trans hvb
  have hs : outSeg p.1 a b ⊆ origDomain ui :=
    (outSeg_subset_origDomain_iff hab).2 ⟨hp.1.1, hp.1.2.1, hua.le, hb⟩
  have hs0 : outSeg p.1 a 0 ⊆ origDomain ui :=
    (outSeg_subset_origDomain_iff (hab.trans hb)).2 ⟨hp.1.1, hp.1.2.1, hua.le, le_rfl⟩
  have hpa : (p.1, a) ∈ adaptiveExterior S ui ue ell :=
    ⟨hs0 ⟨rfl, le_rfl, hab.trans hb⟩,
      (le_max_left ue uc).trans ((le_max_right ul (max ue uc)).trans hp.2.1), hℓa⟩
  have hEfull := (henergy p.1 a hpa).1
  have cl := Calculus.continuousOn_out_section h.solution.cont_lam hs0
  have ct := Calculus.continuousOn_out_section h.solution.cont_theta hs0
  have hl (s : ℝ) (hs' : s ∈ Icc a 0) : S.lam p.1 s ≠ 0 :=
    (h.solution.lam_pos (p.1, s) (hs0 ⟨rfl, hs'⟩)).ne'
  have hi : IntervalIntegrable (fun s =>
      ‖S.theta p.1 s / (S.lam p.1 s : ℂ)‖ ^ 2 * S.lam p.1 s) volume a 0 :=
    (((ct.div (Complex.continuous_ofReal.comp_continuousOn cl)
      (fun s hs' => Complex.ofReal_ne_zero.mpr (hl s hs'))).norm.pow 2).mul
      cl).intervalIntegrable_of_Icc
        (hab.trans hb)
  have hn : ∀ᵐ s ∂volume.restrict (Ioc a 0),
      0 ≤ ‖S.theta p.1 s / (S.lam p.1 s : ℂ)‖ ^ 2 * S.lam p.1 s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs'
    exact mul_nonneg (sq_nonneg _)
      (h.solution.lam_pos (p.1, s) (hs0 ⟨rfl, hs'.1.le, hs'.2⟩)).le
  have hE := (intervalIntegral.integral_mono_interval le_rfl hab hb hn hi).trans hEfull
  let L := (C + 2) * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r p.1 0)))
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hphis (s : ℝ) (hs' : s ∈ Icc a b) : ‖S.phi p.1 s‖ ≤ L := by
    apply hlog (p.1, s)
    refine ⟨hs ⟨rfl, hs'⟩, (le_max_left ul (max ue uc)).trans hp.2.1, ?_⟩
    exact hℓa.trans (outgoing_radius_mono h hua.le hs'.1
      (fun _ hx => hs (outSeg_subset_outSeg le_rfl hs'.2 hx)))
  have hbound := charge_pointwise_of_annulus h hL hua hab hb hs ⟨hav, hvb⟩
    (fun s hs' => (outgoing_radius_mono h (hua.trans_le hs'.1).le hs'.2
      (fun _ hx => hs (outSeg_subset_outSeg hs'.1 le_rfl hx))).trans hrb)
    hlenlo hlenhi hphis hE
  have hscalept : e ^ 2 * L ^ 2 * S.r p.1 p.2 ^ 2 ≤ 1 := by
    have htop := radius_le_terminal h hp.1
    have hs' := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le htop 2)
      (mul_nonneg (sq_nonneg e) (sq_nonneg L))
    exact hs'.trans hc.2.2.2.2.le
  refine ⟨hbound, charge_pointwise_absorb hr ?_ hbound hscalept⟩
  exact mass_nonneg h ⟨hp.1.1, hp.1.2.1, hp.1.2.1.le, le_rfl⟩

end EmcsfAcExtension.Global
