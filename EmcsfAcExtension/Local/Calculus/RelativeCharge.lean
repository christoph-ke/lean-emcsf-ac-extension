module

public import EmcsfAcExtension.Frozen.IsSolution
import EmcsfAcExtension.Local.Calculus.Reconstruction

/-! # Relative charge on a regular-center outgoing cone

The Maxwell and ordinary mass constraints give the exact inequalities of
charged_SF_new_version.tex:L4345–4369. Null-label integrals include the radial Jacobian
`λ`, so no inverse radius coordinate is needed.
-/

public section

open Set MeasureTheory Filter Complex
open scoped Topology

namespace EmcsfAcExtension.Local

private theorem integral_cauchy_schwarz {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b)) :
    (∫ x in a..b, f x * g x) ^ 2 ≤
      (∫ x in a..b, f x ^ 2) * (∫ x in a..b, g x ^ 2) := by
  have iff : IntervalIntegrable (fun x => f x ^ 2) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab (hf.pow 2)
  have ifg : IntervalIntegrable (fun x => f x * g x) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab (hf.mul hg)
  have igg : IntervalIntegrable (fun x => g x ^ 2) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab (hg.pow 2)
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
            (igg.const_mul (t ^ 2)),
            intervalIntegral.integral_add iff (ifg.const_mul (2 * t))]
          simp only [intervalIntegral.integral_const_mul]
    rw [he] at hp
    nlinarith only [hp]
  have hd := discrim_le_zero h
  dsimp [discrim] at hd
  nlinarith only [hd]

/-- The mass ratio is continuous along a complete outgoing cone in the broad
AC class. The value at the vertex uses the frozen regular-axis limit. -/
theorem continuousOn_mu_out {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u < v) (hseg : outSeg u u v ⊆ D) :
    ContinuousOn (S.mu u) (Icc u v) := by
  have cr := continuousOn_out_section hS.cont_r hseg
  have cm := continuousOn_out_section hS.cont_m hseg
  intro s hs
  by_cases hsu : s = u
  · subst s
    have huD := hseg (show (u, u) ∈ outSeg u u v from ⟨rfl, le_rfl, huv.le⟩)
    have ht : Tendsto (fun t : ℝ => (u, t)) (𝓝[>] u)
        (𝓝[D ∩ {p : ℝ × ℝ | p.1 < p.2}] (u, u)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨(continuous_const.prodMk continuous_id).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iio_mem_nhds huv)] with t ht htv
      exact ⟨hseg ⟨rfl, ht.le, htv.le⟩, ht⟩
    have hlim := (hS.axis_mu u huD).comp ht
    have hzero : S.mu u u = 0 := by simp [Fields.mu, (hS.axis u huD).1]
    have hc : ContinuousWithinAt (S.mu u) (Ioi u) u := by
      simpa only [ContinuousWithinAt, hzero, Function.comp_def, Function.uncurry_def] using hlim
    exact (continuousWithinAt_Ioi_iff_Ici.mp hc).mono Icc_subset_Ici_self
  · have hur : u < s := lt_of_le_of_ne hs.1 (Ne.symm hsu)
    exact ((continuousWithinAt_const.mul (cm s hs)).div (cr s hs)
      (hS.r_pos (u, s) (hseg ⟨rfl, hs⟩) hur).ne')

/-- [node restart-sec-bv-stability-independent#oscillatory-charge-constraint]
The exact oscillatory Maxwell primitive, charged_SF_new_version.tex:L5290–5290, in the
broad AC class on a complete outgoing cone. No envelope is assumed. -/
theorem Stab.oscillatory_charge_constraint {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u ≤ v) (hseg : outSeg u u v ⊆ D) :
    S.Q u v = -e * ∫ s in u..v, S.lam u s * S.r u s *
      (starRingEnd ℂ (S.phi u s) * (S.theta u s / S.lam u s)).im := by
  have heq := integralForm_of_ac_of_interior_deriv huv
    (hS.ac_out u u v huv hseg).2.2.1
    (fun s hs => IsSolution.hasDerivAt_charge_out hS hseg hs)
  have halg : ∀ s ∈ Icc u v, S.QV e u s = -e * (S.lam u s * S.r u s *
      (starRingEnd ℂ (S.phi u s) * (S.theta u s / S.lam u s)).im) := by
    intro s hs
    have hl := (hS.lam_pos (u, s) (hseg ⟨rfl, hs⟩)).ne'
    rw [← mul_div_assoc, Complex.div_ofReal_im]
    dsimp [Fields.QV]
    field_simp
  have hi := intervalIntegral.integral_congr (a := u) (b := v) (μ := volume) (fun s hs => halg s (by
    simpa only [uIcc_of_le huv] using hs))
  have hval := heq.2
  rw [hi, intervalIntegral.integral_const_mul] at hval
  simpa [(hS.axis u (hseg ⟨rfl, le_rfl, huv⟩)).2.2.1] using hval

/-- [node restart-sec-bv-stability-independent#oscillatory-charge-constraint]
The oscillatory Maxwell bound with the exact universal coefficient `1/2`.
It is independent of the geometric box, cone size, coupling, and data. -/
theorem Stab.oscillatory_charge_bound {e M ε : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u ≤ v) (hseg : outSeg u u v ⊆ D)
    (hM : ∀ s ∈ Icc u v, ‖S.phi u s‖ ≤ M)
    (hε : ∀ s ∈ Icc u v, ‖S.theta u s / S.lam u s‖ ≤ ε) :
    |S.Q u v| ≤ |e| * M * ε * S.r u v ^ 2 / 2 := by
  have cr := continuousOn_out_section hS.cont_r hseg
  have cl := continuousOn_out_section hS.cont_lam hseg
  have cp := continuousOn_out_section hS.cont_phi hseg
  have ct := continuousOn_out_section hS.cont_theta hseg
  have cx := ct.div (continuous_ofReal.comp_continuousOn cl) (fun s hs => by
    change (S.lam u s : ℂ) ≠ 0
    exact_mod_cast (hS.lam_pos (u, s) (hseg ⟨rfl, hs⟩)).ne')
  have cg := (cl.mul cr).mul (continuous_im.comp_continuousOn (cp.star.mul cx))
  have ig := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv cg
  have ib : IntervalIntegrable (fun s => S.lam u s * S.r u s * M * ε) volume u v :=
    ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv
      (((cl.mul cr).mul continuousOn_const).mul continuousOn_const)
  have hp : ∀ s ∈ Icc u v, ‖S.lam u s * S.r u s *
      (starRingEnd ℂ (S.phi u s) * (S.theta u s / S.lam u s)).im‖ ≤
        S.lam u s * S.r u s * M * ε := by
    intro s hs
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM s hs)
    have hl := hS.lam_pos (u, s) (hseg ⟨rfl, hs⟩)
    have hr : 0 ≤ S.r u s := by
      rcases eq_or_lt_of_le hs.1 with h | h
      · subst s
        rw [(hS.axis u (hseg ⟨rfl, le_rfl, huv⟩)).1]
      · exact (hS.r_pos (u, s) (hseg ⟨rfl, hs⟩) h).le
    calc
      _ = (S.lam u s * S.r u s) *
          |(starRingEnd ℂ (S.phi u s) * (S.theta u s / S.lam u s)).im| := by
            rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hl.le hr),
              Real.norm_eq_abs]
      _ ≤ (S.lam u s * S.r u s) * (‖S.phi u s‖ * ‖S.theta u s / S.lam u s‖) := by
        gcongr
        simpa only [norm_mul, Complex.norm_conj] using
          Complex.abs_im_le_norm (starRingEnd ℂ (S.phi u s) * (S.theta u s / S.lam u s))
      _ ≤ S.lam u s * S.r u s * (M * ε) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (hM s hs) (hε s hs) (norm_nonneg _) hM0)
          (mul_nonneg hl.le hr)
      _ = _ := by ring
  have hbound := (intervalIntegral.norm_integral_le_integral_norm huv).trans
    (intervalIntegral.integral_mono_on huv ig.norm ib hp)
  calc
    |S.Q u v| = |e| * ‖∫ s in u..v, S.lam u s * S.r u s *
        (starRingEnd ℂ (S.phi u s) * (S.theta u s / S.lam u s)).im‖ := by
      rw [Stab.oscillatory_charge_constraint hS huv hseg, abs_mul, abs_neg,
        Real.norm_eq_abs]
    _ ≤ |e| * (∫ s in u..v, S.lam u s * S.r u s * M * ε) :=
      mul_le_mul_of_nonneg_left hbound (abs_nonneg e)
    _ = _ := by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
      have hm := outgoing_radius_moment hS huv hseg 1
      simp only [pow_one, Nat.reduceAdd] at hm
      rw [hm]
      ring

private theorem twice_massV (S : Fields) {u s : ℝ} (hl : S.lam u s ≠ 0) :
    2 * S.mV u s = S.lam u s * (1 - S.mu u s) * ‖S.theta u s / S.lam u s‖ ^ 2 +
      S.lam u s * (S.Q u s ^ 2 / S.r u s ^ 2) := by
  simp only [Fields.mV, norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
  by_cases hr : S.r u s = 0
  · simp only [hr, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero,
      mul_zero, add_zero]
    field_simp [hl]
  · field_simp [hl, hr]

/-- [node restart-lem-relative-charge#mass-controls-radial-flux]
The radial ordinary mass equation, with the exact Jacobian, at every
positive-radius point. No constants or bounds on the scalar are assumed. -/
theorem RelCharge.radial_mass_equation {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u s : ℝ} (hp : (u, s) ∈ D) :
    2 * S.mV u s / S.lam u s =
      (1 - S.mu u s) * ‖S.theta u s / S.lam u s‖ ^ 2 + S.Q u s ^ 2 / S.r u s ^ 2 := by
  rw [twice_massV S (hS.lam_pos (u, s) hp).ne']
  field_simp [(hS.lam_pos (u, s) hp).ne']

/-- [node restart-lem-relative-charge#mass-controls-radial-flux]
The scalar radial flux is at most twice the ordinary mass,
charged_SF_new_version.tex:L4365–4367. This bound is exact and applies to a single
regular-center outgoing cone in the broad AC class. -/
theorem RelCharge.mass_controls_radial_flux {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u < v) (hseg : outSeg u u v ⊆ D) :
    (∫ s in u..v, S.lam u s * (1 - S.mu u s) * ‖S.theta u s / S.lam u s‖ ^ 2) ≤
      2 * S.m u v := by
  have cl := continuousOn_out_section hS.cont_lam hseg
  have ct := continuousOn_out_section hS.cont_theta hseg
  have cg : ContinuousOn (fun s => 1 - S.mu u s) (Icc u v) :=
    continuousOn_const.sub (continuousOn_mu_out hS huv hseg)
  have cx := ct.div (continuous_ofReal.comp_continuousOn cl) (fun s hs => by
    change (S.lam u s : ℂ) ≠ 0
    exact_mod_cast (hS.lam_pos (u, s) (hseg ⟨rfl, hs⟩)).ne')
  have iflux := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv.le
    ((cl.mul cg).mul (cx.norm.pow 2))
  have heq := integralForm_of_ac_of_interior_deriv huv.le
    (hS.ac_out u u v huv.le hseg).2.1
    (fun s hs => IsSolution.hasDerivAt_mass_out hS hseg hs)
  have hle := intervalIntegral.integral_mono_on huv.le iflux (heq.1.const_mul 2)
    (fun s hs => show S.lam u s * (1 - S.mu u s) * ‖S.theta u s / S.lam u s‖ ^ 2 ≤
      2 * S.mV u s from by
        rw [twice_massV S (hS.lam_pos (u, s) (hseg ⟨rfl, hs⟩)).ne']
        exact le_add_of_nonneg_right (mul_nonneg
          (hS.lam_pos (u, s) (hseg ⟨rfl, hs⟩)).le (div_nonneg (sq_nonneg _) (sq_nonneg _))))
  rw [intervalIntegral.integral_const_mul, ← heq.2] at hle
  simpa [(hS.axis u (hseg ⟨rfl, le_rfl, huv.le⟩)).2.1] using hle

/-- [node restart-lem-relative-charge#maxwell-cauchy-schwarz]
Weighted Maxwell Cauchy–Schwarz on a regular-center outgoing cone,
charged_SF_new_version.tex:L4358–4364. The coefficient is exactly `e²`; the factors
are the radial integrals expressed with `dr = λ dv`. -/
theorem RelCharge.maxwell_cauchy_schwarz {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u < v) (hseg : outSeg u u v ⊆ D) :
    S.Q u v ^ 2 ≤ e ^ 2 *
      (∫ s in u..v, S.lam u s * (1 - S.mu u s) * ‖S.theta u s / S.lam u s‖ ^ 2) *
      (∫ s in u..v, S.lam u s * S.r u s ^ 2 * ‖S.phi u s‖ ^ 2 / (1 - S.mu u s)) := by
  have cl := continuousOn_out_section hS.cont_lam hseg
  have cr := continuousOn_out_section hS.cont_r hseg
  have cp := continuousOn_out_section hS.cont_phi hseg
  have ct := continuousOn_out_section hS.cont_theta hseg
  have cg : ContinuousOn (fun s => 1 - S.mu u s) (Icc u v) :=
    continuousOn_const.sub (continuousOn_mu_out hS huv hseg)
  have pos_l (s : ℝ) (hs : s ∈ Icc u v) := hS.lam_pos (u, s) (hseg ⟨rfl, hs⟩)
  have pos_g (s : ℝ) (hs : s ∈ Icc u v) := hS.one_sub_mu_pos (u, s) (hseg ⟨rfl, hs⟩)
  have cx : ContinuousOn (fun s => S.theta u s / (S.lam u s : ℂ)) (Icc u v) :=
    ct.div (continuous_ofReal.comp_continuousOn cl) (fun s hs => by
      change (S.lam u s : ℂ) ≠ 0
      exact_mod_cast (pos_l s hs).ne')
  let f := fun s => Real.sqrt (S.lam u s) * Real.sqrt (1 - S.mu u s) *
    ‖S.theta u s / S.lam u s‖
  let g := fun s => Real.sqrt (S.lam u s) / Real.sqrt (1 - S.mu u s) *
    S.r u s * ‖S.phi u s‖
  have cf : ContinuousOn f (Icc u v) := (cl.sqrt.mul cg.sqrt).mul cx.norm
  have cgg : ContinuousOn g (Icc u v) :=
    ((cl.sqrt.div cg.sqrt (fun s hs => (Real.sqrt_pos.mpr (pos_g s hs)).ne')).mul cr).mul cp.norm
  have fsq (s : ℝ) (hs : s ∈ Icc u v) : f s ^ 2 =
      S.lam u s * (1 - S.mu u s) * ‖S.theta u s / S.lam u s‖ ^ 2 := by
    dsimp [f]
    rw [mul_pow, mul_pow, Real.sq_sqrt (pos_l s hs).le, Real.sq_sqrt (pos_g s hs).le]
  have gsq (s : ℝ) (hs : s ∈ Icc u v) : g s ^ 2 =
      S.lam u s * S.r u s ^ 2 * ‖S.phi u s‖ ^ 2 / (1 - S.mu u s) := by
    dsimp [g]
    rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt (pos_l s hs).le,
      Real.sq_sqrt (pos_g s hs).le]
    ring
  have fg (s : ℝ) (hs : s ∈ Icc u v) : f s * g s =
      S.lam u s * S.r u s * ‖S.phi u s‖ * ‖S.theta u s / S.lam u s‖ := by
    have hg0 := (Real.sqrt_pos.mpr (pos_g s hs)).ne'
    have he : f s * g s = Real.sqrt (S.lam u s) ^ 2 *
        S.r u s * ‖S.phi u s‖ * ‖S.theta u s / S.lam u s‖ := by
      dsimp [f, g]
      field_simp [hg0]
    rw [he, Real.sq_sqrt (pos_l s hs).le]
  have nr (s : ℝ) (hs : s ∈ Icc u v) : 0 ≤ S.r u s := by
    rcases eq_or_lt_of_le hs.1 with h | h
    · subst s
      rw [(hS.axis u (hseg ⟨rfl, le_rfl, huv.le⟩)).1]
    · exact (hS.r_pos (u, s) (hseg ⟨rfl, hs⟩) h).le
  have cgq := (cl.mul cr).mul (continuous_im.comp_continuousOn (cp.star.mul cx))
  have iq := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv.le cgq
  have ifg := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv.le (cf.mul cgg)
  have hp : ∀ s ∈ Icc u v, ‖S.lam u s * S.r u s *
      (starRingEnd ℂ (S.phi u s) * (S.theta u s / S.lam u s)).im‖ ≤ f s * g s := by
    intro s hs
    rw [fg s hs, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (pos_l s hs).le (nr s hs)), Real.norm_eq_abs]
    calc
      _ ≤ (S.lam u s * S.r u s) *
          (‖S.phi u s‖ * ‖S.theta u s / S.lam u s‖) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (pos_l s hs).le (nr s hs))
        simpa only [norm_mul, starRingEnd_apply, norm_star] using
          Complex.abs_im_le_norm (starRingEnd ℂ (S.phi u s) * (S.theta u s / S.lam u s))
      _ = _ := by ring
  have hq := (intervalIntegral.norm_integral_le_integral_norm huv.le).trans
    (intervalIntegral.integral_mono_on huv.le iq.norm ifg hp)
  have hq' : |S.Q u v| ≤ |e| * (∫ s in u..v, f s * g s) := by
    rw [Stab.oscillatory_charge_constraint hS huv.le hseg, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left hq (abs_nonneg e)
  have nfg : 0 ≤ ∫ s in u..v, f s * g s :=
    intervalIntegral.integral_nonneg huv.le (fun s hs => by
      rw [fg s hs]
      have := (pos_l s hs).le
      have := nr s hs
      positivity)
  calc
    S.Q u v ^ 2 = |S.Q u v| ^ 2 := (sq_abs _).symm
    _ ≤ (|e| * (∫ s in u..v, f s * g s)) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (abs_nonneg _) nfg)).mpr hq'
    _ = e ^ 2 * (∫ s in u..v, f s * g s) ^ 2 := by rw [mul_pow, sq_abs]
    _ ≤ e ^ 2 * ((∫ s in u..v, f s ^ 2) * (∫ s in u..v, g s ^ 2)) :=
      mul_le_mul_of_nonneg_left (integral_cauchy_schwarz huv.le cf cgg) (sq_nonneg _)
    _ = _ := by
      rw [intervalIntegral.integral_congr (fun s hs => fsq s (by
        simpa only [uIcc_of_le huv.le] using hs)),
        intervalIntegral.integral_congr (fun s hs => gsq s (by
          simpa only [uIcc_of_le huv.le] using hs))]
      ring

/-- [node restart-lem-relative-charge]
Relative charge controlled by ordinary Hawking mass, charged_SF_new_version.tex:L4345–4352.
The coefficient is exactly `e²`, with no smallness or geometric box premise. -/
theorem lem_relative_charge {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u < v) (hseg : outSeg u u v ⊆ D) :
    S.Q u v ^ 2 ≤ e ^ 2 * S.mu u v * S.r u v *
      (∫ s in u..v, S.lam u s * S.r u s ^ 2 * ‖S.phi u s‖ ^ 2 / (1 - S.mu u s)) := by
  have hB : 0 ≤ ∫ s in u..v,
      S.lam u s * S.r u s ^ 2 * ‖S.phi u s‖ ^ 2 / (1 - S.mu u s) :=
    intervalIntegral.integral_nonneg huv.le (fun s hs => by
      exact div_nonneg (mul_nonneg (mul_nonneg
        (hS.lam_pos (u, s) (hseg ⟨rfl, hs⟩)).le (sq_nonneg _)) (sq_nonneg _))
        (hS.one_sub_mu_pos (u, s) (hseg ⟨rfl, hs⟩)).le)
  have hle := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (RelCharge.mass_controls_radial_flux hS huv hseg)
      (sq_nonneg e)) hB
  have hr := (hS.r_pos (u, v) (hseg ⟨rfl, huv.le, le_rfl⟩) huv).ne'
  calc
    _ ≤ _ := (RelCharge.maxwell_cauchy_schwarz hS huv hseg).trans hle
    _ = _ := by dsimp [Fields.mu]; field_simp

/-- [node restart-lem-relative-charge]
The explicit consequence `restart-eq-relative-charge` of relative charge,
charged_SF_new_version.tex:L4353–4356.
The exact coefficient `1 / (3κ)` is uniform over the coupling, scalar bound,
cone, and solution. The gap and scalar bounds hold on the whole cone segment. -/
theorem eq_relative_charge {e κ M : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u < v) (hseg : outSeg u u v ⊆ D)
    (hκ : 0 < κ) (hgap : ∀ s ∈ Icc u v, κ ≤ 1 - S.mu u s)
    (hM : ∀ s ∈ Icc u v, ‖S.phi u s‖ ≤ M) :
    S.Q u v ^ 2 / S.r u v ^ 2 ≤ (e ^ 2 * M ^ 2 * S.r u v ^ 2 / (3 * κ)) * S.mu u v := by
  have cl := continuousOn_out_section hS.cont_lam hseg
  have cr := continuousOn_out_section hS.cont_r hseg
  have cp := continuousOn_out_section hS.cont_phi hseg
  have cg : ContinuousOn (fun s => 1 - S.mu u s) (Icc u v) :=
    continuousOn_const.sub (continuousOn_mu_out hS huv hseg)
  have pos_g (s : ℝ) (hs : s ∈ Icc u v) := hκ.trans_le (hgap s hs)
  have iB : IntervalIntegrable (fun s =>
      S.lam u s * S.r u s ^ 2 * ‖S.phi u s‖ ^ 2 / (1 - S.mu u s)) volume u v :=
    ContinuousOn.intervalIntegrable_of_Icc huv.le
      (((cl.mul (cr.pow 2)).mul (cp.norm.pow 2)).div cg (fun s hs => (pos_g s hs).ne'))
  have iB' : IntervalIntegrable
      (fun s => S.lam u s * S.r u s ^ 2 * (M ^ 2 / κ)) volume u v :=
    ContinuousOn.intervalIntegrable_of_Icc huv.le ((cl.mul (cr.pow 2)).mul continuousOn_const)
  have hB := intervalIntegral.integral_mono_on huv.le iB iB' (fun s hs => by
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM s hs)
    have hsq := (sq_le_sq₀ (norm_nonneg _) hM0).mpr (hM s hs)
    have hdiv : ‖S.phi u s‖ ^ 2 / (1 - S.mu u s) ≤ M ^ 2 / κ :=
      (div_le_div_of_nonneg_right hsq (pos_g s hs).le).trans
        (div_le_div_of_nonneg_left (sq_nonneg M) hκ (hgap s hs))
    calc
      _ = (S.lam u s * S.r u s ^ 2) * (‖S.phi u s‖ ^ 2 / (1 - S.mu u s)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hdiv
        (mul_nonneg (hS.lam_pos (u, s) (hseg ⟨rfl, hs⟩)).le (sq_nonneg _)))
  rw [intervalIntegral.integral_mul_const, outgoing_radius_moment hS huv.le hseg 2] at hB
  have hflux : 0 ≤ ∫ s in u..v,
      S.lam u s * (1 - S.mu u s) * ‖S.theta u s / S.lam u s‖ ^ 2 :=
    intervalIntegral.integral_nonneg huv.le (fun s hs =>
      mul_nonneg (mul_nonneg (hS.lam_pos (u, s) (hseg ⟨rfl, hs⟩)).le
        (pos_g s hs).le) (sq_nonneg _))
  have hm := hflux.trans (RelCharge.mass_controls_radial_flux hS huv hseg)
  have hr := hS.r_pos (u, v) (hseg ⟨rfl, huv.le, le_rfl⟩) huv
  have hmu : 0 ≤ S.mu u v := div_nonneg hm hr.le
  have htotal := (lem_relative_charge hS huv hseg).trans
    (mul_le_mul_of_nonneg_left hB (mul_nonneg (mul_nonneg (sq_nonneg e) hmu) hr.le))
  apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
  calc
    _ ≤ _ := htotal
    _ = _ := by
      field_simp
      ring

end EmcsfAcExtension.Local
