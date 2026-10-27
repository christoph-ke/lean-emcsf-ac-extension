module

public import EmcsfAcExtension.Local.Defs.Recon
public import EmcsfAcExtension.Frozen.Fields.NormalizedOut
public import EmcsfAcExtension.Frozen.Fields.NormalizedIn
import EmcsfAcExtension.Infra.AC.Quotient

/-! # Outgoing radial reconstruction

Sectionwise calculus for the literal reconstruction maps of
`charged_SF_new_version.tex:L5948–L5973`.
The estimates and axis integrability needed to apply this calculus are proved in `CenterOrders`.
No incoming equation for an arbitrary candidate is asserted here.
-/

public section

open MeasureTheory Set Filter Topology Complex

namespace EmcsfAcExtension.Local.Recon

variable {e : ℝ} {lam : ℝ → ℝ → ℝ} {hh : ℝ → ℝ → ℂ} {u b v : ℝ}

/-- [node restart-sec-independent-null-construction#scalar-axis-value]
The prescribed scalar value at the axis (charged_SF_new_version.tex:L5958). -/
@[simp] theorem phi_axis : phi lam hh u u = hh u u := by simp [phi]

/-- The scalar oscillation vanishes at the axis. -/
@[simp] theorem ratio_axis : ratio lam hh u u = 0 := by simp [ratio]

/-- The radius vanishes at the axis. -/
@[simp] theorem r_axis : r lam u u = 0 := by simp [r]

/-- The charge vanishes at the axis. -/
@[simp] theorem Q_axis : Q e lam hh u u = 0 := by simp [Q]

/-- The mass vanishes at the axis. -/
@[simp] theorem m_axis : m e lam hh u u = 0 := by simp [m]

/-- The totalized mass ratio is zero at the axis. -/
@[simp] theorem mu_axis : mu e lam hh u u = 0 := by simp [mu]

/-- The outgoing exponential has the prescribed ingoing normalization. -/
@[simp] theorem nu_axis : nu e lam hh u u = -lam u u := by simp [nu]

/-- The electromagnetic potential vanishes at the axis. -/
@[simp] theorem A_axis : A e lam hh u u = 0 := by simp [A]

/-- Reconstruction recovers the prescribed normalized outgoing scalar wherever `λ ≠ 0`. -/
theorem toFields_a_eq (hlam : lam u v ≠ 0) : (toFields e lam hh).a u v = hh u v := by
  simp [Fields.a, toFields, ratio, hlam]

/-- All regular-axis field normalizations of the reconstructed configuration.
These are literal axis identities, requiring no regularity premise. -/
theorem toFields_axis :
    (toFields e lam hh).r u u = 0 ∧ (toFields e lam hh).m u u = 0 ∧
    (toFields e lam hh).Q u u = 0 ∧ (toFields e lam hh).A u u = 0 ∧
    (toFields e lam hh).lam u u + (toFields e lam hh).nu u u = 0 ∧
    (toFields e lam hh).a u u = (toFields e lam hh).phi u u ∧
    (toFields e lam hh).b u u = (toFields e lam hh).phi u u := by
  simp [Fields.a, Fields.b, toFields]

/-- Positive lower and upper bounds on the candidate give the corresponding radius bounds.
The constants are exactly the displayed candidate bounds, independently of the candidate. -/
theorem r_bounds {l U : ℝ} (huv : u ≤ v) (hlam : ContinuousOn (lam u) (Icc u v))
    (hlo : ∀ s ∈ Icc u v, l ≤ lam u s) (hup : ∀ s ∈ Icc u v, lam u s ≤ U) :
    l * (v - u) ≤ r lam u v ∧ r lam u v ≤ U * (v - u) := by
  have hi := hlam.intervalIntegrable_of_Icc (μ := volume) huv
  constructor
  · simpa [r, mul_comm] using
      intervalIntegral.integral_mono_on huv intervalIntegrable_const hi hlo
  · simpa [r, mul_comm] using
      intervalIntegral.integral_mono_on huv hi intervalIntegrable_const hup

/-- A positive continuous candidate has positive reconstructed radius off the axis. -/
theorem r_pos {l : ℝ} (hl : 0 < l) (huv : u < v)
    (hlam : ContinuousOn (lam u) (Icc u v)) (hlo : ∀ s ∈ Icc u v, l ≤ lam u s) :
    0 < r lam u v := by
  have hi := hlam.intervalIntegrable_of_Icc (μ := volume) huv.le
  have hb := intervalIntegral.integral_mono_on huv.le intervalIntegrable_const hi hlo
  have : l * (v - u) ≤ r lam u v := by simpa [r, mul_comm] using hb
  exact (mul_pos hl (sub_pos.mpr huv)).trans_le this

/-- Off the axis, multiplication by radius cancels the scalar average denominator. -/
theorem r_mul_phi (huv : u < v) (hr : r lam u v ≠ 0) :
    (r lam u v : ℂ) * phi lam hh u v = ∫ s in u..v, (lam u s : ℂ) * hh u s := by
  simp [phi, huv, hr]

/-- The scalar oscillation is the normalized weighted difference from the endpoint value. -/
theorem ratio_integral (huv : u < v) (hr : r lam u v ≠ 0)
    (hlam : ContinuousOn (lam u) (Icc u v)) (hhc : ContinuousOn (hh u) (Icc u v)) :
    ratio lam hh u v = (r lam u v : ℂ)⁻¹ *
      ∫ s in u..v, (lam u s : ℂ) * (hh u v - hh u s) := by
  have hc := Complex.continuous_ofReal.comp_continuousOn hlam
  have hi := hc.intervalIntegrable_of_Icc (μ := volume) huv.le
  have hhi := (hc.mul hhc).intervalIntegrable_of_Icc (μ := volume) huv.le
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub (f := fun s => (lam u s : ℂ) * hh u v)
    (g := fun s => (lam u s : ℂ) * hh u s) (hi.mul_const (hh u v)) hhi]
  simp only [mul_sub, intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal]
  simp [ratio, phi, huv, ← r_def, hr]

/-- A positive weighted scalar average preserves a uniform scalar bound.
The bound `H` is fixed before the candidate, and no charge or gap bound is needed. -/
theorem norm_phi_le {l H : ℝ} (hl : 0 < l) (huv : u ≤ v)
    (hlam : ContinuousOn (lam u) (Icc u v)) (hhc : ContinuousOn (hh u) (Icc u v))
    (hlo : ∀ s ∈ Icc u v, l ≤ lam u s) (hhH : ∀ s ∈ Icc u v, ‖hh u s‖ ≤ H) :
    ‖phi lam hh u v‖ ≤ H := by
  rcases huv.eq_or_lt with rfl | huv
  · simpa using hhH u (by simp)
  have hr := r_pos hl huv hlam hlo
  simp only [phi, huv, ite_true]
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr, inv_mul_le_iff₀ hr]
  have hb := intervalIntegral.norm_integral_le_of_norm_le huv.le
    (f := fun s => (lam u s : ℂ) * hh u s) (g := fun s => lam u s * H)
    (Filter.Eventually.of_forall fun s hs => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hl.trans_le (hlo s ⟨hs.1.le, hs.2⟩))]
      exact mul_le_mul_of_nonneg_left (hhH s ⟨hs.1.le, hs.2⟩)
        (hl.le.trans (hlo s ⟨hs.1.le, hs.2⟩)))
    ((hlam.intervalIntegrable_of_Icc (μ := volume) huv.le).mul_const H)
  simpa [intervalIntegral.integral_mul_const, r, mul_comm] using hb

/-- A Lipschitz scalar candidate has linearly vanishing oscillation.
The displayed constant `D` is uniform in the candidate and in the section. -/
theorem norm_ratio_le_of_lipschitz {l D : ℝ} (hl : 0 < l) (hD : 0 ≤ D) (huv : u ≤ v)
    (hlam : ContinuousOn (lam u) (Icc u v)) (hhc : ContinuousOn (hh u) (Icc u v))
    (hlo : ∀ s ∈ Icc u v, l ≤ lam u s)
    (hd : ∀ s ∈ Icc u v, ‖hh u v - hh u s‖ ≤ D * (v - s)) :
    ‖ratio lam hh u v‖ ≤ D * (v - u) := by
  rcases huv.eq_or_lt with rfl | huv
  · simp
  have hr := r_pos hl huv hlam hlo
  rw [ratio_integral huv hr.ne' hlam hhc, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hr, inv_mul_le_iff₀ hr]
  have hb := intervalIntegral.norm_integral_le_of_norm_le huv.le
    (f := fun s => (lam u s : ℂ) * (hh u v - hh u s))
    (g := fun s => lam u s * (D * (v - u))) (Filter.Eventually.of_forall fun s hs => by
      have hs' : s ∈ Icc u v := ⟨hs.1.le, hs.2⟩
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hl.trans_le (hlo s hs'))]
      exact mul_le_mul_of_nonneg_left
        ((hd s hs').trans (mul_le_mul_of_nonneg_left (by linarith [hs'.1]) hD))
        (hl.le.trans (hlo s hs')))
    ((hlam.intervalIntegrable_of_Icc (μ := volume) huv.le).mul_const _)
  simpa [intervalIntegral.integral_mul_const, r, mul_comm] using hb

/-- Bounded outgoing derivatives imply the sectionwise Lipschitz estimate used above. -/
theorem norm_sub_le_of_hasDerivWithinAt {h' : ℝ → ℂ} {D s t : ℝ}
    (hd : ∀ x ∈ Icc u b, HasDerivWithinAt (hh u) (h' x) (Icc u b) x)
    (hb : ∀ x ∈ Icc u b, ‖h' x‖ ≤ D) (hs : s ∈ Icc u b) (ht : t ∈ Icc u b) :
    ‖hh u t - hh u s‖ ≤ D * |t - s| := by
  simpa [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Icc u b) hs ht

/-- [node restart-null-reconstruct-rphi]
The radial primitive solves the outgoing radius equation, including one-sided endpoints. -/
theorem hasDerivWithinAt_r (hlam : ContinuousOn (lam u) (Icc u b)) (hv : v ∈ Icc u b) :
    HasDerivWithinAt (r lam u) (lam u v) (Icc u b) v := by
  have : Fact (v ∈ Icc u b) := ⟨hv⟩
  exact intervalIntegral.integral_hasDerivWithinAt_right (s := Icc u b) (t := Icc u b)
    ((hlam.mono (Icc_subset_Icc le_rfl hv.2)).intervalIntegrable_of_Icc hv.1)
    (hlam.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc v) (hlam v hv)

/-- The FTC on a closed outgoing interval, for real or complex continuous densities. -/
theorem hasDerivWithinAt_primitive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {g : ℝ → E} (hg : ContinuousOn g (Icc u b)) (hv : v ∈ Icc u b) :
    HasDerivWithinAt (fun x => ∫ s in u..x, g s) (g v) (Icc u b) v := by
  have : Fact (v ∈ Icc u b) := ⟨hv⟩
  exact intervalIntegral.integral_hasDerivWithinAt_right (s := Icc u b) (t := Icc u b)
    ((hg.mono (Icc_subset_Icc le_rfl hv.2)).intervalIntegrable_of_Icc hv.1)
    (hg.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc v) (hg v hv)

/-- Continuity of a primitive on the entire closed outgoing interval. -/
theorem continuousOn_primitive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} (hub : u ≤ b) (hg : IntervalIntegrable g volume u b) :
    ContinuousOn (fun x => ∫ s in u..x, g s) (Icc u b) := by
  have hi : IntegrableOn g (uIcc u b) := by
    rw [uIcc_of_le hub]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hub).mp hg
  simpa only [uIcc_of_le hub] using intervalIntegral.continuousOn_primitive_interval hi

/-- [node restart-null-reconstruct-rphi]
The scalar reconstruction solves its outgoing equation off the axis. -/
theorem hasDerivWithinAt_phi (hlam : ContinuousOn (lam u) (Icc u b))
    (hhc : ContinuousOn (hh u) (Icc u b)) (hv : v ∈ Icc u b) (huv : u < v)
    (hr : r lam u v ≠ 0) : HasDerivWithinAt (phi lam hh u)
      ((lam u v : ℂ) * ratio lam hh u v / (r lam u v : ℂ)) (Icc u b) v := by
  have hc := Complex.continuous_ofReal.comp_continuousOn hlam
  have hn := hasDerivWithinAt_primitive (hc.mul hhc) hv
  have hd := (hasDerivWithinAt_r hlam hv).ofReal_comp
  have hrC : (r lam u v : ℂ) ≠ 0 := by exact_mod_cast hr
  have he : phi lam hh u =ᶠ[𝓝[Icc u b] v]
      (fun x => (∫ s in u..x, (lam u s : ℂ) * hh u s) / (r lam u x : ℂ)) := by
    filter_upwards [(eventually_gt_nhds huv).filter_mono nhdsWithin_le_nhds] with x hx
    simp [phi, hx, div_eq_inv_mul]
  have hq := (hn.div hd hrC).congr_of_eventuallyEq he (by
    simp [phi, huv, div_eq_inv_mul])
  dsimp only [Function.comp_apply, Pi.mul_apply] at hq
  convert hq using 1
  simp only [ratio, phi, huv, ite_true]
  field_simp

/-- The current may be expressed in terms of the reconstructed outgoing scalar derivative. -/
theorem current_eq_theta :
    lam u v * (starRingEnd ℂ (phi lam hh u v) * hh u v).im =
      (starRingEnd ℂ (phi lam hh u v) * ((lam u v : ℂ) * ratio lam hh u v)).im := by
  simp [ratio, mul_sub, Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The radius times the scalar is the prescribed outgoing primitive, including at the axis.
Its derivative needs no scalar derivative assumption. -/
theorem hasDerivWithinAt_r_mul_phi {l : ℝ} (hl : 0 < l)
    (hlam : ContinuousOn (lam u) (Icc u b)) (hhc : ContinuousOn (hh u) (Icc u b))
    (hlo : ∀ s ∈ Icc u b, l ≤ lam u s) (hv : v ∈ Icc u b) :
    HasDerivWithinAt (fun x => (r lam u x : ℂ) * phi lam hh u x)
      ((lam u v : ℂ) * hh u v) (Icc u b) v := by
  have he (x) (hx : x ∈ Icc u b) : (r lam u x : ℂ) * phi lam hh u x =
      ∫ s in u..x, (lam u s : ℂ) * hh u s := by
    rcases hx.1.eq_or_lt with rfl | hux
    · simp
    · exact r_mul_phi hux (r_pos hl hux (hlam.mono (Icc_subset_Icc le_rfl hx.2))
        (fun s hs => hlo s ⟨hs.1, hs.2.trans hx.2⟩)).ne'
  exact (hasDerivWithinAt_primitive
    ((Complex.continuous_ofReal.comp_continuousOn hlam).mul hhc) hv).congr he (he v hv)

/-- The charge constraint from continuity of the reconstructed scalar.
`CenterOrders` supplies this continuity for bounded `C¹ᵥ` candidates. -/
theorem hasDerivWithinAt_Q_of_continuous (hlam : ContinuousOn (lam u) (Icc u b))
    (hhc : ContinuousOn (hh u) (Icc u b))
    (hphi : ContinuousOn (phi lam hh u) (Icc u b)) (hv : v ∈ Icc u b) :
    HasDerivWithinAt (Q e lam hh u)
      (-e * r lam u v *
        (starRingEnd ℂ (phi lam hh u v) * ((lam u v : ℂ) * ratio lam hh u v)).im)
      (Icc u b) v := by
  have hc := (continuousOn_primitive (hv.1.trans hv.2)
    (hlam.intervalIntegrable_of_Icc (hv.1.trans hv.2))).mul hlam
  have hj := Complex.continuous_im.comp_continuousOn
    ((Complex.continuous_conj.comp_continuousOn hphi).mul hhc)
  have hd := (hasDerivWithinAt_primitive (hc.mul hj) hv).const_mul (-e)
  convert hd using 1
  · ext x
    simp [Q, r]
  · rw [← current_eq_theta]
    dsimp only [r, Function.comp_apply, Pi.mul_apply]
    ring

/-- The ingoing null derivative is negative for every positive axis optical factor.
This sign statement does not need an integrability or gap assumption. -/
theorem nu_neg (hlam : 0 < lam u u) : nu e lam hh u v < 0 := by
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hlam) (Real.exp_pos _)

private theorem factor_integral {a f : ℝ → ℝ} (ha : IntervalIntegrable a volume u b)
    (hv : v ∈ Icc u b) :
    (∫ s in u..v, f s * Real.exp (-∫ t in s..v, a t)) =
      Real.exp (-∫ t in u..v, a t) *
        ∫ s in u..v, Real.exp (∫ t in u..s, a t) * f s := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc u b := by
    rw [uIcc_of_le hv.1] at hs
    exact ⟨hs.1, hs.2.trans hv.2⟩
  have hv' : v ∈ uIcc u b := Icc_subset_uIcc hv
  have hs'' : s ∈ uIcc u b := Icc_subset_uIcc hs'
  have hsub := intervalIntegral.integral_interval_sub_left
    (ha.mono_set (uIcc_subset_uIcc left_mem_uIcc hv'))
    (ha.mono_set (uIcc_subset_uIcc left_mem_uIcc hs''))
  dsimp only
  rw [show -(∫ t in s..v, a t) = -(∫ t in u..v, a t) + ∫ t in u..s, a t by
    linarith [hsub], Real.exp_add]
  ring

/-- The linear outgoing mass equation, under continuity of its two radial coefficients.
The main construction theorem derives both continuity premises from the candidate bounds. -/
theorem hasDerivWithinAt_m_of_continuous
    (ha : ContinuousOn (fun s => lam u s * ‖ratio lam hh u s‖ ^ 2 / r lam u s) (Icc u b))
    (hf : ContinuousOn (fun s => lam u s *
      (‖ratio lam hh u s‖ ^ 2 + Q e lam hh u s ^ 2 / r lam u s ^ 2)) (Icc u b))
    (hv : v ∈ Icc u b) : HasDerivWithinAt (m e lam hh u)
      ((1 - mu e lam hh u v) * lam u v * ‖ratio lam hh u v‖ ^ 2 / 2 +
        lam u v * Q e lam hh u v ^ 2 / (2 * r lam u v ^ 2)) (Icc u b) v := by
  let a := fun s => lam u s * ‖ratio lam hh u s‖ ^ 2 / r lam u s
  let f := fun s => lam u s * (‖ratio lam hh u s‖ ^ 2 +
    Q e lam hh u s ^ 2 / r lam u s ^ 2)
  let p := fun x => ∫ s in u..x, a s
  have hub := hv.1.trans hv.2
  have hp : ContinuousOn p (Icc u b) :=
    continuousOn_primitive hub (ha.intervalIntegrable_of_Icc hub)
  have hrep (x) (hx : x ∈ Icc u b) : m e lam hh u x =
      (1 / 2 : ℝ) * (Real.exp (-p x) * ∫ s in u..x, Real.exp (p s) * f s) := by
    exact congrArg ((1 / 2 : ℝ) * ·) (factor_integral (ha.intervalIntegrable_of_Icc hub) hx)
  have hd := (((hasDerivWithinAt_primitive ha hv).neg.exp).mul
    (hasDerivWithinAt_primitive ((Real.continuous_exp.comp_continuousOn hp).mul hf) hv)).const_mul
      (1 / 2 : ℝ)
  have hd' := hd.congr (fun x hx => hrep x hx) (hrep v hv)
  convert hd' using 1
  change (1 - 2 * m e lam hh u v / r lam u v) * lam u v *
      ‖ratio lam hh u v‖ ^ 2 / 2 + lam u v * Q e lam hh u v ^ 2 /
      (2 * r lam u v ^ 2) = _
  rw [hrep v hv]
  have he : Real.exp (-p v) * Real.exp (p v) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  dsimp only [a, f, p, Function.comp_apply, Pi.mul_apply, Pi.neg_apply] at he ⊢
  linear_combination -(lam u v * (‖ratio lam hh u v‖ ^ 2 +
    Q e lam hh u v ^ 2 / r lam u v ^ 2) / 2) * he

/-- The outgoing null-derivative equation from continuity of its radial coefficient. -/
theorem hasDerivWithinAt_nu_of_continuous
    (hc : ContinuousOn (fun s => lam u s / r lam u s * z e lam hh u s) (Icc u b))
    (hv : v ∈ Icc u b) : HasDerivWithinAt (nu e lam hh u)
      (nu e lam hh u v * lam u v / r lam u v * z e lam hh u v) (Icc u b) v := by
  convert (hasDerivWithinAt_primitive hc hv).exp.const_mul (-lam u u) using 1
  · rfl
  · dsimp only [nu]
    ring

/-- The outgoing potential equation from continuity of its radial coefficient. -/
theorem hasDerivWithinAt_A_of_continuous
    (hc : ContinuousOn (fun s => 2 * nu e lam hh u s * lam u s * Q e lam hh u s /
      ((1 - mu e lam hh u s) * r lam u s ^ 2)) (Icc u b)) (hv : v ∈ Icc u b) :
    HasDerivWithinAt (A e lam hh u)
      (2 * nu e lam hh u v * lam u v * Q e lam hh u v /
        ((1 - mu e lam hh u v) * r lam u v ^ 2)) (Icc u b) v :=
  hasDerivWithinAt_primitive hc hv

/-- Continuity at an axis from a continuous vanishing majorant, together with off-axis
continuity within the same closed interval. This applies to the raw totalized quotients
whose axis value is zero. -/
theorem continuousOn_of_axis_bound {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    {g : ℝ → ℝ} (hf : f u = 0) (hg : ContinuousAt g u) (hg0 : g u = 0)
    (hb : ∀ x ∈ Icc u b, ‖f x‖ ≤ g x)
    (hc : ∀ x ∈ Icc u b, u < x → ContinuousWithinAt f (Icc u b) x) :
    ContinuousOn f (Icc u b) := by
  intro x hx
  rcases hx.1.eq_or_lt with rfl | hux
  · change Tendsto f (𝓝[Icc u b] u) (𝓝 (f u))
    rw [hf, tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (g := g) (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact hb y hy
    · rw [← hg0]
      exact hg.continuousWithinAt
  · exact hc x hx hux

/-- The scalar average is continuous up to the axis for a Lipschitz candidate.
No gap assumption, incoming regularity or bound on the scalar's absolute value is needed. -/
theorem continuousOn_phi_of_lipschitz {l D : ℝ} (hl : 0 < l) (hD : 0 ≤ D) (hub : u ≤ b)
    (hlam : ContinuousOn (lam u) (Icc u b)) (hhc : ContinuousOn (hh u) (Icc u b))
    (hlo : ∀ s ∈ Icc u b, l ≤ lam u s)
    (hd : ∀ s ∈ Icc u b, ∀ t ∈ Icc u b, ‖hh u t - hh u s‖ ≤ D * |t - s|) :
    ContinuousOn (phi lam hh u) (Icc u b) := by
  have hb (x) (hx : x ∈ Icc u b) : ‖phi lam hh u x - hh u u‖ ≤ 2 * D * (x - u) := by
    have hsub : Icc u x ⊆ Icc u b := Icc_subset_Icc le_rfl hx.2
    have hf := norm_ratio_le_of_lipschitz hl hD hx.1 (hlam.mono hsub) (hhc.mono hsub)
      (fun s hs => hlo s (hsub hs)) (fun s hs => by
        simpa [abs_of_nonneg (sub_nonneg.mpr hs.2)] using hd s (hsub hs) x hx)
    calc
      _ = ‖(hh u x - hh u u) - ratio lam hh u x‖ := by congr 1; simp [ratio]
      _ ≤ ‖hh u x - hh u u‖ + ‖ratio lam hh u x‖ := norm_sub_le _ _
      _ ≤ D * (x - u) + D * (x - u) := add_le_add
        (by simpa [abs_of_nonneg (sub_nonneg.mpr hx.1)] using hd u ⟨le_rfl, hub⟩ x hx) hf
      _ = _ := by ring
  have hc : ContinuousOn (fun x => phi lam hh u x - hh u u) (Icc u b) := by
    apply continuousOn_of_axis_bound (by simp) (by fun_prop) (by ring) hb
    intro x hx hux
    exact (hasDerivWithinAt_phi hlam hhc hx hux
      (r_pos hl hux (hlam.mono (Icc_subset_Icc le_rfl hx.2))
        (fun s hs => hlo s ⟨hs.1, hs.2.trans hx.2⟩)).ne').continuousWithinAt.sub
      continuousWithinAt_const
  exact (hc.add (continuousOn_const (c := hh u u))).congr (by intro x hx; simp)

/-- Cancellation of the real self-current in the reconstructed charge density. -/
theorem current_eq_ratio :
    (starRingEnd ℂ (phi lam hh u v) * hh u v).im =
      (starRingEnd ℂ (phi lam hh u v) * ratio lam hh u v).im := by
  simp only [ratio, mul_sub, Complex.sub_im, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- A charge bound from explicit radius, scalar and oscillation bounds.
All constants on the right are fixed candidate bounds; none depends on the candidate. -/
theorem abs_Q_le_of_bounds {U H D : ℝ} (hU : 0 ≤ U) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (huv : u ≤ v)
    (hr : ∀ s ∈ Icc u v, 0 ≤ r lam u s ∧ r lam u s ≤ U * (s - u))
    (hlam : ∀ s ∈ Icc u v, 0 ≤ lam u s ∧ lam u s ≤ U)
    (hphi : ∀ s ∈ Icc u v, ‖phi lam hh u s‖ ≤ H)
    (hf : ∀ s ∈ Icc u v, ‖ratio lam hh u s‖ ≤ D * (s - u)) :
    |Q e lam hh u v| ≤ (|e| * H * U ^ 2 * D) * (v - u) ^ 3 := by
  rw [Q, abs_neg, abs_mul]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := u) (b := v) (f := fun s => r lam u s * lam u s *
      (starRingEnd ℂ (phi lam hh u s) * hh u s).im)
    (C := U ^ 2 * H * D * (v - u) ^ 2) (fun s hs => by
      have hs' : s ∈ Icc u v := by
        have := uIoc_subset_uIcc hs
        simpa [uIcc_of_le huv] using this
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hr s hs').1,
        abs_of_nonneg (hlam s hs').1, current_eq_ratio]
      have him : |(starRingEnd ℂ (phi lam hh u s) * ratio lam hh u s).im| ≤
          H * (D * (s - u)) := by
        apply (Complex.abs_im_le_norm _).trans
        rw [norm_mul, show ‖starRingEnd ℂ (phi lam hh u s)‖ = ‖phi lam hh u s‖ by simp]
        exact mul_le_mul (hphi s hs') (hf s hs') (norm_nonneg _) hH
      calc
        _ ≤ (U * (s - u)) * U * (H * (D * (s - u))) :=
          mul_le_mul (mul_le_mul (hr s hs').2 (hlam s hs').2 (hlam s hs').1
            (mul_nonneg hU (sub_nonneg.mpr hs'.1))) him (abs_nonneg _)
            (mul_nonneg (mul_nonneg hU (sub_nonneg.mpr hs'.1)) hU)
        _ ≤ U ^ 2 * H * D * (v - u) ^ 2 := by
          calc
            _ = U ^ 2 * H * D * (s - u) ^ 2 := by ring
            _ ≤ _ := by gcongr <;> linarith [hs'.1, hs'.2])
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr huv)] at hb
  calc
    _ ≤ |e| * (U ^ 2 * H * D * (v - u) ^ 2 * (v - u)) :=
      mul_le_mul_of_nonneg_left hb (abs_nonneg e)
    _ = _ := by ring

/-- Squared electric term after cancellation of the positive radius factor.
`K` is a fixed cubic charge bound, and `l` is the fixed positive lower optical bound. -/
theorem charge_sq_div_r_sq_le_of_bounds {l K : ℝ} (hl : 0 < l) (hK : 0 ≤ K)
    (huv : u < v) (hr : l * (v - u) ≤ r lam u v)
    (hQ : |Q e lam hh u v| ≤ K * (v - u) ^ 3) :
    Q e lam hh u v ^ 2 / r lam u v ^ 2 ≤ (K / l) ^ 2 * (v - u) ^ 4 := by
  have hx : 0 < v - u := sub_pos.mpr huv
  have hr0 : 0 < r lam u v := (mul_pos hl hx).trans_le hr
  calc
    _ = (|Q e lam hh u v| / r lam u v) ^ 2 := by rw [div_pow, sq_abs]
    _ ≤ (K * (v - u) ^ 3 / (l * (v - u))) ^ 2 := by gcongr
    _ = _ := by field_simp

/-- The mass exponential lies in `(0,1]` on an outgoing prefix with positive optical factor. -/
theorem mass_exp_le_one {s : ℝ} (hus : u ≤ s) (hsv : s ≤ v)
    (hlam : ∀ t ∈ Icc u v, 0 ≤ lam u t) (hr : ∀ t ∈ Icc u v, 0 ≤ r lam u t) :
    Real.exp (-∫ t in s..v, lam u t * ‖ratio lam hh u t‖ ^ 2 / r lam u t) ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact neg_nonpos.mpr (intervalIntegral.integral_nonneg hsv fun t ht =>
    div_nonneg (mul_nonneg (hlam t ⟨hus.trans ht.1, ht.2⟩) (sq_nonneg _))
      (hr t ⟨hus.trans ht.1, ht.2⟩))

/-- A cubic mass bound from fixed optical and scalar oscillation bounds.
The coefficient depends only on `l,U,D,K,L`, uniformly in the candidate and vertex. -/
theorem mass_bounds_of_bounds {l U D K L : ℝ} (hl : 0 < l) (hU : 0 ≤ U)
    (_hD : 0 ≤ D) (hK : 0 ≤ K) (_hL : 0 ≤ L) (huv : u ≤ v) (hvL : v - u ≤ L)
    (hr : ∀ s ∈ Icc u v, l * (s - u) ≤ r lam u s)
    (hlam : ∀ s ∈ Icc u v, 0 ≤ lam u s ∧ lam u s ≤ U)
    (hf : ∀ s ∈ Icc u v, ‖ratio lam hh u s‖ ≤ D * (s - u))
    (hQ : ∀ s ∈ Icc u v, |Q e lam hh u s| ≤ K * (s - u) ^ 3) :
    0 ≤ m e lam hh u v ∧ m e lam hh u v ≤
      (U * (D ^ 2 + (K / l) ^ 2 * L ^ 2) / 2) * (v - u) ^ 3 := by
  have hr0 (s) (hs : s ∈ Icc u v) : 0 ≤ r lam u s :=
    (mul_nonneg hl.le (sub_nonneg.mpr hs.1)).trans (hr s hs)
  have hpos (s) (hs : s ∈ Icc u v) : 0 ≤ lam u s *
      (‖ratio lam hh u s‖ ^ 2 + Q e lam hh u s ^ 2 / r lam u s ^ 2) *
      Real.exp (-∫ t in s..v, lam u t * ‖ratio lam hh u t‖ ^ 2 / r lam u t) := by
    have := (hlam s hs).1
    positivity
  refine ⟨mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg huv hpos), ?_⟩
  rcases huv.eq_or_lt with rfl | huv
  · simp
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := u) (b := v) (f := fun s => lam u s *
      (‖ratio lam hh u s‖ ^ 2 + Q e lam hh u s ^ 2 / r lam u s ^ 2) *
      Real.exp (-∫ t in s..v, lam u t * ‖ratio lam hh u t‖ ^ 2 / r lam u t))
    (C := U * (D ^ 2 + (K / l) ^ 2 * L ^ 2) * (v - u) ^ 2) (fun s hs => by
      have hs' : s ∈ Icc u v := by
        have := uIoc_subset_uIcc hs
        simpa [uIcc_of_le huv.le] using this
      rw [Real.norm_eq_abs, abs_of_nonneg (hpos s hs')]
      have hq : Q e lam hh u s ^ 2 / r lam u s ^ 2 ≤
          (K / l) ^ 2 * L ^ 2 * (v - u) ^ 2 := by
        rcases hs'.1.eq_or_lt with rfl | hus
        · simp only [Q_axis, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
            r_axis, div_zero]
          positivity
        · calc
            _ ≤ (K / l) ^ 2 * (s - u) ^ 4 :=
              charge_sq_div_r_sq_le_of_bounds hl hK hus (hr s hs') (hQ s hs')
            _ = (K / l) ^ 2 * (s - u) ^ 2 * (s - u) ^ 2 := by ring
            _ ≤ _ := by gcongr <;> linarith [hs'.1, hs'.2]
      have hf' : ‖ratio lam hh u s‖ ^ 2 ≤ D ^ 2 * (v - u) ^ 2 := by
        calc
          _ ≤ (D * (s - u)) ^ 2 := by gcongr; exact hf s hs'
          _ = D ^ 2 * (s - u) ^ 2 := mul_pow _ _ _
          _ ≤ _ := by gcongr <;> linarith [hs'.1, hs'.2]
      calc
        _ ≤ U * (D ^ 2 * (v - u) ^ 2 +
            (K / l) ^ 2 * L ^ 2 * (v - u) ^ 2) * 1 := by
          apply mul_le_mul
          · exact mul_le_mul (hlam s hs').2 (add_le_add hf' hq)
              (by positivity) hU
          · exact mass_exp_le_one (hh := hh) hs'.1 hs'.2 (fun t ht => (hlam t ht).1) hr0
          · positivity
          · positivity
        _ = _ := by ring)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr huv.le)] at hb
  change (1 / 2 : ℝ) * _ ≤ _
  calc
    _ ≤ (1 / 2 : ℝ) * (U * (D ^ 2 + (K / l) ^ 2 * L ^ 2) *
        (v - u) ^ 2 * (v - u)) := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hb) (by norm_num)
    _ = _ := by ring

/-- Cancellation of powers of radius in an explicit vanishing-order bound.
`C` and `l` are fixed bounds, and the resulting coefficient is exactly `C/l^j`. -/
theorem abs_div_pow_le_of_order {a r x C l : ℝ} {n j : ℕ} (hl : 0 < l) (hx : 0 < x)
    (hC : 0 ≤ C) (hr : l * x ≤ r) (ha : |a| ≤ C * x ^ (n + j)) :
    |a / r ^ j| ≤ (C / l ^ j) * x ^ n := by
  have hr0 : 0 < r := (mul_pos hl hx).trans_le hr
  rw [abs_div, abs_of_pos (pow_pos hr0 j)]
  calc
    _ ≤ C * x ^ (n + j) / (l * x) ^ j := by gcongr
    _ = _ := by rw [pow_add, mul_pow]; field_simp

/-- The reconstructed mass ratio has a quadratic center bound from a cubic mass bound.
Its displayed coefficient depends only on the fixed mass and lower optical bounds. -/
theorem abs_mu_le_of_bounds {l K : ℝ} (hl : 0 < l) (hK : 0 ≤ K) (huv : u < v)
    (hr : l * (v - u) ≤ r lam u v) (hm0 : 0 ≤ m e lam hh u v)
    (hm : m e lam hh u v ≤ K * (v - u) ^ 3) :
    |mu e lam hh u v| ≤ (2 * K / l) * (v - u) ^ 2 := by
  have hb : |2 * m e lam hh u v| ≤ (2 * K) * (v - u) ^ (2 + 1) := by
    rw [abs_of_nonneg (mul_nonneg (by norm_num) hm0)]
    exact (mul_le_mul_of_nonneg_left hm (by norm_num)).trans_eq (by ring)
  simpa only [mu, pow_one] using
    abs_div_pow_le_of_order (n := 2) (j := 1) hl (sub_pos.mpr huv) (by positivity) hr hb

/-- An integrable radial coefficient gives an absolutely continuous null derivative
on the entire section, including the axis endpoint. -/
theorem ac_nu_of_integrable
    (hB : IntervalIntegrable (fun s => lam u s / r lam u s * z e lam hh u s) volume u b) :
    AbsolutelyContinuousOnInterval (nu e lam hh u) u b := by
  have hp := hB.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => -lam u u) u b :=
    (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  exact hc.mul_normed_ring hp.exp

/-- Uniqueness of the axis-normalized null derivative among AC solutions of its radial ODE.
Only integrability of the displayed coefficient is needed; in particular the conclusion
also applies whenever the endpoint coefficient is integrable without being continuous. -/
theorem nu_eq_of_ac_of_ae_hasDerivAt {n : ℝ → ℝ}
    (hn : AbsolutelyContinuousOnInterval n u b)
    (hB : IntervalIntegrable (fun s => lam u s / r lam u s * z e lam hh u s) volume u b)
    (hd : ∀ᵐ x, x ∈ uIcc u b → HasDerivAt n
      (n x * (lam u x / r lam u x * z e lam hh u x)) x)
    (haxis : n u = -lam u u) : ∀ v ∈ Icc u b, n v = nu e lam hh u v := by
  let p := fun x => ∫ s in u..x, lam u s / r lam u s * z e lam hh u s
  let w := fun x => Real.exp (-p x)
  have hp := hB.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hw : AbsolutelyContinuousOnInterval w u b := hp.neg.exp
  have hz : ∀ᵐ x, x ∈ uIcc u b → HasDerivAt (fun y => w y * n y) 0 x := by
    filter_upwards [hB.ae_hasDerivAt_integral, hd] with x hx hdx hmem
    have hw' : HasDerivAt w
        (w x * -(lam u x / r lam u x * z e lam hh u x)) x :=
      (hx hmem u left_mem_uIcc).neg.exp
    convert hw'.mul (hdx hmem) using 1
    ring
  obtain ⟨c, hc⟩ := (hw.mul_normed_ring hn).const_of_ae_hasDerivAt_zero hz
  have ha := hc u left_mem_uIcc
  simp only [w, p, intervalIntegral.integral_same, neg_zero, Real.exp_zero, one_mul] at ha
  intro v hv
  have hv' := hc v (Icc_subset_uIcc hv)
  rw [← ha, haxis] at hv'
  have he : Real.exp (p v) * w v = 1 := by
    dsimp only [w]
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hm := congrArg (Real.exp (p v) * ·) hv'
  rw [← mul_assoc, he, one_mul] at hm
  simpa only [p, nu, mul_comm] using hm

end EmcsfAcExtension.Local.Recon
