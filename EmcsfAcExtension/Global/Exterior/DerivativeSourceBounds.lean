module

public import EmcsfAcExtension.Global.Exterior.Charge
import EmcsfAcExtension.Infra.AC.Variation

/-! # Charged source estimates on outgoing exterior rows

Radial integrals are written in the original outgoing label, with Jacobian
`λ`. The energy and reciprocal-radius moments come from the frozen
characteristic equations. All displayed constants are numerical and uniform
in the solution, coupling, radius and outgoing row.
Source: `charged_SF_new_version.tex:L1313–L1325`, approved internal project record (S2)–(S4).
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
Weighted Cauchy–Schwarz for continuous functions and a nonnegative
continuous weight. The coefficient is `1`, independent of all inputs. -/
theorem weighted_integral_cauchy_schwarz {a b : ℝ} (hab : a ≤ b)
    {f g w : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hg : ContinuousOn g (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hw0 : ∀ v ∈ Icc a b, 0 ≤ w v) :
    (∫ v in a..b, f v * g v * w v) ^ 2 ≤
      (∫ v in a..b, f v ^ 2 * w v) * (∫ v in a..b, g v ^ 2 * w v) := by
  have h := integral_cauchy_schwarz hab (hf.mul hw.sqrt) (hg.mul hw.sqrt)
  dsimp only [Pi.mul_apply] at h
  have hfg : (∫ v in a..b, (f v * Real.sqrt (w v)) * (g v * Real.sqrt (w v))) =
      ∫ v in a..b, f v * g v * w v := by
    apply intervalIntegral.integral_congr
    intro v hv
    have hv' : v ∈ Icc a b := by simpa only [uIcc_of_le hab] using hv
    calc
      _ = f v * g v * (Real.sqrt (w v)) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (hw0 v hv')]
  have hff : (∫ v in a..b, (f v * Real.sqrt (w v)) ^ 2) =
      ∫ v in a..b, f v ^ 2 * w v := by
    apply intervalIntegral.integral_congr
    intro v hv
    have hv' : v ∈ Icc a b := by simpa only [uIcc_of_le hab] using hv
    change (f v * Real.sqrt (w v)) ^ 2 = f v ^ 2 * w v
    rw [mul_pow, Real.sq_sqrt (hw0 v hv')]
  have hgg : (∫ v in a..b, (g v * Real.sqrt (w v)) ^ 2) =
      ∫ v in a..b, g v ^ 2 * w v := by
    apply intervalIntegral.integral_congr
    intro v hv
    have hv' : v ∈ Icc a b := by simpa only [uIcc_of_le hab] using hv
    change (g v * Real.sqrt (w v)) ^ 2 = g v ^ 2 * w v
    rw [mul_pow, Real.sq_sqrt (hw0 v hv')]
  rwa [hfg, hff, hgg] at h

variable {ui e : ℝ} {S : Fields}

/-- [internal]
The outgoing scalar's absolute radial integral is bounded by `2 sqrt(M R)`.
The coefficient `2` is universal. The late gap premise supplies scalar
energy and is discharged by the terminal exterior consumer. -/
theorem integral_outgoing_field_le_of_gap (h : OriginalData ui e S) {u a : ℝ}
    (hua : u < a) (ha : a ≤ 0) (hs : outSeg u a 0 ⊆ origDomain ui)
    (hg : ∀ v ∈ Icc a 0, 1 / 2 ≤ 1 - S.mu u v) :
    (∫ v in a..0, ‖S.theta u v / (S.lam u v : ℂ)‖ * S.lam u v) ≤
      2 * Real.sqrt (terminalMass S u * terminalRadius S u) := by
  have hr := h.solution.r_pos (u, a) (hs ⟨rfl, le_rfl, ha⟩) hua
  have hl (v : ℝ) (hv : v ∈ Icc a 0) :=
    h.solution.lam_pos (u, v) (hs ⟨rfl, hv⟩)
  have cl := Calculus.continuousOn_out_section h.solution.cont_lam hs
  have cF := ((Calculus.continuousOn_out_section h.solution.cont_theta hs).div
    (Complex.continuous_ofReal.comp_continuousOn cl)
    (fun v hv => Complex.ofReal_ne_zero.mpr (hl v hv).ne')).norm
  have hcs := weighted_integral_cauchy_schwarz ha cF
    (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Icc a 0)) cl
    (fun v hv => (hl v hv).le)
  simp only [mul_one, one_pow, one_mul] at hcs
  have hrad := (h.solution.eq_out u a 0 hua ha hs).1
  have he := scalar_energy_le_of_gap h hua ha hs hg
  have hM := mass_nonneg h (hs ⟨rfl, ha, le_rfl⟩)
  have hR := h.solution.r_pos (u, 0) (hs ⟨rfl, ha, le_rfl⟩) (hua.trans_le ha)
  have hw0 := intervalIntegral.integral_nonneg (μ := volume) ha (fun v hv => (hl v hv).le)
  have hprod := mul_le_mul he (show (∫ v in a..0, S.lam u v) ≤ terminalRadius S u by
    rw [← hrad.2]; dsimp [terminalRadius]; linarith only [hr]) hw0 (by positivity)
  have hsqrt := Real.sq_sqrt (mul_nonneg hM hR.le)
  have hsq := hcs.trans hprod
  dsimp only [Pi.div_apply, Function.comp_apply, terminalMass, terminalRadius] at hsq hsqrt ⊢
  nlinarith only [hsq, hsqrt, Real.sqrt_nonneg (S.m u 0 * S.r u 0)]

/-- [internal]
The quadratic-coupling source is bounded by `2 e² L² sqrt(M R)`.
The coefficient `2` is numerical, uniformly in all data and scales. The
scalar envelope and late gap are explicit intermediate inputs; they are
proved by the terminal exterior estimates. No outgoing derivative occurs. -/
theorem source_quadratic_coupling_bound_of_gap (h : OriginalData ui e S)
    {u a L : ℝ} (hua : u < a) (ha : a ≤ 0)
    (hs : outSeg u a 0 ⊆ origDomain ui)
    (hg : ∀ v ∈ Icc a 0, 1 / 2 ≤ 1 - S.mu u v)
    (hphi : ∀ v ∈ Icc a 0, ‖S.phi u v‖ ≤ L) :
    (∫ v in a..0, e ^ 2 * ‖S.phi u v‖ ^ 2 *
      ‖S.theta u v / (S.lam u v : ℂ)‖ * S.lam u v) ≤
      2 * e ^ 2 * L ^ 2 * Real.sqrt (terminalMass S u * terminalRadius S u) := by
  have hl (v : ℝ) (hv : v ∈ Icc a 0) :=
    h.solution.lam_pos (u, v) (hs ⟨rfl, hv⟩)
  have cl := Calculus.continuousOn_out_section h.solution.cont_lam hs
  have cF := ((Calculus.continuousOn_out_section h.solution.cont_theta hs).div
    (Complex.continuous_ofReal.comp_continuousOn cl)
    (fun v hv => Complex.ofReal_ne_zero.mpr (hl v hv).ne')).norm
  have cp := (Calculus.continuousOn_out_section h.solution.cont_phi hs).norm
  have hpoint (v : ℝ) (hv : v ∈ Icc a 0) :
      e ^ 2 * ‖S.phi u v‖ ^ 2 * ‖S.theta u v / (S.lam u v : ℂ)‖ * S.lam u v ≤
        (e ^ 2 * L ^ 2) * (‖S.theta u v / (S.lam u v : ℂ)‖ * S.lam u v) := by
    have hsq := pow_le_pow_left₀ (norm_nonneg (S.phi u v)) (hphi v hv) 2
    have hh := mul_le_mul_of_nonneg_left hsq (sq_nonneg e)
    have hh' := mul_le_mul_of_nonneg_right hh
      (mul_nonneg (norm_nonneg (S.theta u v / (S.lam u v : ℂ))) (hl v hv).le)
    simpa only [mul_assoc] using hh'
  have hi := ((((cp.pow 2).const_mul (e ^ 2)).mul cF).mul cl).intervalIntegrable_of_Icc
    (μ := volume) ha
  have hj := ((cF.mul cl).const_mul (e ^ 2 * L ^ 2)).intervalIntegrable_of_Icc
    (μ := volume) ha
  calc
    _ ≤ ∫ v in a..0, (e ^ 2 * L ^ 2) *
        (‖S.theta u v / (S.lam u v : ℂ)‖ * S.lam u v) :=
      intervalIntegral.integral_mono_on ha hi hj hpoint
    _ = (e ^ 2 * L ^ 2) * ∫ v in a..0,
        ‖S.theta u v / (S.lam u v : ℂ)‖ * S.lam u v :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (integral_outgoing_field_le_of_gap h hua ha hs hg)
        (mul_nonneg (sq_nonneg e) (sq_nonneg L))
      convert hh using 1
      ring

/-- [internal]
The scalar-charge source is bounded by `2 |e| L sqrt(M/ell)`.
The numerical coefficient `2` is uniform in the solution, coupling, row
and scalar envelope. This uses the electromagnetic mass energy, so requires
no pointwise charge bound. The envelope is supplied by the terminal consumer. -/
theorem source_scalar_charge_bound_of_envelope (h : OriginalData ui e S)
    {u a L : ℝ} (hua : u < a) (ha : a ≤ 0)
    (hs : outSeg u a 0 ⊆ origDomain ui)
    (hphi : ∀ v ∈ Icc a 0, ‖S.phi u v‖ ≤ L) :
    (∫ v in a..0, |e| * |S.Q u v| * ‖S.phi u v‖ / S.r u v ^ 2 * S.lam u v) ≤
      2 * |e| * L * Real.sqrt (terminalMass S u / S.r u a) := by
  have hr (v : ℝ) (hv : v ∈ Icc a 0) :=
    h.solution.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
  have hl (v : ℝ) (hv : v ∈ Icc a 0) :=
    h.solution.lam_pos (u, v) (hs ⟨rfl, hv⟩)
  have cr := Calculus.continuousOn_out_section h.solution.cont_r hs
  have cl := Calculus.continuousOn_out_section h.solution.cont_lam hs
  have cq := (Calculus.continuousOn_out_section h.solution.cont_Q hs).abs
  have cp := (Calculus.continuousOn_out_section h.solution.cont_phi hs).norm
  let f : ℝ → ℝ := fun v => |S.Q u v| / S.r u v
  let g : ℝ → ℝ := fun v => (S.r u v)⁻¹
  have cf : ContinuousOn f (Icc a 0) := cq.div cr (fun v hv => (hr v hv).ne')
  have cg : ContinuousOn g (Icc a 0) := cr.inv₀ (fun v hv => (hr v hv).ne')
  have hc := weighted_integral_cauchy_schwarz ha cf cg cl (fun v hv => (hl v hv).le)
  have he : (∫ v in a..0, f v ^ 2 * S.lam u v) ≤ 2 * terminalMass S u := by
    simpa only [f, div_pow, sq_abs] using electromagnetic_energy_le h hua ha le_rfl hs
  have hm : (∫ v in a..0, g v ^ 2 * S.lam u v) ≤ (S.r u a)⁻¹ := by
    have heq : (∫ v in a..0, g v ^ 2 * S.lam u v) =
        ∫ v in a..0, S.lam u v / S.r u v ^ 2 := by
      apply intervalIntegral.integral_congr
      intro v _
      simp only [g, inv_pow, div_eq_mul_inv, mul_comm]
    rw [heq, inverse_radius_moment h hua ha hs]
    exact sub_le_self _ (inv_nonneg.mpr (hr 0 ⟨ha, le_rfl⟩).le)
  have hM := mass_nonneg h (hs ⟨rfl, ha, le_rfl⟩)
  have hgn := intervalIntegral.integral_nonneg (μ := volume) ha
    (fun v hv => mul_nonneg (sq_nonneg (g v)) (hl v hv).le)
  have hprod := mul_le_mul he hm hgn (by positivity)
  have hsqrt := Real.sq_sqrt (div_nonneg hM (hr a ⟨le_rfl, ha⟩).le)
  have hsmall : (∫ v in a..0, f v * g v * S.lam u v) ≤
      2 * Real.sqrt (terminalMass S u / S.r u a) := by
    have hh := hc.trans hprod
    have hh' : (∫ v in a..0, f v * g v * S.lam u v) ^ 2 ≤
        2 * (terminalMass S u / S.r u a) := by
      simpa only [div_eq_mul_inv, mul_assoc] using hh
    dsimp only [terminalMass] at hh' hsqrt ⊢
    nlinarith only [hh', hsqrt, Real.sqrt_nonneg (S.m u 0 / S.r u a)]
  have hL : 0 ≤ L := (norm_nonneg _).trans (hphi a ⟨le_rfl, ha⟩)
  have hi := ((((cq.const_mul |e|).mul cp).div (cr.pow 2)
    (fun v hv => pow_ne_zero _ (hr v hv).ne')).mul cl).intervalIntegrable_of_Icc
    (μ := volume) ha
  have hj := (((cf.mul cg).mul cl).const_mul (|e| * L)).intervalIntegrable_of_Icc
    (μ := volume) ha
  calc
    _ ≤ ∫ v in a..0, (|e| * L) * (f v * g v * S.lam u v) := by
      apply intervalIntegral.integral_mono_on ha hi hj
      intro v hv
      have hh := mul_le_mul_of_nonneg_left (hphi v hv)
        (div_nonneg (mul_nonneg (abs_nonneg e) (abs_nonneg (S.Q u v))) (sq_nonneg (S.r u v)))
      have hh' := mul_le_mul_of_nonneg_right hh (hl v hv).le
      convert hh' using 1 <;> dsimp [f, g] <;> field_simp [(hr v hv).ne']
    _ = (|e| * L) * ∫ v in a..0, f v * g v * S.lam u v :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hsmall (mul_nonneg (abs_nonneg e) hL)
      convert hh using 1
      ring

/-- [internal]
The linear-charge source is at most `4 |e| M/ell`. The numerical constant
`4` is uniform in all data and scales. The electromagnetic and scalar
mass energies are proved from the original solution; only the late gap is
an explicit intermediate input. -/
theorem source_linear_charge_bound_of_gap (h : OriginalData ui e S)
    {u a : ℝ} (hua : u < a) (ha : a ≤ 0)
    (hs : outSeg u a 0 ⊆ origDomain ui)
    (hg : ∀ v ∈ Icc a 0, 1 / 2 ≤ 1 - S.mu u v) :
    (∫ v in a..0, |e| * |S.Q u v| / S.r u v ^ 2 *
      ‖S.theta u v / (S.lam u v : ℂ)‖ * S.lam u v) ≤
      4 * |e| * (terminalMass S u / S.r u a) := by
  have hr (v : ℝ) (hv : v ∈ Icc a 0) :=
    h.solution.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
  have hl (v : ℝ) (hv : v ∈ Icc a 0) :=
    h.solution.lam_pos (u, v) (hs ⟨rfl, hv⟩)
  have cr := Calculus.continuousOn_out_section h.solution.cont_r hs
  have cl := Calculus.continuousOn_out_section h.solution.cont_lam hs
  have cq := (Calculus.continuousOn_out_section h.solution.cont_Q hs).abs
  have cF := ((Calculus.continuousOn_out_section h.solution.cont_theta hs).div
    (Complex.continuous_ofReal.comp_continuousOn cl)
    (fun v hv => Complex.ofReal_ne_zero.mpr (hl v hv).ne')).norm
  let f : ℝ → ℝ := fun v => |S.Q u v| / S.r u v
  let g : ℝ → ℝ := fun v => ‖S.theta u v / (S.lam u v : ℂ)‖ / S.r u v
  have cf : ContinuousOn f (Icc a 0) := cq.div cr (fun v hv => (hr v hv).ne')
  have cg : ContinuousOn g (Icc a 0) := cF.div cr (fun v hv => (hr v hv).ne')
  have hc := weighted_integral_cauchy_schwarz ha cf cg cl (fun v hv => (hl v hv).le)
  have he : (∫ v in a..0, f v ^ 2 * S.lam u v) ≤ 2 * terminalMass S u := by
    simpa only [f, div_pow, sq_abs] using electromagnetic_energy_le h hua ha le_rfl hs
  have hrl (v : ℝ) (hv : v ∈ Icc a 0) : S.r u a ≤ S.r u v :=
    outgoing_radius_mono h hua.le hv.1
      (fun _ hx => hs (outSeg_subset_outSeg le_rfl hv.2 hx))
  have hgb : (∫ v in a..0, g v ^ 2 * S.lam u v) ≤
      (4 * terminalMass S u) / S.r u a ^ 2 := by
    have hi := ((cg.pow 2).mul cl).intervalIntegrable_of_Icc (μ := volume) ha
    have hj := (((cF.pow 2).mul cl).div_const (S.r u a ^ 2)).intervalIntegrable_of_Icc
      (μ := volume) ha
    calc
      _ ≤ ∫ v in a..0, ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v /
          S.r u a ^ 2 := by
        apply intervalIntegral.integral_mono_on ha hi hj
        intro v hv
        dsimp [g]
        rw [div_pow, div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_left
          (mul_nonneg (sq_nonneg _) (hl v hv).le) (sq_pos_of_pos (hr a ⟨le_rfl, ha⟩))
          (pow_le_pow_left₀ (hr a ⟨le_rfl, ha⟩).le (hrl v hv) 2)
      _ = (∫ v in a..0, ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v) /
          S.r u a ^ 2 := intervalIntegral.integral_div _ _
      _ ≤ _ := div_le_div_of_nonneg_right (scalar_energy_le_of_gap h hua ha hs hg)
        (sq_nonneg _)
  have hM := mass_nonneg h (hs ⟨rfl, ha, le_rfl⟩)
  have hgn := intervalIntegral.integral_nonneg (μ := volume) ha
    (fun v hv => mul_nonneg (sq_nonneg (g v)) (hl v hv).le)
  have hprod := mul_le_mul he hgb hgn (by positivity)
  have hsq := hc.trans hprod
  have hid : (2 * terminalMass S u) * (4 * terminalMass S u / S.r u a ^ 2) =
      8 * (terminalMass S u / S.r u a) ^ 2 := by ring
  rw [hid] at hsq
  have hX : 0 ≤ terminalMass S u / S.r u a := div_nonneg hM (hr a ⟨le_rfl, ha⟩).le
  have hsmall : (∫ v in a..0, f v * g v * S.lam u v) ≤
      4 * (terminalMass S u / S.r u a) := by nlinarith only [hsq, hX]
  have heq : (∫ v in a..0, |e| * |S.Q u v| / S.r u v ^ 2 *
      ‖S.theta u v / (S.lam u v : ℂ)‖ * S.lam u v) =
      |e| * ∫ v in a..0, f v * g v * S.lam u v := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v _
    dsimp [f, g]
    ring
  rw [heq]
  have hh := mul_le_mul_of_nonneg_left hsmall (abs_nonneg e)
  convert hh using 1
  ring

/-- [internal]
The pointwise charge comparison bounds `|Q|/r` on an exterior row by
`8 sqrt(M/ell)`. Its numerical coefficient is uniform. -/
theorem charge_div_radius_le_of_pointwise {Q M r ell : ℝ}
    (hell : 0 < ell) (hr : ell ≤ r) (hM : 0 ≤ M)
    (hQ : Q ^ 2 / r ^ 2 ≤ 64 * (M / r)) :
    |Q| / r ≤ 8 * Real.sqrt (M / ell) := by
  have hrp := hell.trans_le hr
  have hratio := div_le_div_of_nonneg_left hM hell hr
  have hsq : (|Q| / r) ^ 2 ≤ 64 * (M / ell) := by
    rw [div_pow, sq_abs]
    exact hQ.trans (mul_le_mul_of_nonneg_left hratio (by norm_num))
  have hsqrt := Real.sq_sqrt (div_nonneg hM hell.le)
  nlinarith only [hsq, hsqrt, Real.sqrt_nonneg (M / ell)]

/-- [internal]
The cubic-charge source is bounded by `32 |e| L (M/ell) sqrt(M/ell)`,
the literal `M^(3/2) ell^(-3/2)` bound of the source. The coefficient `32`
is numerical and uniform in all data. Its pointwise charge and scalar
inputs are precisely the estimates supplied by internal project record. -/
theorem source_cubic_charge_bound_of_profiles (h : OriginalData ui e S)
    {u a L : ℝ} (hua : u < a) (ha : a ≤ 0)
    (hs : outSeg u a 0 ⊆ origDomain ui)
    (hg : ∀ v ∈ Icc a 0, 1 / 2 ≤ 1 - S.mu u v)
    (hphi : ∀ v ∈ Icc a 0, ‖S.phi u v‖ ≤ L)
    (hQ : ∀ v ∈ Icc a 0, S.Q u v ^ 2 / S.r u v ^ 2 ≤
      64 * (terminalMass S u / S.r u v)) :
    (∫ v in a..0, |e| * |S.Q u v| * ‖S.phi u v‖ / S.r u v ^ 2 *
      ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v) ≤
      32 * |e| * L * (terminalMass S u / S.r u a) *
        Real.sqrt (terminalMass S u / S.r u a) := by
  have hr (v : ℝ) (hv : v ∈ Icc a 0) :=
    h.solution.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
  have hl (v : ℝ) (hv : v ∈ Icc a 0) :=
    h.solution.lam_pos (u, v) (hs ⟨rfl, hv⟩)
  have cr := Calculus.continuousOn_out_section h.solution.cont_r hs
  have cl := Calculus.continuousOn_out_section h.solution.cont_lam hs
  have cq := (Calculus.continuousOn_out_section h.solution.cont_Q hs).abs
  have cp := (Calculus.continuousOn_out_section h.solution.cont_phi hs).norm
  have cF := ((Calculus.continuousOn_out_section h.solution.cont_theta hs).div
    (Complex.continuous_ofReal.comp_continuousOn cl)
    (fun v hv => Complex.ofReal_ne_zero.mpr (hl v hv).ne')).norm
  have hM := mass_nonneg h (hs ⟨rfl, ha, le_rfl⟩)
  have hL : 0 ≤ L := (norm_nonneg _).trans (hphi a ⟨le_rfl, ha⟩)
  let K := 8 * |e| * L * Real.sqrt (terminalMass S u / S.r u a) / S.r u a
  have hK : 0 ≤ K := by
    dsimp [K]
    exact div_nonneg (by positivity) (hr a ⟨le_rfl, ha⟩).le
  have hb (v : ℝ) (hv : v ∈ Icc a 0) :
      |e| * |S.Q u v| * ‖S.phi u v‖ / S.r u v ^ 2 ≤ K := by
    have hrl : S.r u a ≤ S.r u v := outgoing_radius_mono h hua.le hv.1
      (fun _ hx => hs (outSeg_subset_outSeg le_rfl hv.2 hx))
    have hq := charge_div_radius_le_of_pointwise (hr a ⟨le_rfl, ha⟩) hrl hM (hQ v hv)
    have hp := mul_le_mul (hphi v hv) hq
      (div_nonneg (abs_nonneg _) (hr v hv).le) hL
    have hdiv := div_le_div_of_nonneg_left (by positivity :
      0 ≤ L * (8 * Real.sqrt (terminalMass S u / S.r u a))) (hr a ⟨le_rfl, ha⟩) hrl
    have hp' := div_le_div_of_nonneg_right hp (hr v hv).le
    have he := mul_le_mul_of_nonneg_left (hp'.trans hdiv) (abs_nonneg e)
    convert he using 1 <;> dsimp [K] <;> ring
  have hi := (((((cq.const_mul |e|).mul cp).div (cr.pow 2)
    (fun v hv => pow_ne_zero _ (hr v hv).ne')).mul (cF.pow 2)).mul cl).intervalIntegrable_of_Icc
    (μ := volume) ha
  have hj := (((cF.pow 2).mul cl).const_mul K).intervalIntegrable_of_Icc (μ := volume) ha
  calc
    _ ≤ ∫ v in a..0, K * (‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v) := by
      apply intervalIntegral.integral_mono_on ha hi hj
      intro v hv
      have hh := mul_le_mul_of_nonneg_right (hb v hv)
        (mul_nonneg (sq_nonneg ‖S.theta u v / (S.lam u v : ℂ)‖) (hl v hv).le)
      simpa only [Pi.mul_apply, Pi.div_apply, Pi.pow_apply, Function.comp_apply, mul_assoc] using hh
    _ = K * ∫ v in a..0, ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (scalar_energy_le_of_gap h hua ha hs hg) hK
      convert hh using 1
      dsimp [K]
      ring

end EmcsfAcExtension.Global.Exterior
