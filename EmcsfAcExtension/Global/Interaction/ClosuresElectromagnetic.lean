module

public import EmcsfAcExtension.Global.Interaction.RadialZ
import EmcsfAcExtension.Global.Calculus.Sections

/-! # Electromagnetic radial comparison before insertion of the profiles

The expansion ratio is retained until it is bounded by one. The following
helper keeps the literal intermediate integral of `charged_SF_new_version.tex:L3403–L3412`.
Its profile premises are discharged by the stopped-envelope closures.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global

/-- [internal] The full electromagnetic incoming comparison chain. The
positive coefficient depends only on `δ,Cq`, before all solution data.
The source's radial measure is expressed as `dr = λ dv`. -/
theorem ct_z_charge_chain_of_profiles (δ Cq : ℝ) (hδ : 0 < δ) (hCq : 0 ≤ Cq) :
    ∃ C : ℝ, 0 < C ∧ ∀ (e M₀ F c Λ ε : ℝ) (S : Fields) (D : Set (ℝ × ℝ)) (u a b : ℝ),
      IsSolution e S D → ExteriorStops S D δ c Λ F ε → u < a → a ≤ b →
      outSeg u a b ⊆ D → 0 ≤ M₀ → 0 ≤ F →
      (∀ v ∈ Icc a b, ‖S.phi u v‖ ≤ M₀) →
      (∀ v ∈ Icc a b, |S.Q u v| / S.r u v ^ 2 ≤ Cq * |e| * M₀ * F) →
      ‖radialZEM e S u a b‖ ≤ (|e| / δ) *
          (∫ v in a..b, S.lam u v / S.r u v * |S.Q u v| * ‖S.phi u v‖) ∧
        (|e| / δ) *
          (∫ v in a..b, S.lam u v / S.r u v * |S.Q u v| * ‖S.phi u v‖) ≤
          C * e ^ 2 * M₀ ^ 2 * F * S.r u b ^ 2 := by
  refine ⟨Cq / δ + 1, by positivity, ?_⟩
  intro e M₀ F c Λ ε S D u a b hS hstop hua hab hs hM hF hphi hcharge
  let A := Cq * |e| * M₀ * F
  let K := Cq / δ * e ^ 2 * M₀ ^ 2 * F
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have cn := Calculus.continuousOn_out_section hS.cont_nu hs
  have cm := Calculus.continuousOn_out_section hS.cont_m hs
  have cq := Calculus.continuousOn_out_section hS.cont_Q hs
  have cp := Calculus.continuousOn_out_section hS.cont_phi hs
  have hr (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.r u v :=
    hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
  have hl (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.lam u v := hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)
  have hn (v : ℝ) (hv : v ∈ Icc a b) : S.nu u v < 0 := hS.nu_neg (u, v) (hs ⟨rfl, hv⟩)
  have hg (v : ℝ) (hv : v ∈ Icc a b) : δ ≤ 1 - S.mu u v := (hstop (u, v) (hs ⟨rfl, hv⟩)).2.1
  have cg : ContinuousOn (fun v => 1 - S.mu u v) (Icc a b) :=
    continuousOn_const.sub ((continuousOn_const.mul cm).div cr (fun v hv => (hr v hv).ne'))
  have cw := (((cl.div cr (fun v hv => (hr v hv).ne')).mul cq.abs).mul cp.norm)
  have iw := cw.intervalIntegrable_of_Icc hab (μ := volume)
  have csource : ContinuousOn (S.waveSource e u) (Icc a b) := by
    have cc := (((((continuousOn_const : ContinuousOn (fun _ : ℝ => I * (e : ℂ))
      (Icc a b)).mul (Complex.continuous_ofReal.comp_continuousOn cq)).mul cp).mul
        (Complex.continuous_ofReal.comp_continuousOn cn)).mul
          (Complex.continuous_ofReal.comp_continuousOn cl)).div
      ((Complex.continuous_ofReal.comp_continuousOn cg).mul
        (Complex.continuous_ofReal.comp_continuousOn cr)) (fun v hv =>
          mul_ne_zero (Complex.ofReal_ne_zero.mpr (hδ.trans_le (hg v hv)).ne')
            (Complex.ofReal_ne_zero.mpr (hr v hv).ne'))
    apply cc.congr
    intro v _
    simp only [Pi.mul_apply, Pi.div_apply, Function.comp_apply, Fields.waveSource,
      Complex.ofReal_sub, Complex.ofReal_one]
  have iem := csource.intervalIntegrable_of_Icc hab (μ := volume)
  have hratio (v : ℝ) (hv : v ∈ Icc a b) : (-S.nu u v) / (-S.nu u b) ≤ 1 := by
    have hh := (Interaction.radial_expansion_control hS hstop (hua.trans_le hv.1) hv.2
      (fun z hz => hs ⟨hz.1, hv.1.trans hz.2.1, hz.2.2⟩)).2.1
    apply (div_le_one (neg_pos.mpr (hn b ⟨hab, le_rfl⟩))).mpr
    simpa only [one_mul] using (le_div_iff₀ (neg_pos.mpr (hn v hv))).mp hh
  have hpoint (v : ℝ) (hv : v ∈ Icc a b) :
      ‖(S.nu u b : ℂ)⁻¹ * S.waveSource e u v‖ ≤
        (|e| / δ) * (S.lam u v / S.r u v * |S.Q u v| * ‖S.phi u v‖) := by
    have hgp := hδ.trans_le (hg v hv)
    have hgapnorm : ‖(1 - (S.mu u v : ℂ))‖ = 1 - S.mu u v := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hgp]
    have heq : ‖(S.nu u b : ℂ)⁻¹ * S.waveSource e u v‖ =
        ((-S.nu u v) / (-S.nu u b)) *
          (|e| * |S.Q u v| * ‖S.phi u v‖ * S.lam u v / ((1 - S.mu u v) * S.r u v)) := by
      simp only [Fields.waveSource, norm_mul, norm_div, norm_inv, Complex.norm_I,
        one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (hn v hv),
        abs_of_neg (hn b ⟨hab, le_rfl⟩), abs_of_pos (hl v hv), abs_of_pos (hr v hv), hgapnorm]
      field_simp [hgp.ne', (hr v hv).ne']
    rw [heq]
    have hnum : 0 ≤ |e| * |S.Q u v| * ‖S.phi u v‖ * S.lam u v :=
      mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (norm_nonneg _)) (hl v hv).le
    calc
      _ ≤ |e| * |S.Q u v| * ‖S.phi u v‖ * S.lam u v /
          ((1 - S.mu u v) * S.r u v) :=
        mul_le_of_le_one_left (div_nonneg hnum (mul_nonneg hgp.le (hr v hv).le)) (hratio v hv)
      _ ≤ |e| * |S.Q u v| * ‖S.phi u v‖ * S.lam u v / (δ * S.r u v) :=
        div_le_div_of_nonneg_left hnum (mul_pos hδ (hr v hv))
          (mul_le_mul_of_nonneg_right (hg v hv) (hr v hv).le)
      _ = _ := by ring
  constructor
  · rw [radialZEM, ← intervalIntegral.integral_const_mul]
    apply (intervalIntegral.norm_integral_le_integral_norm hab).trans
    have hh := intervalIntegral.integral_mono_on hab
      (iem.const_mul (S.nu u b : ℂ)⁻¹).norm (iw.const_mul (|e| / δ)) hpoint
    simpa only [intervalIntegral.integral_const_mul, Pi.mul_apply, Pi.div_apply,
      Function.comp_apply] using hh
  · have hpoint' (v : ℝ) (hv : v ∈ Icc a b) :
        (|e| / δ) * (S.lam u v / S.r u v * |S.Q u v| * ‖S.phi u v‖) ≤
          K * (S.lam u v * S.r u v) := by
      have hq : |S.Q u v| ≤ A * S.r u v ^ 2 :=
        (div_le_iff₀ (sq_pos_of_pos (hr v hv))).mp (hcharge v hv)
      have hqp := mul_le_mul hq (hphi v hv) (norm_nonneg _)
        (mul_nonneg hA (sq_nonneg _))
      calc
        _ = (|e| / δ * (S.lam u v / S.r u v)) * (|S.Q u v| * ‖S.phi u v‖) := by ring
        _ ≤ (|e| / δ * (S.lam u v / S.r u v)) * (A * S.r u v ^ 2 * M₀) :=
          mul_le_mul_of_nonneg_left hqp
            (mul_nonneg (div_nonneg (abs_nonneg _) hδ.le)
              (div_nonneg (hl v hv).le (hr v hv).le))
        _ = _ := by dsimp [K, A]; rw [← sq_abs e]; field_simp [hδ.ne', (hr v hv).ne']
    have im := (cl.mul cr).intervalIntegrable_of_Icc hab (μ := volume)
    have hi := intervalIntegral.integral_mono_on hab (iw.const_mul (|e| / δ))
      (im.const_mul K) hpoint'
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
    dsimp only [Pi.mul_apply, Pi.div_apply, Function.comp_apply] at hi
    have hmom := Interaction.radial_moment hS hua hab hs 1
    norm_num only [pow_one, Nat.reduceAdd, Nat.cast_one] at hmom
    rw [hmom] at hi
    have hsmall : (S.r u b ^ 2 - S.r u a ^ 2) / 2 ≤ S.r u b ^ 2 := by
      nlinarith only [sq_nonneg (S.r u a), sq_nonneg (S.r u b)]
    have hh := mul_le_mul_of_nonneg_left hsmall hK
    have hpos : 0 ≤ e ^ 2 * M₀ ^ 2 * F * S.r u b ^ 2 := by positivity
    dsimp [K] at hi hh
    nlinarith only [hi, hh, hpos]

end EmcsfAcExtension.Global
