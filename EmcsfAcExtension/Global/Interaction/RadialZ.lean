module

public import EmcsfAcExtension.Global.Interaction.RadialY
import EmcsfAcExtension.Infra.PowerKernel
import EmcsfAcExtension.Global.Calculus.Sections
import EmcsfAcExtension.Local.Calculus.Reconstruction
import EmcsfAcExtension.Infra.Triangle

/-! # Finite separation in the incoming radial reconstruction

The power kernel retains the factor `r - x` before any label integration.
Source: `charged_SF_new_version.tex:L3396–L3403`; internal project record, auxiliary
reconstructions.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Interaction

/-- [node sec:charged-terminal-interaction#finite-separation-radial-kernel]
Exact finite radial kernel and its separation bound, charged_SF_new_version.tex:L3396–L3403.
The coefficient is exactly `1 / p`, where `p = 1 - F²`; it is uniform in
both positive radial endpoints. -/
theorem finite_separation_radial_kernel {p x r : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) (hx : 0 < x) (hxr : x ≤ r) :
    (∫ s in x..r, (x / s) ^ p / s) = (1 - (x / r) ^ p) / p ∧
      (1 - (x / r) ^ p) / p ≤ (r - x) / (p * r) := by
  have hr : 0 < r := hx.trans_le hxr
  have heq : (∫ s in x..r, (x / s) ^ p / s) =
      ∫ s in x..r, orderedPowerKernel p 0 x s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hxr] at hs
    have hsp : 0 < s := hx.trans_le hs.1
    dsimp [orderedPowerKernel]
    rw [sub_zero, sub_zero, Real.div_rpow hx.le hsp.le,
      Real.rpow_add hsp 1 p, Real.rpow_one]
    ring
  constructor
  · rw [heq, integral_orderedPowerKernel_eq hp hx hxr]
    simp only [sub_zero]
    rw [Real.div_rpow hx.le hr.le, Real.rpow_neg hr.le, div_eq_mul_inv]
    ring
  · have hpow := Real.self_le_rpow_of_le_one (div_nonneg hx.le hr.le)
      ((div_le_one hr).mpr hxr) hp1
    calc
      _ ≤ (1 - x / r) / p := div_le_div_of_nonneg_right (by linarith only [hpow]) hp.le
      _ = _ := by field_simp

private theorem radial_power_tail_le {e p : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) (hp : 0 < p) (hp1 : p ≤ 1) :
    S.r u a ^ p * (∫ v in a..b, S.lam u v / S.r u v ^ (1 + p)) ≤
      (S.r u b - S.r u a) / (p * S.r u b) := by
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have hr (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.r u v :=
    hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
  have hdr (v : ℝ) (hv : v ∈ Ioo a b) : HasDerivAt (S.r u) (S.lam u v) v := by
    apply Local.hasDerivAt_of_integralForm_interior hv (cl.mono Ioo_subset_Icc_self)
    intro c d hac hcd hdb
    exact (hS.eq_out u c d (hua.trans hac) hcd (fun q hq =>
      hs ⟨hq.1, hac.le.trans hq.2.1, hq.2.2.trans hdb.le⟩)).1
  have cpow := cr.rpow_const (fun v hv => Or.inl (hr v hv).ne') (p := 1 + p)
  have ig := (cl.div cpow (fun v hv => (Real.rpow_pos_of_pos (hr v hv) _).ne'))
    |>.intervalIntegrable_of_Icc hab (μ := volume)
  have cf : ContinuousOn (fun v => -(S.r u v ^ (-p)) / p) (Icc a b) :=
    ((cr.rpow_const (fun v hv => Or.inl (hr v hv).ne')).neg).div_const p
  have heval := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab cf
    (f' := fun v => S.lam u v / S.r u v ^ (1 + p)) (fun v hv => ?_) ig
  · have heq : S.r u a ^ p * (∫ v in a..b, S.lam u v / S.r u v ^ (1 + p)) =
        (1 - (S.r u a / S.r u b) ^ p) / p := by
      rw [heval]
      rw [Real.div_rpow (hr a ⟨le_rfl, hab⟩).le (hr b ⟨hab, le_rfl⟩).le,
        Real.rpow_neg (hr a ⟨le_rfl, hab⟩).le, Real.rpow_neg (hr b ⟨hab, le_rfl⟩).le]
      field_simp [(Real.rpow_pos_of_pos (hr a ⟨le_rfl, hab⟩) p).ne',
        (Real.rpow_pos_of_pos (hr b ⟨hab, le_rfl⟩) p).ne', hp.ne']
      ring
    rw [heq]
    have hrad : S.r u a ≤ S.r u b := by
      have h := intervalIntegral.integral_nonneg hab (μ := volume) (fun v hv =>
        (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)).le)
      rw [← (hS.eq_out u a b hua hab hs).1.2] at h
      exact sub_nonneg.mp h
    exact (finite_separation_radial_kernel hp hp1 (hr a ⟨le_rfl, hab⟩) hrad).2
  · have hd : HasDerivAt (fun v => -(S.r u v ^ (-p)) / p)
        (-(S.lam u v * (-p) * S.r u v ^ (-p - 1)) / p) v := by
      simpa only [Pi.neg_apply] using!
        (((hdr v hv).rpow_const (p := -p) (Or.inl (hr v ⟨hv.1.le, hv.2.le⟩).ne')).neg).div_const p
    apply hd.congr_deriv
    rw [show -p - 1 = -(1 + p) by ring, Real.rpow_neg (hr v ⟨hv.1.le, hv.2.le⟩).le]
    field_simp [hp.ne']

/-- [internal]
The source radial double integral retains finite endpoint separation.
The coefficient is exactly `1 / p`, uniformly in the row and nonnegative
integrable source. Fubini applies to a product of two integrable factors. -/
theorem radial_source_kernel {e p : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) (hp : 0 < p) (hp1 : p ≤ 1)
    (q : ℝ → ℝ) (iq : IntervalIntegrable q volume a b)
    (hq : ∀ v ∈ Icc a b, 0 ≤ q v) :
    (∫ v in a..b, S.lam u v / S.r u v *
      (∫ x in a..v, (S.r u x / S.r u v) ^ p * q x)) ≤
      p⁻¹ * ∫ x in a..b, (S.r u b - S.r u x) / S.r u b * q x := by
  let f := fun x => S.r u x ^ p * q x
  let g := fun x => S.lam u x / S.r u x ^ (1 + p)
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have hr (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.r u v :=
    hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
  have cf := cr.rpow_const (p := p) (fun v hv => Or.inl (hr v hv).ne')
  have cg : ContinuousOn g (Icc a b) := cl.div
    (cr.rpow_const (fun v hv => Or.inl (hr v hv).ne'))
    (fun v hv => (Real.rpow_pos_of_pos (hr v hv) _).ne')
  have ifunc : IntervalIntegrable f volume a b :=
    iq.continuousOn_mul (by simpa only [uIcc_of_le hab] using cf)
  have ig := cg.intervalIntegrable_of_Icc hab (μ := volume)
  have hrect : IntegrableOn (fun z : ℝ × ℝ => f z.1 * g z.2)
      (Icc a b ×ˢ Icc a b) (volume.prod volume) := by
    rw [IntegrableOn, ← Measure.prod_restrict]
    exact ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp ifunc).mul_prod
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp ig)
  have htri := hrect.mono_set (show triangle a b ⊆ Icc a b ×ˢ Icc a b from
    fun z hz => ⟨⟨hz.1, hz.2.1.trans hz.2.2⟩, ⟨hz.1.trans hz.2.1, hz.2.2⟩⟩)
  have hswap := integral_integral_swap_triangle hab htri
  have heq : (∫ v in a..b, S.lam u v / S.r u v *
      (∫ x in a..v, (S.r u x / S.r u v) ^ p * q x)) =
      ∫ x in a..b, f x * (∫ v in x..b, g v) := by
    calc
      _ = ∫ v in a..b, ∫ x in a..v, f x * g v := by
        apply intervalIntegral.integral_congr
        intro v hv
        dsimp only
        rw [uIcc_of_le hab] at hv
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro x hx
        dsimp only
        rw [uIcc_of_le hv.1] at hx
        dsimp [f, g]
        rw [Real.div_rpow (hr x ⟨hx.1, hx.2.trans hv.2⟩).le (hr v hv).le,
          Real.rpow_add (hr v hv) 1 p, Real.rpow_one]
        ring
      _ = ∫ x in a..b, ∫ v in x..b, f x * g v := hswap.symm
      _ = _ := by simp only [intervalIntegral.integral_const_mul]
  have ct : ContinuousOn (fun x => ∫ v in x..b, g v) (Icc a b) := by
    have cp : ContinuousOn (fun x => ∫ v in a..x, g v) (Icc a b) := by
      simpa only [uIcc_of_le hab] using
        (ig.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).continuousOn
    have ct₀ : ContinuousOn (fun x => (∫ v in a..b, g v) - ∫ v in a..x, g v) (Icc a b) :=
      continuousOn_const.sub cp
    apply ct₀.congr
    intro x hx
    exact (intervalIntegral.integral_interval_sub_left ig
      (ig.mono_set (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc hx)))).symm
  have itail : IntervalIntegrable (fun x => f x * (∫ v in x..b, g v)) volume a b := by
    apply (ifunc.continuousOn_mul (by simpa only [uIcc_of_le hab] using ct)).congr
    intro x _
    change (∫ v in x..b, g v) * f x = f x * (∫ v in x..b, g v)
    ring
  have cweight : ContinuousOn (fun x => (S.r u b - S.r u x) / S.r u b) (Icc a b) := by
    simpa only [Pi.sub_apply] using! (continuousOn_const.sub cr).div_const (S.r u b)
  have iweight : IntervalIntegrable (fun x => (S.r u b - S.r u x) / S.r u b * q x) volume a b := by
    exact iq.continuousOn_mul (by simpa only [uIcc_of_le hab] using cweight)
  rw [heq, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hab itail (iweight.const_mul p⁻¹)
  intro x hx
  change f x * (∫ v in x..b, g v) ≤ p⁻¹ * ((S.r u b - S.r u x) / S.r u b * q x)
  have hker := radial_power_tail_le hS (hua.trans_le hx.1) hx.2
    (fun z hz => hs ⟨hz.1, hx.1.trans hz.2.1, hz.2.2⟩) hp hp1
  have hh := mul_le_mul_of_nonneg_right hker (hq x hx)
  dsimp only [f, g]
  convert hh using 1 <;> ring

end EmcsfAcExtension.Global.Interaction

namespace EmcsfAcExtension.Global

/-- [internal]
Selected incoming boundary piece, retaining the expansion ratio that is
needed in the later source estimates. -/
@[expose] noncomputable def radialZBoundary (S : Fields) (u a b : ℝ) : ℂ :=
  ((S.nu u a / S.nu u b : ℝ) : ℂ) * (S.xi u a / S.nu u a) -
    (S.nu u b : ℂ)⁻¹ * ∫ v in a..b,
      ((S.nu u v * S.lam u v / S.r u v : ℝ) : ℂ) * radialYBoundary S u a v

/-- [internal] Selected incoming derivative-source piece. -/
@[expose] noncomputable def radialZSource (S : Fields) (u a b : ℝ) : ℂ :=
  -(S.nu u b : ℂ)⁻¹ * ∫ v in a..b,
    ((S.nu u v * S.lam u v / S.r u v : ℝ) : ℂ) * radialYSource S u a v

/-- [internal]
Selected incoming electromagnetic piece. The integrating factor is the
actual incoming expansion, rather than an independently chosen ODE solution. -/
@[expose] noncomputable def radialZEM (e : ℝ) (S : Fields) (u a b : ℝ) : ℂ :=
  (S.nu u b : ℂ)⁻¹ * ∫ v in a..b, S.waveSource e u v

/-- [internal]
Exact incoming decomposition from the outgoing wave equation and the
selected outgoing split, charged_SF_new_version.tex:L3384–L3412. Every primitive is
integrable on the proper row. No constants or scalar profile is assumed. -/
theorem ct_z_split_identity {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) :
    S.xi u b / S.nu u b =
      radialZBoundary S u a b + radialZSource S u a b + radialZEM e S u a b := by
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have cn := Calculus.continuousOn_out_section hS.cont_nu hs
  have ct := Calculus.continuousOn_out_section hS.cont_theta hs
  have hr (v : ℝ) (hv : v ∈ Icc a b) :=
    (hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)).ne'
  have hl (v : ℝ) (hv : v ∈ Icc a b) :=
    Complex.ofReal_ne_zero.mpr (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)).ne'
  have cf : ContinuousOn (fun v => ((S.nu u v * S.lam u v / S.r u v : ℝ) : ℂ)) (Icc a b) :=
    continuous_ofReal.comp_continuousOn ((cn.mul cl).div cr hr)
  have cy := ct.div (continuous_ofReal.comp_continuousOn cl) hl
  have iB : IntervalIntegrable (fun v => ((S.nu u v * S.lam u v / S.r u v : ℝ) : ℂ) *
      radialYBoundary S u a v) volume a b :=
    (cf.mul (continuousOn_radialYBoundary_end hS hua hab hs)).intervalIntegrable_of_Icc hab
  have iJ : IntervalIntegrable (fun v => ((S.nu u v * S.lam u v / S.r u v : ℝ) : ℂ) *
      radialYSource S u a v) volume a b :=
    (cf.mul (continuousOn_radialYSource_end hS hua hab hs)).intervalIntegrable_of_Icc hab
  have iY := (cf.mul cy).intervalIntegrable_of_Icc hab (μ := volume)
  have form := (hS.eq_out u a b hua hab hs).2.2.2.2.2.2
  have iem : IntervalIntegrable (S.waveSource e u) volume a b := by
    apply (form.1.add iY).congr
    intro v hv
    dsimp only [Fields.xiV, Pi.add_apply, Pi.mul_apply, Pi.div_apply, Function.comp_def]
    push_cast
    have hv : v ∈ Icc a b := by simpa only [uIcc_of_le hab] using uIoc_subset_uIcc hv
    field_simp [hl v hv]
    ring
  have hflux : (∫ v in a..b, S.xiV e u v) =
      -(∫ v in a..b, ((S.nu u v * S.lam u v / S.r u v : ℝ) : ℂ) * radialYBoundary S u a v) -
      (∫ v in a..b, ((S.nu u v * S.lam u v / S.r u v : ℝ) : ℂ) * radialYSource S u a v) +
      ∫ v in a..b, S.waveSource e u v := by
    have hsum := intervalIntegral.integral_add (iB.neg.sub iJ) iem
    have hdiff := intervalIntegral.integral_sub iB.neg iJ
    dsimp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply] at hsum hdiff
    rw [hdiff, intervalIntegral.integral_neg] at hsum
    rw [← hsum]
    apply intervalIntegral.integral_congr
    intro v hv
    dsimp only
    rw [uIcc_of_le hab] at hv
    have heq := ct_y_split_identity hS hua hv.1
      (fun p hp => hs ⟨hp.1, hp.2.1, hp.2.2.trans hv.2⟩)
    dsimp [Fields.xiV]
    have he : S.theta u v = (S.lam u v : ℂ) *
        (radialYBoundary S u a v + radialYSource S u a v) := by
      rw [← heq, mul_div_cancel₀ _ (hl v hv)]
    rw [he]
    push_cast
    ring
  have heq := form.eq_add_integral
  rw [hflux] at heq
  have hna := Complex.ofReal_ne_zero.mpr (hS.nu_neg (u, a) (hs ⟨rfl, le_rfl, hab⟩)).ne
  have hnb := Complex.ofReal_ne_zero.mpr (hS.nu_neg (u, b) (hs ⟨rfl, hab, le_rfl⟩)).ne
  dsimp [radialZBoundary, radialZSource, radialZEM]
  rw [Complex.ofReal_div]
  field_simp [hna, hnb]
  linear_combination heq

private theorem source_majorant_continuous {e p : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) (q : ℝ → ℝ) (iq : IntervalIntegrable q volume a b) :
    ContinuousOn (fun v => ∫ x in a..v, (S.r u x / S.r u v) ^ p * q x) (Icc a b) := by
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have hr (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.r u v :=
    hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
  have cpow := cr.rpow_const (p := p) (fun v hv => Or.inl (hr v hv).ne')
  have ifunc := iq.continuousOn_mul (by simpa only [uIcc_of_le hab] using cpow)
  have cp : ContinuousOn (fun v => ∫ x in a..v, S.r u x ^ p * q x) (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      (ifunc.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).continuousOn
  apply (cp.div cpow (fun v hv => (Real.rpow_pos_of_pos (hr v hv) p).ne')).congr
  intro v hv
  dsimp only [Pi.div_apply]
  rw [← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  rw [uIcc_of_le hv.1] at hx
  rw [Real.div_rpow (hr x ⟨hx.1, hx.2.trans hv.2⟩).le (hr v hv).le]
  ring

/-- [node eq:ct-z-source]
The incoming source estimate with finite radial separation,
charged_SF_new_version.tex:L3389–L3403. The only coefficient is `1 / (1 - F²)`;
it is uniform in all radii, labels, and source densities. -/
theorem ct_z_source {e δ c Λ F ε : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hstop : ExteriorStops S D δ c Λ F ε)
    {u a b : ℝ} (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D)
    (hF : 0 ≤ F) (hF1 : F < 1) :
    ‖radialZSource S u a b‖ ≤ (1 - F ^ 2)⁻¹ * ∫ v in a..b,
      (S.r u b - S.r u v) / S.r u b * (‖weightedJ S u v‖ / S.lam u v) := by
  let p := 1 - F ^ 2
  let q := fun v => ‖weightedJ S u v‖ / S.lam u v
  have hp : 0 < p := by dsimp [p]; nlinarith only [hF, hF1, sq_nonneg (F - 1)]
  have hp1 : p ≤ 1 := by dsimp [p]; linarith only [sq_nonneg F]
  have cn := Calculus.continuousOn_out_section hS.cont_nu hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have hr (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.r u v :=
    hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
  have hl (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.lam u v := hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)
  have hn (v : ℝ) (hv : v ∈ Icc a b) : S.nu u v < 0 := hS.nu_neg (u, v) (hs ⟨rfl, hv⟩)
  have hratio (v : ℝ) (hv : v ∈ Icc a b) : (-S.nu u v) / (-S.nu u b) ≤ 1 := by
    have hh := (Interaction.radial_expansion_control hS hstop (hua.trans_le hv.1) hv.2
      (fun z hz => hs ⟨hz.1, hv.1.trans hz.2.1, hz.2.2⟩)).2.1
    apply (div_le_one (neg_pos.mpr (hn b ⟨hab, le_rfl⟩))).mpr
    simpa only [one_mul] using (le_div_iff₀ (neg_pos.mpr (hn v hv))).mp hh
  have iq : IntervalIntegrable q volume a b := by
    apply (Interaction.radial_y_source_integrable hS hua hab hs).norm.congr
    intro v hv
    have hv : v ∈ Icc a b := by simpa only [uIcc_of_le hab] using uIoc_subset_uIcc hv
    dsimp [q]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hl v hv)]
  have cY := continuousOn_radialYSource_end hS hua hab hs
  have cw := cl.div cr (fun v hv => (hr v hv).ne')
  have iY := (cw.mul cY.norm).intervalIntegrable_of_Icc hab (μ := volume)
  have cfac := continuous_ofReal.comp_continuousOn ((cn.mul cl).div cr (fun v hv => (hr v hv).ne'))
  have iZ : IntervalIntegrable (fun v => (-(S.nu u b : ℂ)⁻¹) *
      (((S.nu u v * S.lam u v / S.r u v : ℝ) : ℂ) * radialYSource S u a v)) volume a b := by
    have cZ := ((continuousOn_const :
      ContinuousOn (fun _ : ℝ => -(S.nu u b : ℂ)⁻¹) (Icc a b)).mul cfac).mul cY
    apply (cZ.intervalIntegrable_of_Icc hab (μ := volume)).congr
    intro v _
    change (-(S.nu u b : ℂ)⁻¹ * ((S.nu u v * S.lam u v / S.r u v : ℝ) : ℂ)) * _ = _
    ring
  have hfirst : ‖radialZSource S u a b‖ ≤
      ∫ v in a..b, S.lam u v / S.r u v * ‖radialYSource S u a v‖ := by
    rw [radialZSource, ← intervalIntegral.integral_const_mul]
    apply (intervalIntegral.norm_integral_le_integral_norm hab).trans
    apply intervalIntegral.integral_mono_on hab iZ.norm iY
    intro v hv
    change ‖(-(S.nu u b : ℂ)⁻¹) *
      (((S.nu u v * S.lam u v / S.r u v : ℝ) : ℂ) * radialYSource S u a v)‖ ≤
        S.lam u v / S.r u v * ‖radialYSource S u a v‖
    simp only [norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_div, abs_mul, abs_of_neg (hn v hv), abs_of_neg (hn b ⟨hab, le_rfl⟩),
      abs_of_pos (hl v hv), abs_of_pos (hr v hv)]
    have hh := mul_le_mul_of_nonneg_right (hratio v hv)
      (mul_nonneg (div_nonneg (hl v hv).le (hr v hv).le) (norm_nonneg (radialYSource S u a v)))
    convert hh using 1 <;> ring
  have cA := source_majorant_continuous (p := p) hS hua hab hs q iq
  have iA := (cw.mul cA).intervalIntegrable_of_Icc hab (μ := volume)
  have hsecond := intervalIntegral.integral_mono_on hab iY iA (fun v hv => by
    apply mul_le_mul_of_nonneg_left _ (div_nonneg (hl v hv).le (hr v hv).le)
    exact (ct_y_split hS hua hv.1
      (fun z hz => hs ⟨hz.1, hz.2.1, hz.2.2.trans hv.2⟩) hF
      (fun x hx => (hstop (u, x) (hs ⟨rfl, hx.1, hx.2.trans hv.2⟩)).2.2.2.2.1)).2)
  have hkernel := Interaction.radial_source_kernel hS hua hab hs hp hp1 q iq
    (fun v hv => div_nonneg (norm_nonneg _) (hl v hv).le)
  exact hfirst.trans (hsecond.trans hkernel)

/- The electromagnetic term is estimated separately below. -/
end EmcsfAcExtension.Global

namespace EmcsfAcExtension.Global

/-- [internal]
The electromagnetic incoming reconstruction from stopped scalar and charge
profiles, charged_SF_new_version.tex:L3403–L3412. The positive constant depends only
on `δ,Cq`, before coupling, amplitude, scale, and row. The closure consumer
supplies the profiles from its stops and core mass budget. -/
theorem ct_z_charge_of_profiles (δ Cq : ℝ) (hδ : 0 < δ) (hCq : 0 ≤ Cq) :
    ∃ C : ℝ, 0 < C ∧ ∀ (e M₀ F c Λ ε : ℝ) (S : Fields) (D : Set (ℝ × ℝ)) (u a b : ℝ),
      IsSolution e S D → ExteriorStops S D δ c Λ F ε → u < a → a ≤ b →
      outSeg u a b ⊆ D → 0 ≤ M₀ → 0 ≤ F →
      (∀ v ∈ Icc a b, ‖S.phi u v‖ ≤ M₀) →
      (∀ v ∈ Icc a b, |S.Q u v| / S.r u v ^ 2 ≤ Cq * |e| * M₀ * F) →
      ‖radialZEM e S u a b‖ ≤ C * e ^ 2 * M₀ ^ 2 * F * S.r u b ^ 2 := by
  refine ⟨Cq / δ + 1, by positivity, ?_⟩
  intro e M₀ F c Λ ε S D u a b hS hstop hua hab hs hM hF hphi hcharge
  let A := Cq * |e| * M₀ * F
  let K := Cq / δ * e ^ 2 * M₀ ^ 2 * F
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have cn := Calculus.continuousOn_out_section hS.cont_nu hs
  have ct := Calculus.continuousOn_out_section hS.cont_theta hs
  have hr (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.r u v :=
    hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
  have hl (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.lam u v := hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)
  have hn (v : ℝ) (hv : v ∈ Icc a b) : S.nu u v < 0 := hS.nu_neg (u, v) (hs ⟨rfl, hv⟩)
  have hg (v : ℝ) (hv : v ∈ Icc a b) : δ ≤ 1 - S.mu u v := (hstop (u, v) (hs ⟨rfl, hv⟩)).2.1
  have hratio (v : ℝ) (hv : v ∈ Icc a b) : (-S.nu u v) / (-S.nu u b) ≤ 1 := by
    have hh := (Interaction.radial_expansion_control hS hstop (hua.trans_le hv.1) hv.2
      (fun z hz => hs ⟨hz.1, hv.1.trans hz.2.1, hz.2.2⟩)).2.1
    apply (div_le_one (neg_pos.mpr (hn b ⟨hab, le_rfl⟩))).mpr
    simpa only [one_mul] using (le_div_iff₀ (neg_pos.mpr (hn v hv))).mp hh
  have hpoint (v : ℝ) (hv : v ∈ Icc a b) :
      ‖(S.nu u b : ℂ)⁻¹ * S.waveSource e u v‖ ≤ K * (S.lam u v * S.r u v) := by
    have hgp := hδ.trans_le (hg v hv)
    have hq : |S.Q u v| ≤ A * S.r u v ^ 2 :=
      (div_le_iff₀ (sq_pos_of_pos (hr v hv))).mp (hcharge v hv)
    have hqp := mul_le_mul hq (hphi v hv) (norm_nonneg _) (mul_nonneg hA (sq_nonneg _))
    have hgapnorm : ‖(1 - (S.mu u v : ℂ))‖ = 1 - S.mu u v := by
      have heq : (1 - (S.mu u v : ℂ)) = ((1 - S.mu u v : ℝ) : ℂ) := by push_cast; rfl
      rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hgp]
    have hnrm : ‖(S.nu u b : ℂ)⁻¹ * S.waveSource e u v‖ =
        ((-S.nu u v) / (-S.nu u b)) *
          (|e| * |S.Q u v| * ‖S.phi u v‖ * S.lam u v / ((1 - S.mu u v) * S.r u v)) := by
      simp only [Fields.waveSource, norm_mul, norm_div, norm_inv, Complex.norm_I,
        one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_neg (hn v hv), abs_of_neg (hn b ⟨hab, le_rfl⟩),
        abs_of_pos (hl v hv), abs_of_pos (hr v hv), hgapnorm]
      field_simp [hgp.ne', (hr v hv).ne']
    rw [hnrm]
    calc
      _ ≤ |e| * |S.Q u v| * ‖S.phi u v‖ * S.lam u v / ((1 - S.mu u v) * S.r u v) :=
        mul_le_of_le_one_left (div_nonneg
          (mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (norm_nonneg _))
            (hl v hv).le)
          (mul_nonneg hgp.le (hr v hv).le)) (hratio v hv)
      _ = (|e| * S.lam u v / S.r u v) * (|S.Q u v| * ‖S.phi u v‖ / (1 - S.mu u v)) := by
        field_simp [hgp.ne', (hr v hv).ne']
      _ ≤ (|e| * S.lam u v / S.r u v) * (A * S.r u v ^ 2 * M₀ / δ) := by
        apply mul_le_mul_of_nonneg_left _
          (div_nonneg (mul_nonneg (abs_nonneg _) (hl v hv).le) (hr v hv).le)
        exact (div_le_div_of_nonneg_right hqp hgp.le).trans
          (div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg hA (sq_nonneg _)) hM) hδ (hg v hv))
      _ = _ := by dsimp [K, A]; rw [← sq_abs e]; field_simp [hδ.ne', (hr v hv).ne']
  have cy := ct.div (continuous_ofReal.comp_continuousOn cl)
    (fun v hv => Complex.ofReal_ne_zero.mpr (hl v hv).ne')
  have iY := ((continuous_ofReal.comp_continuousOn ((cn.mul cl).div cr
    (fun v hv => (hr v hv).ne'))).mul cy).intervalIntegrable_of_Icc hab (μ := volume)
  have form := (hS.eq_out u a b hua hab hs).2.2.2.2.2.2
  have iem : IntervalIntegrable (S.waveSource e u) volume a b := by
    apply (form.1.add iY).congr
    intro v hv
    have hv : v ∈ Icc a b := by simpa only [uIcc_of_le hab] using uIoc_subset_uIcc hv
    dsimp only [Pi.add_apply, Pi.mul_apply, Pi.div_apply, Function.comp_def, Fields.xiV]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr (hl v hv).ne']
    ring
  have im := (cl.mul cr).intervalIntegrable_of_Icc hab (μ := volume)
  have hi := intervalIntegral.integral_mono_on hab (iem.const_mul (S.nu u b : ℂ)⁻¹).norm
    (im.const_mul K) hpoint
  rw [intervalIntegral.integral_const_mul] at hi
  dsimp only [Pi.mul_apply] at hi
  have hmom := Interaction.radial_moment hS hua hab hs 1
  norm_num only [pow_one, Nat.reduceAdd, Nat.cast_one] at hmom
  rw [hmom] at hi
  rw [radialZEM, ← intervalIntegral.integral_const_mul]
  have hnorm := (intervalIntegral.norm_integral_le_integral_norm hab).trans hi
  have hlast : K * ((S.r u b ^ 2 - S.r u a ^ 2) / 2) ≤
      (Cq / δ + 1) * e ^ 2 * M₀ ^ 2 * F * S.r u b ^ 2 := by
    have hsmall : (S.r u b ^ 2 - S.r u a ^ 2) / 2 ≤ S.r u b ^ 2 := by
      nlinarith only [sq_nonneg (S.r u a), sq_nonneg (S.r u b)]
    have hh := mul_le_mul_of_nonneg_left hsmall hK
    dsimp [K] at hh
    have hpos : 0 ≤ e ^ 2 * M₀ ^ 2 * F * S.r u b ^ 2 := by positivity
    nlinarith only [hh, hpos]
  exact hnorm.trans hlast

/-- [node eq:ct-z-boundary]
The incoming boundary reconstruction retains its expansion ratio,
charged_SF_new_version.tex:L3384–L3388. The denominator is exactly `1 - F² - ε`;
no radius-dependent or data-dependent constant occurs. -/
theorem ct_z_boundary {e δ c Λ F ε : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hstop : ExteriorStops S D δ c Λ F ε)
    {u a b : ℝ} (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D)
    (hF : 0 ≤ F) (hε : 0 ≤ ε) (hgap : ε < 1 - F ^ 2) :
    ‖radialZBoundary S u a b‖ ≤ ((-S.nu u a) / (-S.nu u b)) *
      (‖S.xi u a / S.nu u a‖ + ‖S.theta u a / S.lam u a‖ / (1 - F ^ 2 - ε)) := by
  let p := 1 - F ^ 2
  let d := p - ε
  let Y := ‖S.theta u a / S.lam u a‖
  have hd : 0 < d := sub_pos.mpr hgap
  have hd1 : d ≤ 1 := by dsimp [d, p]; linarith only [hε, sq_nonneg F]
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have cn := Calculus.continuousOn_out_section hS.cont_nu hs
  have hr (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.r u v :=
    hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
  have hl (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.lam u v := hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)
  have hn (v : ℝ) (hv : v ∈ Icc a b) : S.nu u v < 0 := hS.nu_neg (u, v) (hs ⟨rfl, hv⟩)
  let w := fun v => (S.nu u v / S.nu u a) * (S.lam u v / S.r u v)
  have hw (v : ℝ) (hv : v ∈ Icc a b) : 0 ≤ w v :=
    mul_nonneg (div_pos_of_neg_of_neg (hn v hv) (hn a ⟨le_rfl, hab⟩)).le
      (div_nonneg (hl v hv).le (hr v hv).le)
  have cw : ContinuousOn w (Icc a b) :=
    (cn.div_const (S.nu u a)).mul (cl.div cr (fun v hv => (hr v hv).ne'))
  have cY := continuousOn_radialYBoundary_end hS hua hab hs
  have iI := (cw.mul cY.norm).intervalIntegrable_of_Icc hab (μ := volume)
  have cker : ContinuousOn (fun v => S.lam u v / S.r u v ^ (1 + d)) (Icc a b) :=
    cl.div (cr.rpow_const (fun v hv => Or.inl (hr v hv).ne'))
      (fun v hv => (Real.rpow_pos_of_pos (hr v hv) _).ne')
  have iker := cker.intervalIntegrable_of_Icc hab (μ := volume)
  have hI := intervalIntegral.integral_mono_on hab iI (iker.const_mul (Y * S.r u a ^ d))
    (fun v hv => by
      have hgrow := (Interaction.radial_expansion_control hS hstop hua hv.1
        (fun z hz => hs ⟨hz.1, hz.2.1, hz.2.2.trans hv.2⟩)).2.2
      have hy := (ct_y_split hS hua hv.1
        (fun z hz => hs ⟨hz.1, hz.2.1, hz.2.2.trans hv.2⟩) hF
        (fun x hx => (hstop (u, x) (hs ⟨rfl, hx.1, hx.2.trans hv.2⟩)).2.2.2.2.1)).1
      have hpows : (S.r u v / S.r u a) ^ ε * (S.r u a / S.r u v) ^ p =
          S.r u a ^ d / S.r u v ^ d := by
        dsimp only [d]
        rw [Real.div_rpow (hr v hv).le (hr a ⟨le_rfl, hab⟩).le,
          Real.div_rpow (hr a ⟨le_rfl, hab⟩).le (hr v hv).le,
          Real.rpow_sub (hr a ⟨le_rfl, hab⟩) p ε, Real.rpow_sub (hr v hv) p ε]
        field_simp [(Real.rpow_pos_of_pos (hr a ⟨le_rfl, hab⟩) ε).ne',
          (Real.rpow_pos_of_pos (hr v hv) ε).ne', (Real.rpow_pos_of_pos (hr v hv) p).ne']
      have hh := mul_le_mul hgrow hy (norm_nonneg _)
        (Real.rpow_nonneg (div_nonneg (hr v hv).le (hr a ⟨le_rfl, hab⟩).le) ε)
      rw [neg_div_neg_eq] at hh
      have hh' := mul_le_mul_of_nonneg_left hh (div_nonneg (hl v hv).le (hr v hv).le)
      change w v * ‖radialYBoundary S u a v‖ ≤
        (Y * S.r u a ^ d) * (S.lam u v / S.r u v ^ (1 + d))
      rw [show (S.r u v / S.r u a) ^ ε * (Y * (S.r u a / S.r u v) ^ p) =
          Y * (S.r u a ^ d / S.r u v ^ d) by rw [← hpows]; ring] at hh'
      rw [Real.rpow_add (hr v hv) 1 d, Real.rpow_one]
      dsimp only [w, Y] at hh' ⊢
      convert hh' using 1 <;> ring)
  rw [intervalIntegral.integral_const_mul] at hI
  dsimp only [Pi.mul_apply] at hI
  have hker := Interaction.radial_power_tail_le hS hua hab hs hd hd1
  have hker' : (S.r u b - S.r u a) / (d * S.r u b) ≤ 1 / d := by
    apply (div_le_div_iff₀ (mul_pos hd (hr b ⟨hab, le_rfl⟩)) hd).mpr
    nlinarith only [mul_nonneg hd.le (hr a ⟨le_rfl, hab⟩).le]
  have hI' : (∫ v in a..b, w v * ‖radialYBoundary S u a v‖) ≤ Y / d := by
    have hh := mul_le_mul_of_nonneg_left (hker.trans hker') (norm_nonneg (S.theta u a / S.lam u a))
    calc
      _ ≤ Y * S.r u a ^ d * (∫ v in a..b, S.lam u v / S.r u v ^ (1 + d)) := hI
      _ = Y * (S.r u a ^ d * (∫ v in a..b, S.lam u v / S.r u v ^ (1 + d))) := by ring
      _ ≤ Y * (1 / d) := hh
      _ = _ := by ring
  let B := ∫ v in a..b, (w v : ℂ) * radialYBoundary S u a v
  have hB : ‖B‖ ≤ Y / d := by
    apply (intervalIntegral.norm_integral_le_integral_norm hab).trans
    have heq : (∫ v in a..b, ‖(w v : ℂ) * radialYBoundary S u a v‖) =
        ∫ v in a..b, w v * ‖radialYBoundary S u a v‖ := by
      apply intervalIntegral.integral_congr
      intro v hv
      dsimp only
      rw [uIcc_of_le hab] at hv
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw v hv)]
    rwa [heq]
  have hna := Complex.ofReal_ne_zero.mpr (hn a ⟨le_rfl, hab⟩).ne
  have hnb := Complex.ofReal_ne_zero.mpr (hn b ⟨hab, le_rfl⟩).ne
  have hrep : radialZBoundary S u a b =
      ((S.nu u a / S.nu u b : ℝ) : ℂ) * (S.xi u a / S.nu u a - B) := by
    dsimp [radialZBoundary, B]
    rw [mul_sub, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro v _
    dsimp [w]
    push_cast
    field_simp [hna, hnb]
  rw [hrep, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos_of_neg_of_neg (hn a ⟨le_rfl, hab⟩) (hn b ⟨hab, le_rfl⟩)), neg_div_neg_eq]
  exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add le_rfl hB))
    (div_pos_of_neg_of_neg (hn a ⟨le_rfl, hab⟩) (hn b ⟨hab, le_rfl⟩)).le

end EmcsfAcExtension.Global
