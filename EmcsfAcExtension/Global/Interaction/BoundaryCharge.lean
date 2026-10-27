module

public import EmcsfAcExtension.Global.Interaction.Profiles
import EmcsfAcExtension.Local.Calculus.RelativeCharge
import EmcsfAcExtension.Local.Calculus.Reconstruction
import EmcsfAcExtension.Global.Calculus.Sections

/-! # Charge at the boundary of an excluded core

The scalar may grow towards the axis. Its weighted growth is controlled by
the complete core's ordinary mass and gap, not by an exterior derivative
stop extended into the core. Source: `charged_SF_new_version.tex:L3325–L3360`.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Interaction

private theorem cauchy_schwarz {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
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

/-- [internal]
Core scalar growth from the complete-core gap and a boundary scalar bound,
charged_SF_new_version.tex:L3325–L3333. The exact coefficient is `2 / δ`, uniform in
the solution, radius, and coupling. The exterior profile consumer supplies
the boundary scalar bound; no scalar supremum on the core is assumed. -/
theorem core_scalar_growth_of_boundary_bound {e δ M₀ : ℝ} {S : Fields}
    {D : Set (ℝ × ℝ)} (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u u b ⊆ D) (hδ : 0 < δ)
    (hgap : ∀ v ∈ Icc u b, δ ≤ 1 - S.mu u v) (hM : ‖S.phi u b‖ ≤ M₀) :
    ‖S.phi u a‖ ≤ M₀ + Real.sqrt (2 * S.m u b / (δ * S.r u a)) := by
  have hub := hua.trans_le hab
  have hsa : outSeg u a b ⊆ D := fun p hp => hs ⟨hp.1, hua.le.trans hp.2.1, hp.2.2⟩
  have hp (v : ℝ) (hv : v ∈ Icc a b) : (u, v) ∈ D := hsa ⟨rfl, hv⟩
  have hr (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.r u v :=
    hS.r_pos (u, v) (hp v hv) (hua.trans_le hv.1)
  have hl (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.lam u v := hS.lam_pos (u, v) (hp v hv)
  have hg (v : ℝ) (hv : v ∈ Icc a b) : 0 < 1 - S.mu u v :=
    hδ.trans_le (hgap v ⟨hua.le.trans hv.1, hv.2⟩)
  have cr := Calculus.continuousOn_out_section hS.cont_r hsa
  have cl := Calculus.continuousOn_out_section hS.cont_lam hsa
  have ct := Calculus.continuousOn_out_section hS.cont_theta hsa
  have cmu := Local.continuousOn_mu_out hS hub hs
  have cg : ContinuousOn (fun v => 1 - S.mu u v) (Icc a b) :=
    continuousOn_const.sub (cmu.mono (Icc_subset_Icc hua.le le_rfl))
  have cy := ct.div (continuous_ofReal.comp_continuousOn cl)
    (fun v hv => Complex.ofReal_ne_zero.mpr (hl v hv).ne')
  let f := fun v => Real.sqrt (S.lam u v) * Real.sqrt (1 - S.mu u v) *
    ‖S.theta u v / S.lam u v‖
  let g := fun v => Real.sqrt (S.lam u v) / Real.sqrt (1 - S.mu u v) / S.r u v
  have cf : ContinuousOn f (Icc a b) := (cl.sqrt.mul cg.sqrt).mul cy.norm
  have cgg : ContinuousOn g (Icc a b) :=
    (cl.sqrt.div cg.sqrt (fun v hv => (Real.sqrt_pos.mpr (hg v hv)).ne')).div cr
      (fun v hv => (hr v hv).ne')
  have fsq (v : ℝ) (hv : v ∈ Icc a b) : f v ^ 2 =
      S.lam u v * (1 - S.mu u v) * ‖S.theta u v / S.lam u v‖ ^ 2 := by
    dsimp [f]
    rw [mul_pow, mul_pow, Real.sq_sqrt (hl v hv).le, Real.sq_sqrt (hg v hv).le]
  have gsq (v : ℝ) (hv : v ∈ Icc a b) : g v ^ 2 =
      S.lam u v / ((1 - S.mu u v) * S.r u v ^ 2) := by
    dsimp [g]
    rw [div_pow, div_pow, Real.sq_sqrt (hl v hv).le, Real.sq_sqrt (hg v hv).le, div_div]
  have fg (v : ℝ) (hv : v ∈ Icc a b) : f v * g v = ‖S.phiV u v‖ := by
    have hgs := (Real.sqrt_pos.mpr (hg v hv)).ne'
    have he : f v * g v = Real.sqrt (S.lam u v) ^ 2 / S.r u v *
        ‖S.theta u v / S.lam u v‖ := by dsimp [f, g]; field_simp [hgs]
    rw [he, Real.sq_sqrt (hl v hv).le]
    simp only [Fields.phiV, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hl v hv), abs_of_pos (hr v hv)]
    field_simp [(hl v hv).ne', (hr v hv).ne']
  have hcs := cauchy_schwarz hab cf cgg
  rw [intervalIntegral.integral_congr (fun v hv => fg v ((uIcc_of_le hab) ▸ hv)),
    intervalIntegral.integral_congr (fun v hv => fsq v ((uIcc_of_le hab) ▸ hv)),
    intervalIntegral.integral_congr (fun v hv => gsq v ((uIcc_of_le hab) ▸ hv))] at hcs
  have forms := hS.eq_out u a b hua hab hsa
  have hnorm : ‖S.phi u a - S.phi u b‖ ≤ ∫ v in a..b, ‖S.phiV u v‖ := by
    rw [norm_sub_rev, forms.2.2.2.2.2.1.2]
    exact intervalIntegral.norm_integral_le_integral_norm hab
  have hdiff := (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hcs
  have clcore := Calculus.continuousOn_out_section hS.cont_lam hs
  have ctcore := Calculus.continuousOn_out_section hS.cont_theta hs
  have cycore := ctcore.div (continuous_ofReal.comp_continuousOn clcore)
    (fun v hv => Complex.ofReal_ne_zero.mpr (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)).ne')
  have cgcore : ContinuousOn (fun v => 1 - S.mu u v) (Icc u b) := continuousOn_const.sub cmu
  have iE := ((clcore.mul cgcore).mul (cycore.norm.pow 2))
    |>.intervalIntegrable_of_Icc hub.le (μ := volume)
  have iEa := iE.mono_set (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc ⟨hua.le, hab⟩))
  have iEb := iE.mono_set (uIcc_subset_uIcc (Icc_subset_uIcc ⟨hua.le, hab⟩) right_mem_uIcc)
  have hEn := intervalIntegral.integral_nonneg hua.le (μ := volume) (fun v hv =>
    mul_nonneg (mul_nonneg (hS.lam_pos (u, v) (hs ⟨rfl, hv.1, hv.2.trans hab⟩)).le
      (hS.one_sub_mu_pos (u, v) (hs ⟨rfl, hv.1, hv.2.trans hab⟩)).le)
        (sq_nonneg ‖S.theta u v / S.lam u v‖))
  have hsum := intervalIntegral.integral_add_adjacent_intervals iEa iEb
  have hmass := Local.RelCharge.mass_controls_radial_flux hS hub hs
  dsimp only [Pi.mul_apply, Pi.pow_apply, Pi.div_apply, Function.comp_def] at iE hsum
  have hE : (∫ v in a..b, S.lam u v * (1 - S.mu u v) *
      ‖S.theta u v / S.lam u v‖ ^ 2) ≤ 2 * S.m u b := by linarith only [hmass, hsum, hEn]
  have cW : ContinuousOn (fun v => S.lam u v / ((1 - S.mu u v) * S.r u v ^ 2)) (Icc a b) :=
    cl.div (cg.mul (cr.pow 2)) (fun v hv => mul_ne_zero (hg v hv).ne' (pow_ne_zero _ (hr v hv).ne'))
  have iW := cW.intervalIntegrable_of_Icc hab (μ := volume)
  have iW' := ((cl.div (cr.pow 2) (fun v hv => pow_ne_zero _ (hr v hv).ne')).div
    continuousOn_const (fun _ _ => hδ.ne')).intervalIntegrable_of_Icc hab (μ := volume)
  have hW := intervalIntegral.integral_mono_on hab iW iW' (fun v hv => by
    rw [← div_div, div_right_comm]
    exact div_le_div_of_nonneg_left (div_nonneg (hl v hv).le (sq_nonneg _))
      hδ (hgap v ⟨hua.le.trans hv.1, hv.2⟩))
  have ik := (cl.div (cr.pow 2) (fun v hv => pow_ne_zero _ (hr v hv).ne'))
    |>.intervalIntegrable_of_Icc hab (μ := volume)
  have hkernel : (∫ v in a..b, S.lam u v / S.r u v ^ 2) =
      1 / S.r u a - 1 / S.r u b := by
    have hc : ContinuousOn (fun v => -(S.r u v)⁻¹) (Icc a b) :=
      (cr.inv₀ (fun v hv => (hr v hv).ne')).neg
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hc
      (f' := fun v => S.lam u v / S.r u v ^ 2) (fun v hv => ?_) ik
    · simpa only [one_div, neg_sub_neg] using hftc
    · have hd := (Local.IsSolution.hasDerivAt_radius_out hS hs ⟨hua.trans hv.1, hv.2⟩).inv
        (hr v ⟨hv.1.le, hv.2.le⟩).ne'
      simpa only [Pi.inv_apply, Pi.neg_apply, neg_div, neg_neg] using! hd.neg
  dsimp only [Pi.div_apply] at hW
  rw [intervalIntegral.integral_div] at hW
  simp only [Pi.pow_apply] at hW
  rw [hkernel] at hW
  have hW' : (∫ v in a..b, S.lam u v / ((1 - S.mu u v) * S.r u v ^ 2)) ≤
      1 / (δ * S.r u a) := by
    calc
      _ ≤ _ := hW
      _ ≤ (1 / S.r u a) / δ := div_le_div_of_nonneg_right
        (sub_le_self _ (one_div_nonneg.mpr (hr b ⟨hab, le_rfl⟩).le)) hδ.le
      _ = _ := by ring
  have hW0 := intervalIntegral.integral_nonneg (μ := volume) hab (fun v hv =>
    div_nonneg (hl v hv).le (mul_nonneg (hg v hv).le (sq_nonneg (S.r u v))))
  have hE0 := intervalIntegral.integral_nonneg (μ := volume) hab (fun v hv =>
    mul_nonneg (mul_nonneg (hl v hv).le (hg v hv).le) (sq_nonneg ‖S.theta u v / S.lam u v‖))
  have hsq : ‖S.phi u a - S.phi u b‖ ^ 2 ≤ 2 * S.m u b / (δ * S.r u a) := by
    calc
      _ ≤ _ := hdiff
      _ ≤ (2 * S.m u b) * (1 / (δ * S.r u a)) :=
        mul_le_mul hE hW' hW0 (hE0.trans hE)
      _ = _ := by ring
  have hroot := Real.le_sqrt_of_sq_le hsq
  exact (norm_le_norm_add_norm_sub' (S.phi u a) (S.phi u b)).trans (add_le_add hM hroot)

end EmcsfAcExtension.Global.Interaction

namespace EmcsfAcExtension.Global

/-- [internal]
Boundary charge-square from a scalar bound at the outer edge of the core,
charged_SF_new_version.tex:L3334–L3343. The positive constant depends only on `δ` and
is chosen before the coupling, scalar bound, solution, and cone. The
exterior scalar-profile consumer supplies the single boundary scalar bound.
Both terms `M₀² b³` and `m_b b²` are retained. -/
theorem ct_boundary_charge_square_of_boundary_bound (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (e M₀ : ℝ) (S : Fields) (D : Set (ℝ × ℝ)) (u b : ℝ),
      IsSolution e S D → u < b → outSeg u u b ⊆ D →
      (∀ v ∈ Icc u b, δ ≤ 1 - S.mu u v) → ‖S.phi u b‖ ≤ M₀ →
      S.Q u b ^ 2 ≤ C * e ^ 2 * S.m u b *
        (M₀ ^ 2 * S.r u b ^ 3 + S.m u b * S.r u b ^ 2) := by
  refine ⟨4 / δ ^ 2, by positivity, ?_⟩
  intro e M₀ S D u b hS hub hs hgap hM
  have hp (v : ℝ) (hv : v ∈ Icc u b) : (u, v) ∈ D := hs ⟨rfl, hv⟩
  have hr (v : ℝ) (hv : v ∈ Icc u b) : 0 ≤ S.r u v := by
    rcases hv.1.eq_or_lt with h | h
    · subst v
      rw [(hS.axis u (hp u ⟨le_rfl, hub.le⟩)).1]
    · exact (hS.r_pos (u, v) (hp v hv) h).le
  have hm : 0 ≤ S.m u b := by
    have hflux := Local.RelCharge.mass_controls_radial_flux hS hub hs
    have hn := intervalIntegral.integral_nonneg hub.le (μ := volume) (fun v hv =>
      mul_nonneg (mul_nonneg (hS.lam_pos (u, v) (hp v hv)).le
        (hS.one_sub_mu_pos (u, v) (hp v hv)).le) (sq_nonneg ‖S.theta u v / S.lam u v‖))
    linarith only [hflux, hn]
  have hM0 : 0 ≤ M₀ := (norm_nonneg _).trans hM
  have hphi (v : ℝ) (hv : v ∈ Icc u b) :
      S.r u v ^ 2 * ‖S.phi u v‖ ^ 2 ≤
        2 * M₀ ^ 2 * S.r u v ^ 2 + (4 * S.m u b / δ) * S.r u v := by
    rcases hv.1.eq_or_lt with h | huv
    · subst v
      simp only [(hS.axis u (hp u ⟨le_rfl, hub.le⟩)).1, zero_pow (by decide : 2 ≠ 0),
        zero_mul, mul_zero, add_zero, le_refl]
    · have hrv := hS.r_pos (u, v) (hp v hv) huv
      have hcore := Interaction.core_scalar_growth_of_boundary_bound hS huv hv.2 hs hδ hgap hM
      have hsqrt := Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hm)
        (mul_nonneg hδ.le hrv.le))
      change Real.sqrt (2 * S.m u b / (δ * S.r u v)) ^ 2 =
        2 * S.m u b / (δ * S.r u v) at hsqrt
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hcore 2
      have hdiff := sq_nonneg (M₀ - Real.sqrt (2 * S.m u b / (δ * S.r u v)))
      have hsq' : ‖S.phi u v‖ ^ 2 ≤ 2 * M₀ ^ 2 + 4 * S.m u b / (δ * S.r u v) := by
        calc
          _ ≤ 2 * M₀ ^ 2 + 2 * Real.sqrt (2 * S.m u b / (δ * S.r u v)) ^ 2 := by
            nlinarith only [hsq, hdiff]
          _ = _ := by rw [hsqrt]; ring
      calc
        _ ≤ S.r u v ^ 2 * (2 * M₀ ^ 2 + 4 * S.m u b / (δ * S.r u v)) :=
          mul_le_mul_of_nonneg_left hsq' (sq_nonneg _)
        _ = _ := by field_simp [hδ.ne', hrv.ne']
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have cp := Calculus.continuousOn_out_section hS.cont_phi hs
  have cg : ContinuousOn (fun v => 1 - S.mu u v) (Icc u b) :=
    continuousOn_const.sub (Local.continuousOn_mu_out hS hub hs)
  have iB := (((cl.mul (cr.pow 2)).mul (cp.norm.pow 2)).div cg
    (fun v hv => (hδ.trans_le (hgap v hv)).ne')).intervalIntegrable_of_Icc hub.le (μ := volume)
  have i2 := (cl.mul (cr.pow 2)).intervalIntegrable_of_Icc hub.le (μ := volume)
  have i1 := (cl.mul cr).intervalIntegrable_of_Icc hub.le (μ := volume)
  have hB := intervalIntegral.integral_mono_on hub.le iB
    ((i2.const_mul (2 * M₀ ^ 2 / δ)).add (i1.const_mul (4 * S.m u b / δ ^ 2))) (fun v hv => by
      change S.lam u v * S.r u v ^ 2 * ‖S.phi u v‖ ^ 2 / (1 - S.mu u v) ≤
        (2 * M₀ ^ 2 / δ) * (S.lam u v * S.r u v ^ 2) +
          (4 * S.m u b / δ ^ 2) * (S.lam u v * S.r u v)
      calc
        _ = S.lam u v * (S.r u v ^ 2 * ‖S.phi u v‖ ^ 2 / (1 - S.mu u v)) := by ring
        _ ≤ S.lam u v * ((2 * M₀ ^ 2 * S.r u v ^ 2 +
            (4 * S.m u b / δ) * S.r u v) / δ) := by
          apply mul_le_mul_of_nonneg_left _ (hS.lam_pos (u, v) (hp v hv)).le
          exact (div_le_div_of_nonneg_right (hphi v hv)
            (hδ.trans_le (hgap v hv)).le).trans
            (div_le_div_of_nonneg_left (add_nonneg
              (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg M₀)) (sq_nonneg (S.r u v)))
              (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hm) hδ.le) (hr v hv)))
              hδ (hgap v hv))
        _ = _ := by ring)
  rw [intervalIntegral.integral_add (i2.const_mul _) (i1.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hB
  dsimp only [Pi.mul_apply, Pi.pow_apply, Pi.div_apply] at hB
  have hmom1 := Local.outgoing_radius_moment hS hub.le hs 1
  simp only [pow_one, Nat.reduceAdd] at hmom1
  rw [Local.outgoing_radius_moment hS hub.le hs 2, hmom1] at hB
  norm_num only [Nat.reduceAdd, pow_one] at hB
  have hcharge := (Local.lem_relative_charge hS hub hs).trans
    (mul_le_mul_of_nonneg_left hB (by
      have : 0 ≤ S.mu u b := div_nonneg (by linarith only [hm]) (hr b ⟨hub.le, le_rfl⟩)
      exact mul_nonneg (mul_nonneg (sq_nonneg e) this) (hr b ⟨hub.le, le_rfl⟩)))
  have hcoeff : 4 / (3 * δ) ≤ 4 / δ ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hδ)
      (by nlinarith only [hδ.le, mul_le_mul_of_nonneg_left hδ1 hδ.le])
  calc
    _ ≤ _ := hcharge
    _ = 4 / (3 * δ) * (e ^ 2 * S.m u b * M₀ ^ 2 * S.r u b ^ 3) +
        (4 / δ ^ 2) * (e ^ 2 * S.m u b ^ 2 * S.r u b ^ 2) := by
      dsimp [Fields.mu]
      field_simp [(hS.r_pos (u, b) (hp b ⟨hub.le, le_rfl⟩) hub).ne']
      ring
    _ ≤ (4 / δ ^ 2) * (e ^ 2 * S.m u b * M₀ ^ 2 * S.r u b ^ 3) +
        (4 / δ ^ 2) * (e ^ 2 * S.m u b ^ 2 * S.r u b ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_right hcoeff
        (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg e) hm) (sq_nonneg M₀))
          (pow_nonneg (hr b ⟨hub.le, le_rfl⟩) 3))) le_rfl
    _ = _ := by ring

/-- [internal]
Normalized boundary charge, charged_SF_new_version.tex:L3344–L3349, from the complete
core and its boundary scalar bound. The positive constant depends only on
the full-core gap; it is uniform in coupling, scalar background, and radius.
The exterior profile consumer supplies the boundary scalar bound. -/
theorem ct_boundary_charge_of_boundary_bound (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (e M₀ : ℝ) (S : Fields) (D : Set (ℝ × ℝ)) (u b : ℝ),
      IsSolution e S D → u < b → outSeg u u b ⊆ D →
      (∀ v ∈ Icc u b, δ ≤ 1 - S.mu u v) → ‖S.phi u b‖ ≤ M₀ →
      |S.Q u b| / S.r u b ^ 2 ≤ C * |e| *
        (M₀ * Real.sqrt (S.m u b / S.r u b) + S.m u b / S.r u b) := by
  obtain ⟨C, hC, hbound⟩ := ct_boundary_charge_square_of_boundary_bound δ hδ hδ1
  refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hC, ?_⟩
  intro e M₀ S D u b hS hub hs hgap hM
  have hsq := hbound e M₀ S D u b hS hub hs hgap hM
  have hr := hS.r_pos (u, b) (hs ⟨rfl, hub.le, le_rfl⟩) hub
  have hM0 : 0 ≤ M₀ := (norm_nonneg _).trans hM
  have hm : 0 ≤ S.m u b := by
    have hflux := Local.RelCharge.mass_controls_radial_flux hS hub hs
    have hn := intervalIntegral.integral_nonneg hub.le (μ := volume) (fun v hv =>
      mul_nonneg (mul_nonneg (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)).le
        (hS.one_sub_mu_pos (u, v) (hs ⟨rfl, hv⟩)).le) (sq_nonneg ‖S.theta u v / S.lam u v‖))
    linarith only [hflux, hn]
  let η := S.m u b / S.r u b
  have hη : 0 ≤ η := div_nonneg hm hr.le
  have hsq' : (|S.Q u b| / S.r u b ^ 2) ^ 2 ≤ C * e ^ 2 * (M₀ ^ 2 * η + η ^ 2) := by
    rw [div_pow, sq_abs]
    calc
      _ ≤ (C * e ^ 2 * S.m u b * (M₀ ^ 2 * S.r u b ^ 3 +
          S.m u b * S.r u b ^ 2)) / (S.r u b ^ 2) ^ 2 :=
        div_le_div_of_nonneg_right hsq (sq_nonneg _)
      _ = _ := by dsimp [η]; field_simp [hr.ne']
  have hinner : M₀ ^ 2 * η + η ^ 2 ≤ (M₀ * Real.sqrt η + η) ^ 2 := by
    have he : (M₀ * Real.sqrt η) ^ 2 = M₀ ^ 2 * η := by
      rw [mul_pow, Real.sq_sqrt hη]
    have hn := mul_nonneg (mul_nonneg hM0 (Real.sqrt_nonneg η)) hη
    nlinarith only [he, hn]
  have hpos : 0 ≤ Real.sqrt C * |e| * (M₀ * Real.sqrt η + η) := by positivity
  apply (sq_le_sq₀ (div_nonneg (abs_nonneg _) (sq_nonneg _)) hpos).mp
  calc
    _ ≤ _ := hsq'
    _ ≤ C * e ^ 2 * (M₀ * Real.sqrt η + η) ^ 2 :=
      mul_le_mul_of_nonneg_left hinner (mul_nonneg hC.le (sq_nonneg _))
    _ = _ := by rw [mul_pow, mul_pow, Real.sq_sqrt hC.le, sq_abs]

private theorem charge_increment {e M₀ F : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) (hM : 0 ≤ M₀) (_hF : 0 ≤ F)
    (hphi : ∀ v ∈ Icc a b, ‖S.phi u v‖ ≤ M₀)
    (hy : ∀ v ∈ Icc a b, ‖S.theta u v / S.lam u v‖ ≤ F) :
    |S.Q u b - S.Q u a| ≤ |e| * M₀ * F * (S.r u b ^ 2 - S.r u a ^ 2) / 2 := by
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have hr (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.r u v :=
    hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
  have hl (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.lam u v := hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)
  have form := (hS.eq_out u a b hua hab hs).2.2.2.1
  have im := (cl.mul cr).intervalIntegrable_of_Icc hab (μ := volume)
  have hp (v : ℝ) (hv : v ∈ Icc a b) : ‖S.QV e u v‖ ≤ |e| * M₀ * F * (S.lam u v * S.r u v) := by
    have ht : ‖S.theta u v‖ ≤ S.lam u v * F := by
      have hh := hy v hv
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hl v hv)] at hh
      simpa only [mul_comm] using (div_le_iff₀ (hl v hv)).mp hh
    simp only [Fields.QV, Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos (hr v hv)]
    calc
      _ ≤ |e| * S.r u v * (‖S.phi u v‖ * ‖S.theta u v‖) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (abs_nonneg _) (hr v hv).le)
        simpa only [norm_mul, Complex.norm_conj] using
          Complex.abs_im_le_norm (starRingEnd ℂ (S.phi u v) * S.theta u v)
      _ ≤ |e| * S.r u v * (M₀ * (S.lam u v * F)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (hphi v hv) ht (norm_nonneg _) hM)
          (mul_nonneg (abs_nonneg _) (hr v hv).le)
      _ = _ := by ring
  have hi := intervalIntegral.integral_mono_on hab form.1.norm
    (im.const_mul (|e| * M₀ * F)) hp
  rw [intervalIntegral.integral_const_mul] at hi
  dsimp only [Pi.mul_apply] at hi
  have hdr (v : ℝ) (hv : v ∈ Ioo a b) : HasDerivAt (S.r u) (S.lam u v) v := by
    apply Local.hasDerivAt_of_integralForm_interior hv (cl.mono Ioo_subset_Icc_self)
    intro c d hac hcd hdb
    exact (hS.eq_out u c d (hua.trans hac) hcd (fun p hp =>
      hs ⟨hp.1, hac.le.trans hp.2.1, hp.2.2.trans hdb.le⟩)).1
  have hmom : (∫ v in a..b, S.lam u v * S.r u v) = (S.r u b ^ 2 - S.r u a ^ 2) / 2 := by
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab (cr.pow 2)
      (f' := fun v => 2 * (S.lam u v * S.r u v)) (fun v hv => ?_) (im.const_mul 2)
    · rw [intervalIntegral.integral_const_mul] at heq
      simp only [Pi.pow_apply] at heq
      linarith only [heq]
    · apply ((hdr v hv).pow 2).congr_deriv
      norm_num only [Nat.reduceSub, pow_one, Nat.cast_ofNat]
      ring
  rw [hmom] at hi
  calc
    _ = ‖∫ v in a..b, S.QV e u v‖ := by rw [← form.2, Real.norm_eq_abs]
    _ ≤ _ := (intervalIntegral.norm_integral_le_integral_norm hab).trans hi
    _ = _ := by ring

/-- [internal]
Exterior charge profile from the complete-core gap, the exterior scalar
profile, and the explicit boundary budget `m_b/b ≤ F²`,
charged_SF_new_version.tex:L3350–L3360. The constant is chosen from `δ` alone before
all solution data. The stopped-geometry consumer supplies the scalar
profile and the stage budget; no derivative stop is imposed in the core. -/
theorem ct_charge_profile_of_scalar_bound (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (e M₀ F : ℝ) (S : Fields) (D : Set (ℝ × ℝ)) (u a b : ℝ),
      IsSolution e S D → u < a → a ≤ b → outSeg u u b ⊆ D → 1 ≤ M₀ → 0 ≤ F → F ≤ 1 →
      (∀ v ∈ Icc u b, δ ≤ 1 - S.mu u v) →
      (∀ v ∈ Icc a b, ‖S.phi u v‖ ≤ M₀) →
      (∀ v ∈ Icc a b, ‖S.theta u v / S.lam u v‖ ≤ F) →
      S.m u a / S.r u a ≤ F ^ 2 →
      |S.Q u b| / S.r u b ^ 2 ≤ C * |e| * M₀ * F := by
  obtain ⟨C, hC, hbound⟩ := ct_boundary_charge_of_boundary_bound δ hδ hδ1
  refine ⟨2 * C + 1, by positivity, ?_⟩
  intro e M₀ F S D u a b hS hua hab hs hM hF hF1 hgap hphi hy hbudget
  have hsa : outSeg u u a ⊆ D := fun p hp => hs ⟨hp.1, hp.2.1, hp.2.2.trans hab⟩
  have hsb : outSeg u a b ⊆ D := fun p hp => hs ⟨hp.1, hua.le.trans hp.2.1, hp.2.2⟩
  have hra := hS.r_pos (u, a) (hsa ⟨rfl, hua.le, le_rfl⟩) hua
  have hrb := hS.r_pos (u, b) (hs ⟨rfl, (hua.trans_le hab).le, le_rfl⟩) (hua.trans_le hab)
  have hM0 : 0 ≤ M₀ := le_trans (by norm_num) hM
  have hflux := Local.RelCharge.mass_controls_radial_flux hS hua hsa
  have hn := intervalIntegral.integral_nonneg hua.le (μ := volume) (fun v hv =>
    mul_nonneg (mul_nonneg (hS.lam_pos (u, v) (hsa ⟨rfl, hv⟩)).le
      (hS.one_sub_mu_pos (u, v) (hsa ⟨rfl, hv⟩)).le) (sq_nonneg ‖S.theta u v / S.lam u v‖))
  have hm : 0 ≤ S.m u a := by linarith only [hflux, hn]
  have hη : 0 ≤ S.m u a / S.r u a := div_nonneg hm hra.le
  have hroot : Real.sqrt (S.m u a / S.r u a) ≤ F :=
    (Real.sqrt_le_left hF).mpr hbudget
  have hηF : S.m u a / S.r u a ≤ F :=
    hbudget.trans (by nlinarith only [mul_le_mul_of_nonneg_left hF1 hF])
  have hinner : M₀ * Real.sqrt (S.m u a / S.r u a) + S.m u a / S.r u a ≤ 2 * M₀ * F := by
    have h1 := mul_le_mul_of_nonneg_left hroot hM0
    have h2 := mul_le_mul_of_nonneg_right hM hF
    nlinarith only [h1, h2, hηF]
  have hqa := (hbound e M₀ S D u a hS hua hsa
    (fun v hv => hgap v ⟨hv.1, hv.2.trans hab⟩) (hphi a ⟨le_rfl, hab⟩)).trans
    (mul_le_mul_of_nonneg_left hinner (mul_nonneg hC.le (abs_nonneg e)))
  have hqa' : |S.Q u a| ≤ (2 * C * |e| * M₀ * F) * S.r u a ^ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hra)).mp
    convert hqa using 1
    ring
  have hrad := (hS.eq_out u a b hua hab hsb).1
  have hnrad := intervalIntegral.integral_nonneg hab (μ := volume) (fun v hv =>
    (hS.lam_pos (u, v) (hsb ⟨rfl, hv⟩)).le)
  rw [← hrad.2] at hnrad
  have hrsq : S.r u a ^ 2 ≤ S.r u b ^ 2 := pow_le_pow_left₀ hra.le (by linarith only [hnrad]) 2
  have hqa'' := hqa'.trans (mul_le_mul_of_nonneg_left hrsq (by positivity))
  have hinc := charge_increment hS hua hab hsb hM0 hF hphi hy
  have hinc' : |S.Q u b - S.Q u a| ≤ (|e| * M₀ * F) * S.r u b ^ 2 / 2 :=
    hinc.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (sub_le_self _ (sq_nonneg _)) (by positivity)) (by norm_num))
  have htri : |S.Q u b| ≤ |S.Q u a| + |S.Q u b - S.Q u a| := by
    simpa only [Real.norm_eq_abs] using norm_le_norm_add_norm_sub' (S.Q u b) (S.Q u a)
  apply (div_le_iff₀ (sq_pos_of_pos hrb)).mpr
  have hpos : 0 ≤ |e| * M₀ * F * S.r u b ^ 2 := by positivity
  nlinarith only [htri, hqa'', hinc', hpos]

end EmcsfAcExtension.Global
