module

public import EmcsfAcExtension.Global.Interaction.RadialY
public import EmcsfAcExtension.Global.Interaction.BoundaryCharge
import EmcsfAcExtension.Local.Calculus.RelativeCharge
import EmcsfAcExtension.Local.Calculus.Reconstruction
import EmcsfAcExtension.Global.Calculus.Sections

/-! # The exterior Maxwell primitive with its boundary term

The boundary contribution retains its squared radius ratio before the
uniform charge estimate. Source: `charged_SF_new_version.tex:L3350–L3360`.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global

private theorem charge_increment_for_closure {e M₀ F : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
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

/-- [internal] The full exterior charge comparison chain. The constant
is selected from the full-core gap before all solution data; the consumer
discharges the scalar profile from the stopped derivative envelope. -/
theorem ct_charge_profile_chain_of_scalar_bound (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (e M₀ F : ℝ) (S : Fields) (D : Set (ℝ × ℝ)) (u a b : ℝ),
      IsSolution e S D → u < a → a ≤ b → outSeg u u b ⊆ D → 1 ≤ M₀ → 0 ≤ F → F ≤ 1 →
      (∀ v ∈ Icc u b, δ ≤ 1 - S.mu u v) →
      (∀ v ∈ Icc a b, ‖S.phi u v‖ ≤ M₀) →
      (∀ v ∈ Icc a b, ‖S.theta u v / S.lam u v‖ ≤ F) →
      S.m u a / S.r u a ≤ F ^ 2 →
      |S.Q u b| / S.r u b ^ 2 ≤ C * |e| * M₀ * F * (S.r u a / S.r u b) ^ 2 +
          (|e| * M₀ * F / S.r u b ^ 2) * (∫ v in a..b, S.lam u v * S.r u v) ∧
        C * |e| * M₀ * F * (S.r u a / S.r u b) ^ 2 +
          (|e| * M₀ * F / S.r u b ^ 2) * (∫ v in a..b, S.lam u v * S.r u v) ≤
        C * |e| * M₀ * F := by
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
  let A := |e| * M₀ * F
  let C' := 2 * C + 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC' : (1 / 2 : ℝ) ≤ C' := by dsimp [C']; linarith only [hC]
  have hqa'' : |S.Q u a| ≤ C' * A * S.r u a ^ 2 := by
    have hn : 0 ≤ A * S.r u a ^ 2 := mul_nonneg hA (sq_nonneg _)
    dsimp [C', A]
    nlinarith only [hqa', hn]
  have hinc := charge_increment_for_closure hS hua hab hsb hM0 hF hphi hy
  have hmom := Interaction.radial_moment hS hua hab hsb 1
  norm_num only [pow_one, Nat.reduceAdd, Nat.cast_one] at hmom
  have hinc' : |S.Q u b - S.Q u a| ≤ A * (∫ v in a..b, S.lam u v * S.r u v) := by
    rw [hmom]
    convert hinc using 1
    ring
  have htri : |S.Q u b| ≤ |S.Q u a| + |S.Q u b - S.Q u a| := by
    simpa only [Real.norm_eq_abs] using norm_le_norm_add_norm_sub' (S.Q u b) (S.Q u a)
  have hCA : (2 * C + 1) * |e| * M₀ * F = C' * A := by dsimp [C', A]; ring
  rw [hCA]
  change |S.Q u b| / S.r u b ^ 2 ≤ C' * A * (S.r u a / S.r u b) ^ 2 +
      (A / S.r u b ^ 2) * (∫ v in a..b, S.lam u v * S.r u v) ∧
    C' * A * (S.r u a / S.r u b) ^ 2 +
      (A / S.r u b ^ 2) * (∫ v in a..b, S.lam u v * S.r u v) ≤ C' * A
  constructor
  · calc
      _ ≤ (C' * A * S.r u a ^ 2 + A * (∫ v in a..b, S.lam u v * S.r u v)) /
          S.r u b ^ 2 := div_le_div_of_nonneg_right
            (htri.trans (add_le_add hqa'' hinc')) (sq_nonneg _)
      _ = _ := by field_simp [hrb.ne']
  · have hh := mul_le_mul_of_nonneg_right hC'
      (mul_nonneg hA (sub_nonneg.mpr hrsq))
    have hh' : A * ((S.r u b ^ 2 - S.r u a ^ 2) / 2) ≤
        C' * A * (S.r u b ^ 2 - S.r u a ^ 2) := by convert hh using 1 <;> ring
    rw [hmom]
    calc
      _ = (C' * A * S.r u a ^ 2 + A * ((S.r u b ^ 2 - S.r u a ^ 2) / 2)) /
          S.r u b ^ 2 := by field_simp [hrb.ne']
      _ ≤ (C' * A * S.r u a ^ 2 + C' * A * (S.r u b ^ 2 - S.r u a ^ 2)) /
          S.r u b ^ 2 := div_le_div_of_nonneg_right (add_le_add le_rfl hh')
            (sq_nonneg _)
      _ = _ := by field_simp [hrb.ne']; ring

end EmcsfAcExtension.Global
