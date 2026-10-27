module

public import EmcsfAcExtension.Global.Interaction.BoundaryCharge
import EmcsfAcExtension.Local.Calculus.RelativeCharge
import EmcsfAcExtension.Local.Calculus.Reconstruction
import EmcsfAcExtension.Global.Calculus.Sections

/-! # The full boundary Maxwell comparison chain

Both Cauchy–Schwarz factors are retained before the mass and weighted core
scalar bounds are inserted. Source: `charged_SF_new_version.tex:L3334–L3343`.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global

/-- [internal] Boundary charge-square with the explicit Maxwell factors.
The constant depends only on `δ`, before coupling, background, and solution.
The stopped-envelope consumer supplies the boundary scalar bound. -/
theorem ct_boundary_charge_square_chain_of_boundary_bound (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (e M₀ : ℝ) (S : Fields) (D : Set (ℝ × ℝ)) (u b : ℝ),
      IsSolution e S D → u < b → outSeg u u b ⊆ D →
      (∀ v ∈ Icc u b, δ ≤ 1 - S.mu u v) → ‖S.phi u b‖ ≤ M₀ →
      S.Q u b ^ 2 ≤ e ^ 2 *
          (∫ v in u..b, S.lam u v * (1 - S.mu u v) * ‖S.theta u v / S.lam u v‖ ^ 2) *
          (∫ v in u..b, S.lam u v * S.r u v ^ 2 * ‖S.phi u v‖ ^ 2 / (1 - S.mu u v)) ∧
        e ^ 2 *
          (∫ v in u..b, S.lam u v * (1 - S.mu u v) * ‖S.theta u v / S.lam u v‖ ^ 2) *
          (∫ v in u..b, S.lam u v * S.r u v ^ 2 * ‖S.phi u v‖ ^ 2 / (1 - S.mu u v)) ≤
        C * e ^ 2 * S.m u b * (M₀ ^ 2 * S.r u b ^ 3 + S.m u b * S.r u b ^ 2) := by
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
  have hBn : 0 ≤ ∫ v in u..b,
      S.lam u v * S.r u v ^ 2 * ‖S.phi u v‖ ^ 2 / (1 - S.mu u v) :=
    intervalIntegral.integral_nonneg hub.le (fun v hv =>
      div_nonneg (mul_nonneg (mul_nonneg (hS.lam_pos (u, v) (hp v hv)).le
        (sq_nonneg _)) (sq_nonneg _)) (hS.one_sub_mu_pos (u, v) (hp v hv)).le)
  have hcharge := (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Local.RelCharge.mass_controls_radial_flux hS hub hs)
      (sq_nonneg e)) hBn).trans
      (mul_le_mul_of_nonneg_left hB (mul_nonneg (sq_nonneg e)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hm)))
  have hcoeff : 4 / (3 * δ) ≤ 4 / δ ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hδ)
      (by nlinarith only [hδ.le, mul_le_mul_of_nonneg_left hδ1 hδ.le])
  refine ⟨Local.RelCharge.maxwell_cauchy_schwarz hS hub hs, ?_⟩
  calc
    _ ≤ _ := hcharge
    _ = 4 / (3 * δ) * (e ^ 2 * S.m u b * M₀ ^ 2 * S.r u b ^ 3) +
        (4 / δ ^ 2) * (e ^ 2 * S.m u b ^ 2 * S.r u b ^ 2) := by
      field_simp [(hS.r_pos (u, b) (hp b ⟨hub.le, le_rfl⟩) hub).ne']
      ring
    _ ≤ (4 / δ ^ 2) * (e ^ 2 * S.m u b * M₀ ^ 2 * S.r u b ^ 3) +
        (4 / δ ^ 2) * (e ^ 2 * S.m u b ^ 2 * S.r u b ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_right hcoeff
        (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg e) hm) (sq_nonneg M₀))
          (pow_nonneg (hr b ⟨hub.le, le_rfl⟩) 3))) le_rfl
    _ = _ := by ring

end EmcsfAcExtension.Global
