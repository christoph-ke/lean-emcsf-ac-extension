module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.FluxDifferenceRegularity
import EmcsfAcExtension.Local.Calculus.Raychaudhuri
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Incoming optical reconstruction from the initial cone

The first Raychaudhuri integration starts on `u=0`. Its exponential
decays along the incoming coordinate, retaining the nonzero initial
mass comparison and avoiding an unabsorbed axis value.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

/-- Incoming optical reconstruction from the initial cone, with the
negative quadratic exponent and its initial mass factor retained.
This is an exact identity with no estimate constant or smallness
assumption beyond the classical stability setting. -/
theorem stab_in_optical_from_initial
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    S.lam u v / (1 - S.mu u v) = S.lam 0 v / (1 - S.mu 0 v) *
      Real.exp (-(∫ s in 0..u, (-S.nu s v) / S.r s v *
        ‖S.xi s v / (S.nu s v : ℂ)‖ ^ 2)) := by
  let F := fun s => (-S.nu s v) / S.r s v * ‖S.xi s v / (S.nu s v : ℂ)‖ ^ 2
  have hmap : MapsTo (fun s : ℝ => (s, v)) (Icc 0 u) (triangle 0 T) :=
    fun s hs => ⟨hs.1, hs.2.trans huv, hvT⟩
  have cG : ContinuousOn (fun p : ℝ × ℝ => 1 - S.mu p.1 p.2) (triangle 0 T) :=
    continuousOn_const.sub (continuousOn_mu_aux hset.pos hset.c1)
  have cOpt := hset.c1.c1_lam.continuousOn.div cG
    (fun p hp => (hset.c1.one_sub_mu_pos p hp).ne')
  have hOpt : ∀ p ∈ triangle 0 T, 0 < S.lam p.1 p.2 / (1 - S.mu p.1 p.2) :=
    fun p hp => div_pos (hset.c1.lam_pos p hp) (hset.c1.one_sub_mu_pos p hp)
  have cLog : ContinuousOn (fun s => Real.log (S.lam s v / (1 - S.mu s v))) (Icc 0 u) :=
    (cOpt.log (fun p hp => (hOpt p hp).ne')).comp
      (continuous_id.prodMk continuous_const).continuousOn hmap
  have cF : ContinuousOn F (Icc 0 u) := (stab_in_quadratic_flux_continuous hset).comp
    (continuous_id.prodMk continuous_const).continuousOn hmap
  have hd : ∀ s ∈ Ioo 0 u, HasDerivAt
      (fun t => Real.log (S.lam t v / (1 - S.mu t v))) (-F s) s := by
    intro s hs
    apply ((eq_ray_in hset.c1 hs.1.le (hs.2.trans_le huv) hvT).hasDerivAt
      (Icc_mem_nhds hs.1 (hs.2.trans_le huv))).congr_deriv
    dsimp only [F]
    rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hn := (hset.c1.nu_neg (s, v) ⟨hs.1.le, (hs.2.trans_le huv).le, hvT⟩).ne
    have hr := (hset.c1.r_pos (s, v) ⟨hs.1.le, (hs.2.trans_le huv).le, hvT⟩
      (hs.2.trans_le huv)).ne'
    field_simp
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu cLog hd
    (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hu cF.neg)
  rw [intervalIntegral.integral_neg] at hi
  have hlog : Real.log (S.lam u v / (1 - S.mu u v)) =
      Real.log (S.lam 0 v / (1 - S.mu 0 v)) + (-(∫ s in 0..u, F s)) := by
    linarith only [hi]
  have he := congrArg Real.exp hlog
  rw [Real.exp_log (hOpt (u, v) ⟨hu, huv, hvT⟩), Real.exp_add,
    Real.exp_log (hOpt (0, v) ⟨le_rfl, hu.trans huv, hvT⟩)] at he
  exact he

end EmcsfAcExtension.Local
