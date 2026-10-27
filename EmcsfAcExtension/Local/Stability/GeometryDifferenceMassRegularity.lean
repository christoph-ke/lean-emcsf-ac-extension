module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeometryDifferenceOptical
import EmcsfAcExtension.Local.Stability.FluxDifferenceRegularity
import EmcsfAcExtension.Infra.AC.Quotient

/-! # Mass-ratio AC through the regular axis

Solving the exact optical identities for the mass gap expresses it as
a product of a classical expansion and an exponential of an integral
of a continuous quadratic flux. This establishes AC without imposing
an additional endpoint regularity hypothesis.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

private theorem mass_gap_solve_aux {n l γ I : ℝ}
    (hl : l ≠ 0) (hγ : γ ≠ 0) (hopt : n / γ = l * Real.exp I) :
    γ = n / l * Real.exp (-I) := by
  have heq := (div_eq_iff hγ).mp hopt
  rw [Real.exp_neg, ← div_eq_mul_inv, div_div]
  apply (eq_div_iff (mul_ne_zero hl (Real.exp_ne_zero I))).mpr
  calc
    γ * (l * Real.exp I) = l * Real.exp I * γ := by ring
    _ = n := heq.symm

/-- The literal mass ratio is AC on complete outgoing sections of a
classical stability setting. This is an exact regularity statement;
there is no estimate constant, size assumption or radius cutoff. -/
theorem stab_mu_out_ac
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    AbsolutelyContinuousOnInterval (S.mu u) u v := by
  let F := fun s => S.lam u s / S.r u s * ‖S.theta u s / (S.lam u s : ℂ)‖ ^ 2
  have hmap : MapsTo (fun s : ℝ => (u, s)) (Icc u v) (triangle 0 T) :=
    fun s hs => ⟨hu, hs.1, hs.2.trans hvT⟩
  have cF : ContinuousOn F (Icc u v) := (stab_out_quadratic_flux_continuous hset).comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have hI := (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv cF)
    |>.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hN : AbsolutelyContinuousOnInterval (fun s => -S.nu u s / S.lam u u) u v := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le huv]
    exact ((hset.c1.c1_nu.comp
      (contDiffOn_const.prodMk contDiffOn_id) hmap).neg).div_const _
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) u v :=
    (LipschitzWith.const 1).lipschitzOnWith.absolutelyContinuousOnInterval
  apply (hconst.sub (hN.mul_normed_ring hI.neg.exp)).congr
  intro s hs
  have hs' : s ∈ Icc u v := by simpa only [uIcc_of_le huv] using hs
  have haxis : (u, u) ∈ triangle 0 T := ⟨hu, le_rfl, huv.trans hvT⟩
  have hg := mass_gap_solve_aux (hset.c1.lam_pos (u, u) haxis).ne'
    (hset.c1.one_sub_mu_pos (u, s) (hmap hs')).ne'
    (stab_out_optical_from_axis hset hu hs'.1 (hs'.2.trans hvT))
  change 1 - (-S.nu u s / S.lam u u * Real.exp (-(∫ t in u..s, F t))) = S.mu u s
  dsimp only [F]
  linarith only [hg]

/-- The mass ratio is AC on complete incoming sections, in the
original increasing null label. The exact terminal-axis optical
identity supplies the endpoint, with no estimate constant or cutoff. -/
theorem stab_mu_in_ac
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    AbsolutelyContinuousOnInterval (fun s => S.mu s v) u v := by
  let F := fun s => -S.nu s v / S.r s v * ‖S.xi s v / (S.nu s v : ℂ)‖ ^ 2
  have hmap : MapsTo (fun s : ℝ => (s, v)) (Icc u v) (triangle 0 T) :=
    fun s hs => ⟨hu.trans hs.1, hs.2, hvT⟩
  have cF : ContinuousOn F (Icc u v) := (stab_in_quadratic_flux_continuous hset).comp
    (continuous_id.prodMk continuous_const).continuousOn hmap
  have hI := (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv cF)
    |>.absolutelyContinuousOnInterval_intervalIntegral right_mem_uIcc
  have hN : AbsolutelyContinuousOnInterval (fun s => S.lam s v / S.lam v v) u v := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le huv]
    exact (hset.c1.c1_lam.comp
      (contDiffOn_id.prodMk contDiffOn_const) hmap).div_const _
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) u v :=
    (LipschitzWith.const 1).lipschitzOnWith.absolutelyContinuousOnInterval
  apply (hconst.sub (hN.mul_normed_ring hI.exp)).congr
  intro s hs
  have hs' : s ∈ Icc u v := by simpa only [uIcc_of_le huv] using hs
  have haxis : (v, v) ∈ triangle 0 T := ⟨hu.trans huv, le_rfl, hvT⟩
  have hg := mass_gap_solve_aux (hset.c1.lam_pos (v, v) haxis).ne'
    (hset.c1.one_sub_mu_pos (s, v) (hmap hs')).ne'
    (stab_in_optical_from_axis hset (hu.trans hs'.1) hs'.2 hvT)
  change 1 - (S.lam s v / S.lam v v * Real.exp (∫ t in v..s, F t)) = S.mu s v
  rw [intervalIntegral.integral_symm]
  dsimp only [F]
  linarith only [hg]

end EmcsfAcExtension.Local
