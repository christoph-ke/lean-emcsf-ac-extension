module

public import EmcsfAcExtension.Local.Defs.Limit
public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Infra.Calculus.PartialsC1

/-! # Pointwise consequences of constructed-limit comparison settings

The fixed geometric box makes normalized scalar quotients and the relative
radius comparison continuous in the strong primary-field limits.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

private theorem radius_lower_of_setting {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hs : StabSetting e T ε M A S h) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ T) : (v - u) / 4 ≤ S.r u v := by
  have hr : ContinuousOn (S.r u) (Icc u v) :=
    hs.c1.c1_r.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s hmem => ⟨hu, hmem.1, hmem.2.trans hv⟩)
  have hl : ContinuousOn (S.lam u) (Icc u v) :=
    hs.c1.c1_lam.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s hmem => ⟨hu, hmem.1, hmem.2.trans hv⟩)
  have hli : IntervalIntegrable (S.lam u) volume u v := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le huv] using hl
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv hr
    (fun s hmem => by
      have hp : (u, s) ∈ triangle 0 T := ⟨hu, hmem.1.le, hmem.2.le.trans hv⟩
      have hd := hasDerivWithinAt_uncurry_triangle_v hs.c1.c1_r hp
      change HasDerivWithinAt (S.r u) (pdV (triangle 0 T) S.r u s) (Icc u T) s at hd
      rw [(hs.c1.eq_v (u, s) hp hmem.1).1] at hd
      exact hd.hasDerivAt (Icc_mem_nhds hmem.1 (hmem.2.trans_le hv))) hli
  rw [(hs.c1.axis u ⟨hu, le_rfl, huv.trans hv⟩).1, sub_zero] at hi
  have hb := intervalIntegral.integral_mono_on huv intervalIntegrable_const hli
    (fun s hmem => (hs.box.2 (u, s) ⟨hu, hmem.1, hmem.2.trans hv⟩).1)
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_one_div, hi] using hb

/-- Pointwise convergence of the outgoing normalized scalar when the limit
expansion is nonzero. This is a transport helper for an existing strong limit. -/
theorem StrongLimit.tendsto_a_of_lam_ne_zero {e T : ℝ} {Sn : ℕ → Fields} {S : Fields}
    (hlim : StrongLimit e T Sn S) {p : ℝ × ℝ} (hp : p ∈ triangle 0 T)
    (hl : S.lam p.1 p.2 ≠ 0) :
    Tendsto (fun n => (Sn n).a p.1 p.2) atTop (𝓝 (S.a p.1 p.2)) := by
  have hlc := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (hlim.unif_lam.tendsto_at hp)
  exact (hlim.unif_phi.tendsto_at hp).add
    ((hlim.unif_theta.tendsto_at hp).div hlc (Complex.ofReal_ne_zero.mpr hl))

/-- Pointwise convergence of the incoming normalized scalar when the limit
expansion is nonzero, without a covariant derivative assumption. -/
theorem StrongLimit.tendsto_b_of_nu_ne_zero {e T : ℝ} {Sn : ℕ → Fields} {S : Fields}
    (hlim : StrongLimit e T Sn S) {p : ℝ × ℝ} (hp : p ∈ triangle 0 T)
    (hn : S.nu p.1 p.2 ≠ 0) :
    Tendsto (fun n => (Sn n).b p.1 p.2) atTop (𝓝 (S.b p.1 p.2)) := by
  have hnc := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (hlim.unif_nu.tendsto_at hp)
  exact (hlim.unif_phi.tendsto_at hp).add
    ((hlim.unif_xi.tendsto_at hp).div hnc (Complex.ofReal_ne_zero.mpr hn))

/-- Retain the numerical expansion and radial lower bounds of a common
classical comparison setting. The constants are the fixed `1/4` box values. -/
theorem StrongLimit.lower_geometry_of_settings {e T ε M A : ℝ} {Sn : ℕ → Fields}
    {hn : ℕ → ℝ → ℂ} {S : Fields} (hlim : StrongLimit e T Sn S)
    (hs : ∀ n, StabSetting e T ε M A (Sn n) (hn n)) :
    ∀ p ∈ triangle 0 T, 1 / 4 ≤ S.lam p.1 p.2 ∧ 1 / 4 ≤ -S.nu p.1 p.2 ∧
      (p.2 - p.1) / 4 ≤ S.r p.1 p.2 := by
  intro p hp
  exact ⟨ge_of_tendsto (hlim.unif_lam.tendsto_at hp)
      (Eventually.of_forall fun n => ((hs n).box.2 p hp).1),
    ge_of_tendsto (hlim.unif_nu.tendsto_at hp).neg
      (Eventually.of_forall fun n => ((hs n).box.2 p hp).2.2.1),
    ge_of_tendsto (hlim.unif_r.tendsto_at hp)
      (Eventually.of_forall fun n => radius_lower_of_setting (hs n) hp.1 hp.2.1 hp.2.2)⟩

/-- The radius stays zero on the axis in an existing classical strong limit.
No quantitative constant or nondegeneracy condition is needed. -/
theorem StrongLimit.axis_radius_of_c1 {e T : ℝ} {Sn : ℕ → Fields} {S : Fields}
    (hlim : StrongLimit e T Sn S)
    (hs : ∀ n, IsC1Solution e (Sn n) (triangle 0 T)) :
    ∀ t ∈ Icc 0 T, S.r t t = 0 := by
  intro t ht
  have hp : (t, t) ∈ triangle 0 T := ⟨ht.1, le_rfl, ht.2⟩
  exact tendsto_nhds_unique (hlim.unif_r.tendsto_at hp)
    (by simpa only [Function.uncurry_apply_pair, fun n => (hs n).axis t hp |>.1] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))

end EmcsfAcExtension.Local
