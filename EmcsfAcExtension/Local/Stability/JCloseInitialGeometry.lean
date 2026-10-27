module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Local.Calculus.AxisRatio
import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # Initial common geometry and the mass factor

The initial radius gauge fixes the common expansion. Nonnegative radial
mass supplies the upper bound on the scalar optical factor.
-/

public section

open Set MeasureTheory Filter Topology Complex

namespace EmcsfAcExtension.Local.Stab

/-- The Hawking mass is nonnegative from the regular axis along an
outgoing segment. This uses the literal positive radial mass constraint. -/
theorem stab_mass_nonneg {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) : 0 ≤ S.m u v := by
  have hc : ContinuousOn (S.m u) (Icc u v) := hS.c1_m.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn
    (show MapsTo (fun x => (u, x)) (Icc u v) (triangle 0 T) from
      fun x hx => ⟨hu, hx.1, hx.2.trans hvT⟩)
  have hd (x : ℝ) (hx : x ∈ Ioo u v) : HasDerivAt (S.m u) (S.mV u x) x := by
    have hp : (u, x) ∈ triangle 0 T := ⟨hu, hx.1.le, hx.2.le.trans hvT⟩
    have hh := hasDerivWithinAt_pdV hS.c1_m hp
      (show MapsTo (fun x => (u, x)) (Icc u v) (triangle 0 T) from
        fun x hx => ⟨hu, hx.1, hx.2.trans hvT⟩)
    rw [(hS.eq_v (u, x) hp hx.1).2.2.1] at hh
    exact hh.hasDerivAt (Icc_mem_nhds hx.1 hx.2)
  have hm : MonotoneOn (S.m u) (Icc u v) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc u v) hc
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hd x hx).deriv]
      have hμ := hS.one_sub_mu_pos (u, x) ⟨hu, hx.1.le, hx.2.le.trans hvT⟩
      have hlam := hS.lam_pos (u, x) ⟨hu, hx.1.le, hx.2.le.trans hvT⟩
      unfold Fields.mV
      positivity
  have hh := hm ⟨le_rfl, huv⟩ ⟨huv, le_rfl⟩ huv
  rwa [(hS.axis u ⟨hu, le_rfl, huv.trans hvT⟩).2.1] at hh

/-- The initial radius gauge fixes the outgoing expansion to `1/2` on the
whole closed initial section. No smallness assumption is required. -/
theorem initial_lam_of_stabSetting {e s ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e s ε M A S h)
    {v : ℝ} (hv : v ∈ Icc 0 s) : S.lam 0 v = 1 / 2 := by
  have hs : MapsTo (fun x => (0, x)) (Icc 0 s) (triangle 0 s) :=
    fun x hx => ⟨le_rfl, hx.1, hx.2⟩
  have hinner : EqOn (S.lam 0) (fun _ => 1 / 2) (Ioo 0 s) := by
    intro x hx
    have hd := hasDerivWithinAt_pdV hset.c1.c1_r (hs ⟨hx.1.le, hx.2.le⟩) hs
    rw [(hset.c1.eq_v (0, x) (hs ⟨hx.1.le, hx.2.le⟩) hx.1).1] at hd
    have hg : HasDerivWithinAt (S.r 0) (1 / 2) (Icc 0 s) x := by
      exact ((hasDerivAt_id x).div_const 2).hasDerivWithinAt.congr_of_mem
        (fun y hy => (hset.data.1 y hy).1) ⟨hx.1.le, hx.2.le⟩
    exact (hd.hasDerivAt (Icc_mem_nhds hx.1 hx.2)).unique
      (hg.hasDerivAt (Icc_mem_nhds hx.1 hx.2))
  have cl := hset.c1.c1_lam.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hs
  exact hinner.of_subset_closure cl continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo hset.pos.ne]) hv

/-- The initial optical factor lies in `(0,1]`. The upper endpoint is
obtained from the radial mass constraint, including the totalized axis. -/
theorem initial_gamma_le_one {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hs : StabSetting e T ε M A S h) {v : ℝ} (hv : v ∈ Icc 0 T) :
    0 < 1 - S.mu 0 v ∧ 1 - S.mu 0 v ≤ 1 := by
  have hp : (0, v) ∈ triangle 0 T := ⟨le_rfl, hv.1, hv.2⟩
  have hr : 0 ≤ S.r 0 v := by
    rw [(hs.data.1 v hv).1]
    exact div_nonneg hv.1 (by norm_num)
  have hm := stab_mass_nonneg hs.c1 le_rfl hv.1 hv.2
  have hμ : 0 ≤ S.mu 0 v := div_nonneg (mul_nonneg (by norm_num) hm) hr
  exact ⟨hs.c1.one_sub_mu_pos (0, v) hp, by linarith only [hμ]⟩

end EmcsfAcExtension.Local.Stab
