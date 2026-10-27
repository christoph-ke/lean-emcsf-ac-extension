module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Calculus.Normalized
import EmcsfAcExtension.Local.Stability.MomentsSections

/-! # Positivity of the classical radial mass

The outgoing mass constraint and its central zero value imply
nonnegative ordinary mass and hence a mass gap at most `1`.
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- The ordinary mass is nonnegative on every complete classical
stability section, from its exact constraint and central value.
There is no estimate constant or smallness hypothesis. -/
theorem stab_mass_nonneg
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) : 0 ≤ S.m u v := by
  have hmap : MapsTo (fun s : ℝ => (u, s)) (Icc u v) (triangle 0 T) :=
    fun s hs => ⟨hu, hs.1, hs.2.trans hvT⟩
  have cm : ContinuousOn (S.m u) (Icc u v) := hset.c1.c1_m.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have hd : ∀ s ∈ Ioo u v, HasDerivAt (S.m u) (S.mV u s) s := by
    intro s hs
    have hp : (u, s) ∈ triangle 0 T := ⟨hu, hs.1.le, hs.2.le.trans hvT⟩
    have hm := hasDerivWithinAt_v_aux hset.c1.c1_m hu hs.1.le (hs.2.le.trans hvT)
    rw [(hset.c1.eq_v (u, s) hp hs.1).2.2.1] at hm
    exact hm.hasDerivAt (Icc_mem_nhds hs.1 (hs.2.trans_le hvT))
  have hmono : MonotoneOn (S.m u) (Icc u v) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc u v) cm
    · intro s hs
      rw [interior_Icc] at hs
      exact (hd s hs).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hd s hs).deriv]
      have hp : (u, s) ∈ triangle 0 T := ⟨hu, hs.1.le, hs.2.le.trans hvT⟩
      have hgap := hset.c1.one_sub_mu_pos (u, s) hp
      have hlam := hset.c1.lam_pos (u, s) hp
      dsimp only [Fields.mV]
      positivity
  have hm := hmono ⟨le_rfl, huv⟩ ⟨huv, le_rfl⟩ huv
  rwa [(hset.c1.axis u ⟨hu, le_rfl, huv.trans hvT⟩).2.1] at hm

/-- The mass ratio is nonnegative throughout the classical stability
triangle, including its literal zero value on the axis. This exact
sign assertion has no estimate constant or smallness assumption. -/
theorem stab_mu_nonneg
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) : 0 ≤ S.mu u v := by
  have hb := (stab_radius_bounds hset hu huv hvT).1
  have hr : 0 ≤ S.r u v := by linarith only [hb, huv]
  exact div_nonneg (mul_nonneg (by norm_num) (stab_mass_nonneg hset hu huv hvT)) hr

end EmcsfAcExtension.Local
