module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.SmoothSupRadial
import EmcsfAcExtension.Local.Apriori.Mass
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Calculus.RelativeCharge
import EmcsfAcExtension.Local.Calculus.C1ToSolution2
import EmcsfAcExtension.Local.Calculus.Partials

/-! # Quantitative center orders from a scalar derivative budget

The outgoing charge constraint and the positive mass constraint turn linear
scalar decay into cubic charge and mass bounds. Constants retain their
dependence on the scalar size, coupling, background and total cone length.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local

/-- Linear outgoing scalar decay gives cubic charge, with universal
coefficient two. The scalar size `D` is explicit; no compactness constant
or higher derivative of the particular solution enters this estimate. -/
theorem smooth_charge_cubic_of_bound {e T ε M D : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) (hD : 0 ≤ D)
    (hdecay : ∀ q ∈ triangle 0 T,
      ‖S.theta q.1 q.2 / S.lam q.1 q.2‖ ≤ D * S.r q.1 q.2)
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 T) :
    |S.Q u v| ≤ 2 * |e| * M * D * S.r u v ^ 3 := by
  have hS := hset.c1.toIsSolution hset.pos
  have hb := Stab.oscillatory_charge_bound hS hp.2.1
    (show outSeg u u v ⊆ triangle 0 T from fun q hq => by
      rcases hq with ⟨rfl, hq⟩
      exact ⟨hp.1, hq.1, hq.2.trans hp.2.2⟩)
    (fun x hx => (hset.box (u, x) ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩).2.2.2.2.2.1)
    (ε := 4 * D * S.r u v) (fun x hx => by
      have hpx : (u, x) ∈ triangle 0 T := ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩
      apply (hdecay (u, x) hpx).trans
      have hr := (smooth_radius_bounds_aux hset hpx).2
      have hr' := (smooth_radius_bounds_aux hset hp).1
      have hs : S.r u x ≤ 4 * S.r u v := by linarith only [hr, hr', hx.2]
      nlinarith only [mul_le_mul_of_nonneg_left hs hD])
  convert hb using 1; ring

/-- Cubic charge yields a quadratic electric ratio with the explicit
coefficient `4 e² M² D² T²`, uniformly in the field and datum. -/
theorem smooth_charge_square_of_bound {e T ε M D : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) (hD : 0 ≤ D)
    (hdecay : ∀ q ∈ triangle 0 T,
      ‖S.theta q.1 q.2 / S.lam q.1 q.2‖ ≤ D * S.r q.1 q.2)
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 T) :
    S.Q u v ^ 2 / S.r u v ^ 2 ≤
      4 * e ^ 2 * M ^ 2 * D ^ 2 * T ^ 2 * S.r u v ^ 2 := by
  have hr0 := hset.radius_nonneg hp
  have hrT : S.r u v ≤ T :=
    ((smooth_radius_bounds_aux hset hp).2).trans (by linarith only [hp.1, hp.2.2])
  by_cases hr : S.r u v = 0
  · simp only [hr, zero_pow (by decide : 2 ≠ 0), div_zero, mul_zero, le_refl]
  have hq := pow_le_pow_left₀ (abs_nonneg (S.Q u v))
    (smooth_charge_cubic_of_bound hset hD hdecay hp) 2
  rw [sq_abs] at hq
  have hq' : S.Q u v ^ 2 / S.r u v ^ 2 ≤
      4 * e ^ 2 * M ^ 2 * D ^ 2 * S.r u v ^ 4 := by
    apply (div_le_iff₀ (sq_pos_of_ne_zero hr)).mpr
    convert hq using 1; simp only [mul_pow, sq_abs]; ring
  apply hq'.trans
  have hs := pow_le_pow_left₀ hr0 hrT 2
  have hi := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ 4 * e ^ 2 * M ^ 2 * D ^ 2 * S.r u v ^ 2 by positivity)
  nlinarith only [hi]

private theorem mass_derivative_bound {e T ε M D : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) (hD : 0 ≤ D)
    (hdecay : ∀ q ∈ triangle 0 T,
      ‖S.theta q.1 q.2 / S.lam q.1 q.2‖ ≤ D * S.r q.1 q.2)
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 T) :
    S.mV u v ≤ (D ^ 2 + 4 * e ^ 2 * M ^ 2 * D ^ 2 * T ^ 2) *
      S.lam u v * S.r u v ^ 2 := by
  have hl := hset.c1.lam_pos (u, v) hp
  have hm := hset.mu_nonneg hp
  have hd := hset.c1.one_sub_mu_pos (u, v) hp
  have hq := smooth_charge_square_of_bound hset hD hdecay hp
  have hf := pow_le_pow_left₀ (norm_nonneg _) (hdecay (u, v) hp) 2
  rw [mul_pow] at hf
  have heq : S.mV u v = S.lam u v / 2 *
      ((1 - S.mu u v) * ‖S.theta u v / S.lam u v‖ ^ 2 +
        S.Q u v ^ 2 / S.r u v ^ 2) := by
    simp only [Fields.mV, norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
    field_simp [hl.ne']
  rw [heq]
  calc
    _ ≤ S.lam u v / 2 *
        (1 * (D ^ 2 * S.r u v ^ 2) +
          4 * e ^ 2 * M ^ 2 * D ^ 2 * T ^ 2 * S.r u v ^ 2) := by
      gcongr
      linarith only [hm]
    _ ≤ _ := by
      have hh : 0 ≤ (D ^ 2 + 4 * e ^ 2 * M ^ 2 * D ^ 2 * T ^ 2) *
          S.lam u v * S.r u v ^ 2 := by positivity
      nlinarith only [hh]

/-- The center mass ratio has an explicit quadratic bound derived from
linear outgoing scalar decay. Its coefficient depends only on the
displayed `e,M,T,D`, uniformly in the datum, solution and apex.
The mass itself has the corresponding cubic bound. -/
theorem smooth_mass_center_of_bound {e T ε M D : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) (hD : 0 ≤ D)
    (hdecay : ∀ q ∈ triangle 0 T,
      ‖S.theta q.1 q.2 / S.lam q.1 q.2‖ ≤ D * S.r q.1 q.2)
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 T) :
    S.m u v ≤ (D ^ 2 + 4 * e ^ 2 * M ^ 2 * D ^ 2 * T ^ 2) * S.r u v ^ 3 ∧
      S.mu u v ≤ 2 * (D ^ 2 + 4 * e ^ 2 * M ^ 2 * D ^ 2 * T ^ 2) * S.r u v ^ 2 := by
  let C := D ^ 2 + 4 * e ^ 2 * M ^ 2 * D ^ 2 * T ^ 2
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hs : MapsTo (fun x => (u, x)) (Icc u v) (triangle 0 T) :=
    fun x hx => ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩
  have cr := hset.c1.c1_r.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hs
  have cm := hset.c1.c1_m.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hs
  let F (x : ℝ) := C * S.r u x ^ 3 - S.m u x
  have hd (x : ℝ) (hx : x ∈ Ioo u v) :
      HasDerivAt F (3 * C * S.lam u x * S.r u x ^ 2 - S.mV u x) x := by
    have hxp := hs ⟨hx.1.le, hx.2.le⟩
    have dr := (hasDerivWithinAt_pdV hset.c1.c1_r hxp hs).hasDerivAt
      (Icc_mem_nhds hx.1 hx.2)
    have dm := (hasDerivWithinAt_pdV hset.c1.c1_m hxp hs).hasDerivAt
      (Icc_mem_nhds hx.1 hx.2)
    rw [(hset.c1.eq_v (u, x) hxp hx.1).1] at dr
    rw [(hset.c1.eq_v (u, x) hxp hx.1).2.2.1] at dm
    convert ((dr.pow 3).const_mul C).sub dm using 1; ring
  have hmono : MonotoneOn F (Icc u v) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc u v) (((cr.pow 3).const_mul C).sub cm)
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      change 0 ≤ deriv F x
      rw [(hd x hx).deriv]
      have hb := mass_derivative_bound hset hD hdecay (hs ⟨hx.1.le, hx.2.le⟩)
      have hn : 0 ≤ C * S.lam u x * S.r u x ^ 2 := by
        have hl := hset.c1.lam_pos (u, x) (hs ⟨hx.1.le, hx.2.le⟩)
        positivity
      change S.mV u x ≤ C * S.lam u x * S.r u x ^ 2 at hb
      linarith only [hb, hn]
  have hm := hmono ⟨le_rfl, hp.2.1⟩ ⟨hp.2.1, le_rfl⟩ hp.2.1
  have ha := hset.c1.axis u ⟨hp.1, le_rfl, hp.2.1.trans hp.2.2⟩
  dsimp only [F] at hm
  rw [ha.1, ha.2.1] at hm
  norm_num only [zero_pow, mul_zero, sub_zero] at hm
  have hm' : S.m u v ≤ C * S.r u v ^ 3 := by linarith only [hm]
  refine ⟨hm', ?_⟩
  by_cases hr : S.r u v = 0
  · simp only [Fields.mu, hr, div_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, le_refl]
  have hrp : 0 < S.r u v := lt_of_le_of_ne (hset.radius_nonneg hp) (Ne.symm hr)
  change 2 * S.m u v / S.r u v ≤ 2 * C * S.r u v ^ 2
  apply (div_le_iff₀ hrp).mpr
  nlinarith only [hm']

end EmcsfAcExtension.Local
