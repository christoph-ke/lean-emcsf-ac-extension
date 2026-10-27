module

public import EmcsfAcExtension.Local.Defs.Limit
import EmcsfAcExtension.Local.Limit.ExistenceEquations
import EmcsfAcExtension.Local.Limit.ExistenceAC
import EmcsfAcExtension.Local.Limit.UIAux
import EmcsfAcExtension.Local.Calculus.Reconstruction
import EmcsfAcExtension.Infra.BV.Basic

/-! # Closed characteristic AC of the primary Hawking mass

The nontrapped signs make the outgoing mass monotone and the incoming mass
antitone. Continuity and the interior equations give finite variation and
identify an integrable derivative, so endpoint AC follows without any assumed
mass-flux limit.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology

namespace EmcsfAcExtension.Local

private theorem ac_of_density_sign {f q : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hq : ContinuousOn q (Ioo a b))
    (heq : ∀ c d, a < c → c ≤ d → d < b → IntegralForm f q c d)
    (hsign : (∀ x ∈ Ioo a b, 0 ≤ q x) ∨ (∀ x ∈ Ioo a b, q x ≤ 0)) :
    AbsolutelyContinuousOnInterval f a b := by
  have hd x (hx : x ∈ Ioo a b) : HasDerivAt f (q x) x :=
    hasDerivAt_of_integralForm_interior hx hq heq
  have hdiff : DifferentiableOn ℝ f (interior (Icc a b)) := by
    rw [interior_Icc]
    exact fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
  have hbv : BoundedVariationOn f (Icc a b) := by
    rcases hsign with hpos | hneg
    · have hm := monotoneOn_of_deriv_nonneg (convex_Icc a b) hf hdiff (by
        intro x hx
        rw [interior_Icc] at hx
        rw [(hd x hx).deriv]
        exact hpos x hx)
      simpa only [inter_self] using hm.locallyBoundedVariationOn a b
        (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
    · have hm := antitoneOn_of_deriv_nonpos (convex_Icc a b) hf hdiff (by
        intro x hx
        rw [interior_Icc] at hx
        rw [(hd x hx).deriv]
        exact hneg x hx)
      have hmono : MonotoneOn (fun x => -f x) (Icc a b) := fun _ hx _ hy hxy => neg_le_neg (hm hx hy
          hxy)
      have hnegBV : BoundedVariationOn (fun x => -f x) (Icc a b) := by
        simpa only [inter_self] using hmono.locallyBoundedVariationOn a b
          (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
      simpa only [neg_neg] using hnegBV.neg
  apply ac_of_continuous_bv_of_differentiableOn hab hf hbv
  exact fun x hx => (hd x hx).differentiableAt.differentiableWithinAt

/-- Recover full outgoing and incoming AC of the actual limiting Hawking
mass. The signs and uniform mass-ratio limit are the constructed geometry;
no mass derivative convergence or mass AC conclusion is assumed. This
qualitative endpoint argument introduces no numerical constant. -/
theorem StrongLimit.mass_ac_of_c1 {e T : ℝ} {Sn : ℕ → Fields} {S : Fields}
    (hT : 0 < T) (hc1 : ∀ n, IsC1Solution e (Sn n) (triangle 0 T))
    (hlim : StrongLimit e T Sn S)
    (hMu : TendstoUniformlyOn (fun n => Function.uncurry (Sn n).mu)
      (Function.uncurry S.mu) atTop (triangle 0 T))
    (hr : ∀ p ∈ triangle 0 T, p.1 < p.2 → 0 < S.r p.1 p.2)
    (hl : ∀ p ∈ triangle 0 T, 0 < S.lam p.1 p.2)
    (hn : ∀ p ∈ triangle 0 T, S.nu p.1 p.2 < 0)
    (hg : ∀ p ∈ triangle 0 T, 0 < 1 - S.mu p.1 p.2) :
    (∀ u ∈ Icc 0 T, AbsolutelyContinuousOnInterval (S.m u) u T) ∧
    (∀ v ∈ Icc 0 T, AbsolutelyContinuousOnInterval (fun u => S.m u v) 0 v) := by
  obtain ⟨hout, hin⟩ := hlim.integral_equations_of_c1 hT hc1 hr hl hn hg
  have cm := hlim.unif_m.continuousOn (Eventually.of_forall fun n => (hc1
      n).c1_m.continuousOn).frequently
  have cr := hlim.unif_r.continuousOn (Eventually.of_forall fun n => (hc1
      n).c1_r.continuousOn).frequently
  have cl := hlim.unif_lam.continuousOn (Eventually.of_forall fun n => (hc1
      n).c1_lam.continuousOn).frequently
  have cn := hlim.unif_nu.continuousOn (Eventually.of_forall fun n => (hc1
      n).c1_nu.continuousOn).frequently
  have cQ := hlim.unif_Q.continuousOn (Eventually.of_forall fun n => (hc1
      n).c1_Q.continuousOn).frequently
  have ct := hlim.unif_theta.continuousOn (Eventually.of_forall fun n => (hc1
      n).c1_theta.continuousOn).frequently
  have cx := hlim.unif_xi.continuousOn (Eventually.of_forall fun n => (hc1
      n).c1_xi.continuousOn).frequently
  have cMu := hMu.continuousOn (Eventually.of_forall fun n => (hc1 n).continuousOn_mu hT).frequently
  let D := triangle 0 T ∩ {p : ℝ × ℝ | p.1 < p.2}
  have cmV : ContinuousOn (Function.uncurry S.mV) D := by
    have hden p (hp : p ∈ D) : 2 * S.r p.1 p.2 ^ 2 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 2 (hr p hp.1 hp.2).ne')
    simpa only [Fields.mV, Function.uncurry_def] using!
      ((((continuousOn_const (c := (1 : ℝ))).sub (cMu.mono inter_subset_left)).mul
        ((ct.mono inter_subset_left).norm.pow 2)).div
          ((continuousOn_const (c := (2 : ℝ))).mul (cl.mono inter_subset_left))
          (fun p hp => mul_ne_zero (by norm_num) (hl p hp.1).ne')).add
        ((((cQ.mono inter_subset_left).pow 2).mul (cl.mono inter_subset_left)).div
          ((continuousOn_const (c := (2 : ℝ))).mul ((cr.mono inter_subset_left).pow 2)) hden)
  have cmU : ContinuousOn (Function.uncurry S.mU) D := by
    have hden p (hp : p ∈ D) : 2 * S.r p.1 p.2 ^ 2 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 2 (hr p hp.1 hp.2).ne')
    simpa only [Fields.mU, Function.uncurry_def] using!
      ((((continuousOn_const (c := (1 : ℝ))).sub (cMu.mono inter_subset_left)).mul
        ((cx.mono inter_subset_left).norm.pow 2)).div
          ((continuousOn_const (c := (2 : ℝ))).mul (cn.mono inter_subset_left))
          (fun p hp => mul_ne_zero (by norm_num) (hn p hp.1).ne)).add
        ((((cQ.mono inter_subset_left).pow 2).mul (cn.mono inter_subset_left)).div
          ((continuousOn_const (c := (2 : ℝ))).mul ((cr.mono inter_subset_left).pow 2)) hden)
  constructor
  · intro u hu
    have hm : MapsTo (fun x => (u, x)) (Icc u T) (triangle 0 T) := fun x hx => ⟨hu.1, hx.1, hx.2⟩
    apply ac_of_density_sign hu.2 (cm.comp (continuous_const.prodMk continuous_id).continuousOn hm)
      (cmV.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun x hx => ⟨⟨hu.1, hx.1.le, hx.2.le⟩, hx.1⟩))
    · intro a b hua hab hbT
      exact (hout u a b hua hab (by
        rintro ⟨x, y⟩ ⟨rfl, hay, hyb⟩
        exact ⟨hu.1, hua.le.trans hay, hyb.trans hbT.le⟩)).2.2.1
    · left
      intro x hx
      have hp : (u, x) ∈ triangle 0 T := ⟨hu.1, hx.1.le, hx.2.le⟩
      have hpos := hl _ hp
      have hgap := hg _ hp
      change 0 ≤ (1 - S.mu u x) * ‖S.theta u x‖ ^ 2 / (2 * S.lam u x) +
        S.Q u x ^ 2 * S.lam u x / (2 * S.r u x ^ 2)
      exact add_nonneg
        (div_nonneg (mul_nonneg hgap.le (sq_nonneg _))
          (mul_nonneg (by norm_num) hpos.le))
        (div_nonneg (mul_nonneg (sq_nonneg _) hpos.le)
          (mul_nonneg (by norm_num) (sq_nonneg _)))
  · intro v hv
    have hm : MapsTo (fun x => (x, v)) (Icc 0 v) (triangle 0 T) := fun x hx => ⟨hx.1, hx.2, hv.2⟩
    apply ac_of_density_sign hv.1 (cm.comp (continuous_id.prodMk continuous_const).continuousOn hm)
      (cmU.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun x hx => ⟨⟨hx.1.le, hx.2.le, hv.2⟩, hx.2⟩))
    · intro a b h0a hab hbv
      exact (hin a b v hab hbv (by
        rintro ⟨x, y⟩ ⟨hax, hxb, rfl⟩
        exact ⟨h0a.le.trans hax, hxb.trans hbv.le, hv.2⟩)).2.2.1
    · right
      intro x hx
      have hp : (x, v) ∈ triangle 0 T := ⟨hx.1.le, hx.2.le, hv.2⟩
      have hneg := hn _ hp
      have hgap := hg _ hp
      exact add_nonpos
        (div_nonpos_of_nonneg_of_nonpos (mul_nonneg hgap.le (sq_nonneg _))
          (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hneg.le))
        (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hneg.le)
          (mul_nonneg (by norm_num) (sq_nonneg _)))

end EmcsfAcExtension.Local
