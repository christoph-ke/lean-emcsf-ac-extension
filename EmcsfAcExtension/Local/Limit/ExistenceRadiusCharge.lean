module

public import EmcsfAcExtension.Local.Defs.Limit
import EmcsfAcExtension.Local.Limit.ExistenceEquations
import EmcsfAcExtension.Local.Limit.ExistenceAC

/-! # Closed characteristic AC for radius and charge

The radius densities are continuous expansions. Both Maxwell densities are
polynomials of the primary fields, continuous even at the regular axis.
Interior integral equations therefore recover their closed AC primitives.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology

namespace EmcsfAcExtension.Local

private theorem out_ac {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {T : ℝ} {f q : ℝ → ℝ → E}
    (hf : ContinuousOn (Function.uncurry f) (triangle 0 T))
    (hq : ContinuousOn (Function.uncurry q) (triangle 0 T))
    (heq : ∀ u a b, u < a → a ≤ b → outSeg u a b ⊆ triangle 0 T → IntegralForm (f u) (q u) a b)
    {u : ℝ} (hu : u ∈ Icc 0 T) : AbsolutelyContinuousOnInterval (f u) u T := by
  have hm : MapsTo (fun x => (u, x)) (Icc u T) (triangle 0 T) := fun x hx => ⟨hu.1, hx.1, hx.2⟩
  apply ac_of_continuous_density_of_interior_equations hu.2
    (hf.comp (continuous_const.prodMk continuous_id).continuousOn hm)
    (hq.comp (continuous_const.prodMk continuous_id).continuousOn hm)
  intro a b hua hab hbT
  exact heq u a b hua hab (by
    rintro ⟨x, y⟩ ⟨rfl, hay, hyb⟩
    exact ⟨hu.1, hua.le.trans hay, hyb.trans hbT.le⟩)

private theorem in_ac {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {T : ℝ} {f q : ℝ → ℝ → E}
    (hf : ContinuousOn (Function.uncurry f) (triangle 0 T))
    (hq : ContinuousOn (Function.uncurry q) (triangle 0 T))
    (heq : ∀ a b v, a ≤ b → b < v → inSeg a b v ⊆ triangle 0 T →
      IntegralForm (fun x => f x v) (fun x => q x v) a b)
    {v : ℝ} (hv : v ∈ Icc 0 T) : AbsolutelyContinuousOnInterval (fun x => f x v) 0 v := by
  have hm : MapsTo (fun x => (x, v)) (Icc 0 v) (triangle 0 T) := fun x hx => ⟨hx.1, hx.2, hv.2⟩
  apply ac_of_continuous_density_of_interior_equations hv.1
    (hf.comp (continuous_id.prodMk continuous_const).continuousOn hm)
    (hq.comp (continuous_id.prodMk continuous_const).continuousOn hm)
  intro a b h0a hab hbv
  exact heq a b v hab hbv (by
    rintro ⟨x, y⟩ ⟨hax, hxb, rfl⟩
    exact ⟨h0a.le.trans hax, hxb.trans hbv.le, hv.2⟩)

/-- Recover full characteristic AC of radius and charge in a classical
strong limit. Only the actual primary convergence and denominator signs are
assumed; no current convergence or characteristic AC conclusion is an extra
premise. All primitive coefficients are one. -/
theorem StrongLimit.radius_charge_ac_of_c1 {e T : ℝ} {Sn : ℕ → Fields} {S : Fields}
    (hT : 0 < T) (hc1 : ∀ n, IsC1Solution e (Sn n) (triangle 0 T))
    (hlim : StrongLimit e T Sn S)
    (hr : ∀ p ∈ triangle 0 T, p.1 < p.2 → 0 < S.r p.1 p.2)
    (hl : ∀ p ∈ triangle 0 T, 0 < S.lam p.1 p.2)
    (hn : ∀ p ∈ triangle 0 T, S.nu p.1 p.2 < 0)
    (hg : ∀ p ∈ triangle 0 T, 0 < 1 - S.mu p.1 p.2) :
    (∀ u ∈ Icc 0 T, AbsolutelyContinuousOnInterval (S.r u) u T ∧
      AbsolutelyContinuousOnInterval (S.Q u) u T) ∧
    (∀ v ∈ Icc 0 T, AbsolutelyContinuousOnInterval (fun u => S.r u v) 0 v ∧
      AbsolutelyContinuousOnInterval (fun u => S.Q u v) 0 v) := by
  obtain ⟨hout, hin⟩ := hlim.integral_equations_of_c1 hT hc1 hr hl hn hg
  have cr := hlim.unif_r.continuousOn (Eventually.of_forall fun n => (hc1
      n).c1_r.continuousOn).frequently
  have cl := hlim.unif_lam.continuousOn (Eventually.of_forall fun n => (hc1
      n).c1_lam.continuousOn).frequently
  have cn := hlim.unif_nu.continuousOn (Eventually.of_forall fun n => (hc1
      n).c1_nu.continuousOn).frequently
  have cQ := hlim.unif_Q.continuousOn (Eventually.of_forall fun n => (hc1
      n).c1_Q.continuousOn).frequently
  have cp := hlim.unif_phi.continuousOn (Eventually.of_forall fun n => (hc1
      n).c1_phi.continuousOn).frequently
  have ct := hlim.unif_theta.continuousOn (Eventually.of_forall fun n => (hc1
      n).c1_theta.continuousOn).frequently
  have cx := hlim.unif_xi.continuousOn (Eventually.of_forall fun n => (hc1
      n).c1_xi.continuousOn).frequently
  have cqv : ContinuousOn (Function.uncurry (S.QV e)) (triangle 0 T) := by
    simpa only [Fields.QV, Function.uncurry_def] using!
      (((continuousOn_const (c := e)).mul cr).mul
        (Complex.continuous_im.comp_continuousOn ((continuous_star.comp_continuousOn cp).mul
            ct))).neg
  have cqu : ContinuousOn (Function.uncurry (S.QU e)) (triangle 0 T) := by
    simpa only [Fields.QU, Function.uncurry_def] using!
      ((continuousOn_const (c := e)).mul cr).mul
        (Complex.continuous_im.comp_continuousOn ((continuous_star.comp_continuousOn cp).mul cx))
  exact ⟨fun u hu => ⟨out_ac cr cl (fun u a b hua hab hs => (hout u a b hua hab hs).1) hu,
      out_ac cQ cqv (fun u a b hua hab hs => (hout u a b hua hab hs).2.2.2.1) hu⟩,
    fun v hv => ⟨in_ac cr cn (fun a b v hab hbv hs => (hin a b v hab hbv hs).1) hv,
      in_ac cQ cqu (fun a b v hab hbv hs => (hin a b v hab hbv hs).2.2.2.1) hv⟩⟩

end EmcsfAcExtension.Local
