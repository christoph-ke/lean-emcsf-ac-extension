module

public import EmcsfAcExtension.Global.Interaction.NEstimateDecomposition
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import EmcsfAcExtension.Frozen.Fields.EqOn

/-! # Measurability of the seven interaction contributions

Continuous fields on a proper finite exterior are extended by clamping.
The derivative of the extended scalar agrees on the interior of every
outgoing row. Measurable parameter integrals then justify summing the
seven nonnegative integrals before their finiteness is known.
Source: `charged_SF_new_version.tex:L3625–L3745`, internal project record's Tonelli convention.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global.InteractionEstimate

/-- [internal]
The seven literal summands of the weighted interaction source, in the
order boundary/boundary, source/boundary, incoming boundary, pair, mixed
electric, explicit electric curvature, and Maxwell remainder.
This is algebraic bookkeeping; it introduces no estimate constant.
Source: `charged_SF_new_version.tex:L3625–L3745`. -/
@[expose] noncomputable def sourceContribution (e : ℝ) (S : Fields) (vb : ℝ → ℝ)
    (i : Fin 7) (u v : ℝ) : ℂ :=
  ![curvatureScalarSource S u v (radialYBoundary S u (vb u) v)
      (radialCurvatureBoundary S u (vb u) v),
    curvatureScalarSource S u v (radialYSource S u (vb u) v)
      (radialCurvatureBoundary S u (vb u) v),
    curvatureScalarSource S u v (S.theta u v / S.lam u v)
      (radialCurvatureWith S u (vb u) v (radialZBoundary S u (vb u))),
    curvatureScalarSource S u v (S.theta u v / S.lam u v)
      (radialCurvatureWith S u (vb u) v (radialZSource S u (vb u))),
    curvatureScalarSource S u v (S.theta u v / S.lam u v)
      (radialCurvatureWith S u (vb u) v (radialZEM e S u (vb u))),
    curvatureScalarSource S u v (S.theta u v / S.lam u v)
      (radialCurvatureEM e S u (vb u) v),
    ((S.lam u v / (1 - S.mu u v) : ℝ) : ℂ) * Local.emSourceJ e S u v] i

private theorem measurable_param_integral {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (f : α → ℝ → E) (hf : Measurable f.uncurry)
    (a b : α → ℝ) (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun x => ∫ t in a x..b x, f x t) := by
  have hleft : StronglyMeasurable
      ({p : α × ℝ | a p.1 < p.2 ∧ p.2 ≤ b p.1}.indicator f.uncurry) :=
    hf.stronglyMeasurable.indicator
      ((measurableSet_lt (ha.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (hb.comp measurable_fst)))
  have hright : StronglyMeasurable
      ({p : α × ℝ | b p.1 < p.2 ∧ p.2 ≤ a p.1}.indicator f.uncurry) :=
    hf.stronglyMeasurable.indicator
      ((measurableSet_lt (hb.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (ha.comp measurable_fst)))
  convert (hleft.integral_prod_right' (ν := volume)).measurable.sub
    (hright.integral_prod_right' (ν := volume)).measurable using 1
  ext x
  change (∫ t in a x..b x, f x t) =
    (∫ t, (Ioc (a x) (b x)).indicator (fun t => f x t) t) -
      ∫ t, (Ioc (b x) (a x)).indicator (fun t => f x t) t
  rw [integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc]
  rfl

private theorem measurable_primitives (e : ℝ) (T : Fields)
    (hr : Continuous T.r.uncurry) (hl : Continuous T.lam.uncurry)
    (hn : Continuous T.nu.uncurry) (hm : Continuous T.m.uncurry)
    (hq : Continuous T.Q.uncurry) (hp : Continuous T.phi.uncurry)
    (ht : Continuous T.theta.uncurry) (hx : Continuous T.xi.uncurry)
    (hl0 : ∀ u v, T.lam u v ≠ 0) :
    let P := (ℝ × ℝ) × ℝ
    Measurable (fun p : P => radialYBoundary T p.1.1 p.1.2 p.2) ∧
    Measurable (fun p : P => radialYSource T p.1.1 p.1.2 p.2) ∧
    Measurable (fun p : P => radialCurvatureBoundary T p.1.1 p.1.2 p.2) ∧
    Measurable (fun p : P => radialCurvatureWith T p.1.1 p.1.2 p.2
      (radialZBoundary T p.1.1 p.1.2)) ∧
    Measurable (fun p : P => radialCurvatureWith T p.1.1 p.1.2 p.2
      (radialZSource T p.1.1 p.1.2)) ∧
    Measurable (fun p : P => radialCurvatureWith T p.1.1 p.1.2 p.2
      (radialZEM e T p.1.1 p.1.2)) ∧
    Measurable (fun p : P => radialCurvatureEM e T p.1.1 p.1.2 p.2) := by
  dsimp only
  have mr := hr.measurable
  have ml := hl.measurable
  have mn := hn.measurable
  have mm := hm.measurable
  have mq := hq.measurable
  have mp := hp.measurable
  have mt := ht.measurable
  have mx := hx.measurable
  have mμ : Measurable T.mu.uncurry := by unfold Fields.mu; fun_prop
  have mC : Measurable (Local.curv T).uncurry := by unfold Local.curv; fun_prop
  have mWave : Measurable (T.waveSource e).uncurry := by unfold Fields.waveSource; fun_prop
  have ca : Continuous T.a.uncurry := by
    unfold Fields.a
    exact hp.add (ht.div (continuous_ofReal.comp hl)
      (fun p => ofReal_ne_zero.mpr (hl0 p.1 p.2)))
  have md := measurable_deriv_with_param ca
  have mW : Measurable (weightedJ T).uncurry := by unfold weightedJ jOut; fun_prop
  have mD : Measurable (fun p : (ℝ × ℝ) × ℝ => radialDamping T p.1.1 p.1.2 p.2) := by
    unfold radialDamping
    apply Measurable.exp
    apply Measurable.neg
    apply measurable_param_integral
    · try simp only [starRingEnd_apply]
      fun_prop
    · exact measurable_fst.snd
    · exact measurable_snd
  have mYB : Measurable (fun p : (ℝ × ℝ) × ℝ => radialYBoundary T p.1.1 p.1.2 p.2) := by
    unfold radialYBoundary
    fun_prop
  have mYJ : Measurable (fun p : (ℝ × ℝ) × ℝ => radialYSource T p.1.1 p.1.2 p.2) := by
    have mlift := mD.comp (f := fun p : ((ℝ × ℝ) × ℝ) × ℝ => ((p.1.1.1, p.2), p.1.2)) (by fun_prop)
    unfold radialYSource
    apply measurable_param_integral
    · try simp only [starRingEnd_apply]
      fun_prop
    · exact measurable_fst.snd
    · exact measurable_snd
  have mZB : Measurable (fun p : (ℝ × ℝ) × ℝ => radialZBoundary T p.1.1 p.1.2 p.2) := by
    have mlift := mYB.comp (f := fun p : ((ℝ × ℝ) × ℝ) × ℝ => ((p.1.1.1, p.1.1.2), p.2))
        (by fun_prop)
    unfold radialZBoundary
    apply Measurable.sub (by fun_prop)
    apply Measurable.mul (by fun_prop)
    apply measurable_param_integral
    · try simp only [starRingEnd_apply]
      fun_prop
    · exact measurable_fst.snd
    · exact measurable_snd
  have mZJ : Measurable (fun p : (ℝ × ℝ) × ℝ => radialZSource T p.1.1 p.1.2 p.2) := by
    have mlift := mYJ.comp (f := fun p : ((ℝ × ℝ) × ℝ) × ℝ => ((p.1.1.1, p.1.1.2), p.2))
        (by fun_prop)
    unfold radialZSource
    apply Measurable.mul (by fun_prop)
    apply measurable_param_integral
    · try simp only [starRingEnd_apply]
      fun_prop
    · exact measurable_fst.snd
    · exact measurable_snd
  have mZE : Measurable (fun p : (ℝ × ℝ) × ℝ => radialZEM e T p.1.1 p.1.2 p.2) := by
    unfold radialZEM
    apply Measurable.mul (by fun_prop)
    apply measurable_param_integral
    · try simp only [starRingEnd_apply]
      fun_prop
    · exact measurable_fst.snd
    · exact measurable_snd
  have mZBlift := mZB.comp (f := fun p : ((ℝ × ℝ) × ℝ) × ℝ =>
    ((p.1.1.1, p.1.1.2), p.2)) (by fun_prop)
  have mZJlift := mZJ.comp (f := fun p : ((ℝ × ℝ) × ℝ) × ℝ =>
    ((p.1.1.1, p.1.1.2), p.2)) (by fun_prop)
  have mZElift := mZE.comp (f := fun p : ((ℝ × ℝ) × ℝ) × ℝ =>
    ((p.1.1.1, p.1.1.2), p.2)) (by fun_prop)
  refine ⟨mYB, mYJ, ?_, ?_, ?_, ?_, ?_⟩
  · unfold radialCurvatureBoundary
    fun_prop
  · unfold radialCurvatureWith
    apply Measurable.mul (by fun_prop)
    apply measurable_param_integral
    · try simp only [starRingEnd_apply]
      fun_prop
    · exact measurable_fst.snd
    · exact measurable_snd
  · unfold radialCurvatureWith
    apply Measurable.mul (by fun_prop)
    apply measurable_param_integral
    · try simp only [starRingEnd_apply]
      fun_prop
    · exact measurable_fst.snd
    · exact measurable_snd
  · unfold radialCurvatureWith
    apply Measurable.mul (by fun_prop)
    apply measurable_param_integral
    · try simp only [starRingEnd_apply]
      fun_prop
    · exact measurable_fst.snd
    · exact measurable_snd
  · unfold radialCurvatureEM
    apply Measurable.mul (by fun_prop)
    apply measurable_param_integral
    · try simp only [starRingEnd_apply]
      fun_prop
    · exact measurable_fst.snd
    · exact measurable_snd

private theorem row_primitive_congruence (e : ℝ) (T S : Fields) (u a b : ℝ)
    (hab : a ≤ b) (he : T.EqOn S (outSeg u a b))
    (hW : ∀ᵐ v : ℝ, v ∈ Icc a b → weightedJ T u v = weightedJ S u v) :
    radialYBoundary T u a b = radialYBoundary S u a b ∧
    radialYSource T u a b = radialYSource S u a b ∧
    radialCurvatureBoundary T u a b = radialCurvatureBoundary S u a b ∧
    radialCurvatureWith T u a b (radialZBoundary T u a) =
      radialCurvatureWith S u a b (radialZBoundary S u a) ∧
    radialCurvatureWith T u a b (radialZSource T u a) =
      radialCurvatureWith S u a b (radialZSource S u a) ∧
    radialCurvatureWith T u a b (radialZEM e T u a) =
      radialCurvatureWith S u a b (radialZEM e S u a) ∧
    radialCurvatureEM e T u a b = radialCurvatureEM e S u a b := by
  have eq (v : ℝ) (hv : v ∈ Icc a b) := he (u, v) ⟨rfl, hv⟩
  have hm (v : ℝ) (hv : v ∈ Icc a b) : T.mu u v = S.mu u v := by
    simp only [Fields.mu, (eq v hv).1, (eq v hv).2.2.2.1]
  have sub {x y t : ℝ} (hax : a ≤ x) (hyb : y ≤ b) (ht : t ∈ uIcc x y)
      (hxy : x ≤ y) : t ∈ Icc a b := by
    rw [uIcc_of_le hxy] at ht
    exact ⟨hax.trans ht.1, ht.2.trans hyb⟩
  have hD (x y : ℝ) (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) :
      radialDamping T u x y = radialDamping S u x y := by
    unfold radialDamping
    congr 2
    apply intervalIntegral.integral_congr
    intro t ht
    have heq := eq t (sub hax hyb ht hxy)
    simp only [heq.1, heq.2.1, heq.2.2.2.2.2.2.2.1]
  have hB (x y : ℝ) (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) :
      radialYBoundary T u x y = radialYBoundary S u x y := by
    have heq := eq x ⟨hax, hxy.trans hyb⟩
    simp only [radialYBoundary, hD x y hax hxy hyb, heq.2.1, heq.2.2.2.2.2.2.2.1]
  have hJ (x y : ℝ) (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) :
      radialYSource T u x y = radialYSource S u x y := by
    unfold radialYSource
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hW] with t ht htm
    have htm : t ∈ Icc x y := by
      simpa only [uIcc_of_le hxy] using uIoc_subset_uIcc htm
    have heq := eq t ⟨hax.trans htm.1, htm.2.trans hyb⟩
    rw [hD t y (hax.trans htm.1) htm.2 hyb, ht ⟨hax.trans htm.1, htm.2.trans hyb⟩,
      heq.2.1]
  have hZB (t : ℝ) (ht : t ∈ Icc a b) :
      radialZBoundary T u a t = radialZBoundary S u a t := by
    have ea := eq a ⟨le_rfl, hab⟩
    have et := eq t ht
    unfold radialZBoundary
    rw [ea.2.2.1, et.2.2.1, ea.2.2.2.2.2.2.2.2]
    congr 2
    apply intervalIntegral.integral_congr
    intro s hs
    have hs := sub le_rfl ht.2 hs ht.1
    have es := eq s hs
    dsimp only
    rw [es.1, es.2.1, es.2.2.1, hB a s le_rfl hs.1 hs.2]
  have hZJ (t : ℝ) (ht : t ∈ Icc a b) :
      radialZSource T u a t = radialZSource S u a t := by
    unfold radialZSource
    rw [(eq t ht).2.2.1]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    have hs := sub le_rfl ht.2 hs ht.1
    have es := eq s hs
    dsimp only
    rw [es.1, es.2.1, es.2.2.1, hJ a s le_rfl hs.1 hs.2]
  have hZE (t : ℝ) (ht : t ∈ Icc a b) :
      radialZEM e T u a t = radialZEM e S u a t := by
    unfold radialZEM
    rw [(eq t ht).2.2.1]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    have hs := sub le_rfl ht.2 hs ht.1
    rcases eq s hs with ⟨er, el, en, em, eq, ep, _, _, _⟩
    simp only [Fields.waveSource, Fields.mu, er, el, en, em, eq, ep]
  have hC (zT zS : ℝ → ℂ) (hz : ∀ t ∈ Icc a b, zT t = zS t) :
      radialCurvatureWith T u a b zT = radialCurvatureWith S u a b zS := by
    unfold radialCurvatureWith
    rw [(eq b ⟨hab, le_rfl⟩).1]
    congr 1
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hW] with t ht htm
    have htm : t ∈ Icc a b := by
      simpa only [uIcc_of_le hab] using uIoc_subset_uIcc htm
    have et := eq t htm
    rw [et.1, et.2.1, hm t htm, hz t htm, ht htm]
  refine ⟨hB a b le_rfl hab le_rfl, hJ a b le_rfl hab le_rfl, ?_,
    hC _ _ hZB, hC _ _ hZJ, hC _ _ hZE, ?_⟩
  · rcases eq a ⟨le_rfl, hab⟩ with ⟨er, el, en, em, _, _, _, et, ex⟩
    simp only [radialCurvatureBoundary, Local.curv, Fields.mu, er, el, en, em, et, ex,
      (eq b ⟨hab, le_rfl⟩).1]
  · unfold radialCurvatureEM
    rw [(eq b ⟨hab, le_rfl⟩).1]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    have ht := sub le_rfl le_rfl ht hab
    rcases eq t ht with ⟨er, el, _, _, eq, ep, _, et, _⟩
    simp only [er, el, eq, ep, et]

private theorem measurable_contribution_of_continuous (e : ℝ) (T : Fields)
    (hr : Continuous T.r.uncurry) (hl : Continuous T.lam.uncurry)
    (hn : Continuous T.nu.uncurry) (hm : Continuous T.m.uncurry)
    (hq : Continuous T.Q.uncurry) (hp : Continuous T.phi.uncurry)
    (ht : Continuous T.theta.uncurry) (hx : Continuous T.xi.uncurry)
    (hl0 : ∀ u v, T.lam u v ≠ 0) (w : ℝ → ℝ) (hw : Measurable w) (i : Fin 7) :
    Measurable (sourceContribution e T w i).uncurry := by
  obtain ⟨mB, mJ, mC, mZB, mZJ, mZE, mE⟩ :=
    measurable_primitives e T hr hl hn hm hq hp ht hx hl0
  have margs : Measurable (fun p : ℝ × ℝ => ((p.1, w p.1), p.2)) := by fun_prop
  have mB := mB.comp margs
  have mJ := mJ.comp margs
  have mC := mC.comp margs
  have mZB := mZB.comp margs
  have mZJ := mZJ.comp margs
  have mZE := mZE.comp margs
  have mE := mE.comp margs
  have mr := hr.measurable
  have ml := hl.measurable
  have mn := hn.measurable
  have mm := hm.measurable
  have mq := hq.measurable
  have mp := hp.measurable
  have mt := ht.measurable
  have mx := hx.measurable
  change Measurable (fun p : ℝ × ℝ => sourceContribution e T w i p.1 p.2)
  unfold sourceContribution
  fin_cases i <;>
    (try simp only [curvatureScalarSource, Local.emSourceJ, Fields.QV, Fields.mu,
        starRingEnd_apply]) <;>
    fun_prop

/-- [internal]
Each actual contribution has a measurable zero extension from the proper
finite exterior. The rough derivative is replaced only inside outgoing
integrals, using rowwise almost-everywhere equality. No finiteness or
source bound is assumed, and there are no constants. -/
theorem measurable_sourceContribution {ui e u₀ u₁ v₀ ρ : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) (i : Fin 7) :
    Measurable ((exteriorDomain ui u₀ u₁ vb).indicator
      (sourceContribution e S vb i).uncurry) := by
  classical
  let D := exteriorDomain ui u₀ u₁ vb
  have hab : u₀ ≤ u₁ := by
    simpa only [B.first, B.last] using B.ordered (Fin.zero_le (Fin.last N))
  let U := fun u : ℝ => max u₀ (min u₁ u)
  have hU : Continuous U := by fun_prop
  have hUm (u : ℝ) : U u ∈ Icc u₀ u₁ :=
    ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  let π := fun p : ℝ × ℝ => (U p.1, max (vb (U p.1)) (min 0 p.2))
  have hπ : Continuous π :=
    (hU.comp continuous_fst).prodMk
      (((B.cont.comp_continuous hU hUm).comp continuous_fst).max
        (continuous_const.min continuous_snd))
  have hπm (p : ℝ × ℝ) : π p ∈ D :=
    finite_boundary_row B (U p.1) (hUm p.1)
      ⟨rfl, le_max_left _ _, max_le (B.mem _ (hUm p.1)).2.2.2 (min_le_left _ _)⟩
  have hπeq (p : ℝ × ℝ) (hp : p ∈ D) : π p = p := by
    have hu : U p.1 = p.1 := by
      simp only [U, min_eq_right hp.2.2.1, max_eq_right hp.2.1]
    simp only [π, hu, min_eq_right hp.1.2.2.2, max_eq_right hp.2.2.2, Prod.eta]
  let T : Fields := {
    r := fun u v => S.r (π (u, v)).1 (π (u, v)).2
    lam := fun u v => S.lam (π (u, v)).1 (π (u, v)).2
    nu := fun u v => S.nu (π (u, v)).1 (π (u, v)).2
    m := fun u v => S.m (π (u, v)).1 (π (u, v)).2
    Q := fun u v => S.Q (π (u, v)).1 (π (u, v)).2
    phi := fun u v => S.phi (π (u, v)).1 (π (u, v)).2
    A := fun u v => S.A (π (u, v)).1 (π (u, v)).2
    theta := fun u v => S.theta (π (u, v)).1 (π (u, v)).2
    xi := fun u v => S.xi (π (u, v)).1 (π (u, v)).2 }
  have he : T.EqOn S D := by
    intro p hp
    simp [T, hπeq p hp]
  let w := fun u => vb (U u)
  have hw : Continuous w := B.cont.comp_continuous hU hUm
  have hwu (u : ℝ) (hu : u ∈ Icc u₀ u₁) : w u = vb u := by
    simp only [w, U, min_eq_right hu.2, max_eq_right hu.1]
  have hW (u : ℝ) (hu : u ∈ Icc u₀ u₁) :
      ∀ᵐ v : ℝ, v ∈ Icc (vb u) 0 → weightedJ T u v = weightedJ S u v := by
    filter_upwards [volume.ae_ne (vb u), volume.ae_ne (0 : ℝ)] with v hva hv0 hv
    have hvi : v ∈ Ioo (vb u) 0 := ⟨lt_of_le_of_ne hv.1 hva.symm, lt_of_le_of_ne hv.2 hv0⟩
    have hd : deriv (T.a u) v = deriv (S.a u) v := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [Ioo_mem_nhds hvi.1 hvi.2] with t ht
      have het := he (u, t) (finite_boundary_row B u hu ⟨rfl, Ioo_subset_Icc_self ht⟩)
      simp only [Fields.a, het.2.1, het.2.2.2.2.2.1, het.2.2.2.2.2.2.2.1]
    have hev := he (u, v) (finite_boundary_row B u hu ⟨rfl, hv⟩)
    simp only [weightedJ, jOut, Fields.mu, hd, hev.1, hev.2.1, hev.2.2.2.1,
      hev.2.2.2.2.2.2.2.1]
  have hc := measurable_contribution_of_continuous e T
    (hS.cont_r.comp_continuous hπ (fun p => (hπm p).1))
    (hS.cont_lam.comp_continuous hπ (fun p => (hπm p).1))
    (hS.cont_nu.comp_continuous hπ (fun p => (hπm p).1))
    (hS.cont_m.comp_continuous hπ (fun p => (hπm p).1))
    (hS.cont_Q.comp_continuous hπ (fun p => (hπm p).1))
    (hS.cont_phi.comp_continuous hπ (fun p => (hπm p).1))
    (hS.cont_theta.comp_continuous hπ (fun p => (hπm p).1))
    (hS.cont_xi.comp_continuous hπ (fun p => (hπm p).1))
    (fun u v => (hS.lam_pos _ (hπm (u, v)).1).ne') w hw.measurable i
  convert hc.indicator (measurableSet_exteriorDomain B) using 1
  apply indicator_congr
  rintro ⟨u, v⟩ hp
  have hu : u ∈ Icc u₀ u₁ := ⟨hp.2.1, hp.2.2.1⟩
  have hv : v ∈ Icc (vb u) 0 := ⟨hp.2.2.2, hp.1.2.2.2⟩
  obtain ⟨hB, hJ, hC, hZB, hZJ, hZE, hE⟩ := row_primitive_congruence e T S u (vb u) v hv.1
    (fun p hp => he p (finite_boundary_row B u hu ⟨hp.1, hp.2.1, hp.2.2.trans hv.2⟩))
    ((hW u hu).mono fun t ht htm => ht ⟨htm.1, htm.2.trans hv.2⟩)
  have hev := he (u, v) hp
  dsimp only [Function.uncurry]
  unfold sourceContribution
  rw [hwu u hu]
  fin_cases i <;>
    simp [hB, hJ, hC, hZB, hZJ, hZE, hE, curvatureScalarSource,
      Local.emSourceJ, Fields.QV, Fields.mu, hev.1, hev.2.1, hev.2.2.1, hev.2.2.2.1,
      hev.2.2.2.2.1, hev.2.2.2.2.2.1, hev.2.2.2.2.2.2.2.1]

end EmcsfAcExtension.Global.InteractionEstimate
