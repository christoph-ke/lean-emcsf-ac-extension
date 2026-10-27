module

public import EmcsfAcExtension.Local.Broad.RectangleState
import EmcsfAcExtension.Local.Construction.StripTube

/-! # Uniform control of normalized values and first jets

Only continuity of the finite-dimensional algebraic normalization and
its first differential is needed. The old state and its full first jet
range over one fixed compact set; no second derivative of a solution
or modulus belonging to an old solution enters the tolerances.
-/

public section

open Set Metric

namespace EmcsfAcExtension.Local

open Broad

/-- The outgoing normalized scalar, evaluated on a finite state. -/
@[expose] noncomputable def continuation_normalized_a (z : RectangleState) : ℂ :=
  (rectangle_constant_fields z).a 0 0

/-- The incoming normalized scalar, evaluated on a finite state. -/
@[expose] noncomputable def continuation_normalized_b (z : RectangleState) : ℂ :=
  (rectangle_constant_fields z).b 0 0

/-- The mass ratio, evaluated on a finite state. -/
@[expose] noncomputable def continuation_normalized_mu (z : RectangleState) : ℝ :=
  (rectangle_constant_fields z).mu 0 0

/-- The outgoing normalization is twice differentiable away from its
expansion pole, with differentiation only in the finite state. -/
theorem contDiffAt_continuation_normalized_a {z : RectangleState} (hz : z.1.1 ≠ 0) :
    ContDiffAt ℝ 2 continuation_normalized_a z := by
  have cp : ContDiffAt ℝ 2 (fun w : RectangleState => w.2.2.2.2.2.2.1) z := by fun_prop
  have ct : ContDiffAt ℝ 2 (fun w : RectangleState => w.1.2) z := by fun_prop
  have clR : ContDiffAt ℝ 2 (fun w : RectangleState => w.1.1) z := by fun_prop
  have cl := Complex.ofRealCLM.contDiff.contDiffAt.comp z clR
  exact cp.add (ct.mul (cl.fun_inv (Complex.ofReal_ne_zero.mpr hz)))

/-- The incoming normalization is twice differentiable away from its
incoming expansion pole. This is state regularity, not solution C². -/
theorem contDiffAt_continuation_normalized_b {z : RectangleState} (hz : z.2.2.1 ≠ 0) :
    ContDiffAt ℝ 2 continuation_normalized_b z := by
  have cp : ContDiffAt ℝ 2 (fun w : RectangleState => w.2.2.2.2.2.2.1) z := by fun_prop
  have cx : ContDiffAt ℝ 2 (fun w : RectangleState => w.2.2.2.2.2.2.2) z := by fun_prop
  have cnR : ContDiffAt ℝ 2 (fun w : RectangleState => w.2.2.1) z := by fun_prop
  have cn := Complex.ofRealCLM.contDiff.contDiffAt.comp z cnR
  exact cp.add (cx.mul (cn.fun_inv (Complex.ofReal_ne_zero.mpr hz)))

/-- The mass ratio is twice differentiable away from zero radius. -/
theorem contDiffAt_continuation_normalized_mu {z : RectangleState} (hz : z.2.1 ≠ 0) :
    ContDiffAt ℝ 2 continuation_normalized_mu z := by
  have cm : ContDiffAt ℝ 2 (fun w : RectangleState => 2*w.2.2.2.1) z := by fun_prop
  have cr : ContDiffAt ℝ 2 (fun w : RectangleState => w.2.1) z := by fun_prop
  exact cm.mul (cr.fun_inv hz)

private abbrev ContinuationStateJet := (ℝ × ℝ) →L[ℝ] RectangleState

private noncomputable def normalizationJet (p : RectangleState × ContinuationStateJet) :=
  (continuation_normalized_a p.1, continuation_normalized_b p.1,
    (fderiv ℝ continuation_normalized_a p.1).comp p.2,
    (fderiv ℝ continuation_normalized_b p.1).comp p.2,
    continuation_normalized_mu p.1)

/-- Uniform normalized value and first-jet control on the positive-radius
state tube. The tolerances `ζ,q` depend only on `B₀,ℓ,r₀`, before both
states and both full first jets; they are independent of the coupling.
All four normalization differences are at most `B₀`, and the geometric
margins retain half their old lower bounds. No old second jet is used. -/
theorem continuation_normalization_jet_tube
    (B₀ ℓ r₀ : ℝ) (hB : 1 ≤ B₀) (hℓ : 0 < ℓ) (hr₀ : 0 < r₀) :
    ∃ ζ > 0, ∃ q > 0,
      ∀ (w z : RectangleState) (L M : (ℝ × ℝ) →L[ℝ] RectangleState),
        ‖w‖ ≤ B₀ → r₀ ≤ w.2.1 → ℓ ≤ w.1.1 → ℓ ≤ -w.2.2.1 →
        ℓ ≤ 1-continuation_normalized_mu w → ‖L‖ ≤ B₀ →
        ‖z-w‖ ≤ ζ → ‖M-L‖ ≤ q →
        ‖continuation_normalized_a z-continuation_normalized_a w‖ ≤ B₀ ∧
        ‖continuation_normalized_b z-continuation_normalized_b w‖ ≤ B₀ ∧
        ‖(fderiv ℝ continuation_normalized_a z).comp M -
          (fderiv ℝ continuation_normalized_a w).comp L‖ ≤ B₀ ∧
        ‖(fderiv ℝ continuation_normalized_b z).comp M -
          (fderiv ℝ continuation_normalized_b w).comp L‖ ≤ B₀ ∧
        ℓ/2 ≤ 1-continuation_normalized_mu z ∧
        r₀/2 ≤ z.2.1 ∧ ℓ/2 ≤ z.1.1 ∧ ℓ/2 ≤ -z.2.2.1 := by
  let K : Set RectangleState := closedBall 0 (B₀+1) ∩
    {z | r₀/2 ≤ z.2.1 ∧ ℓ/2 ≤ z.1.1 ∧ ℓ/2 ≤ -z.2.2.1}
  have hkr : IsClosed {z : RectangleState | r₀/2 ≤ z.2.1} :=
    isClosed_le continuous_const (by fun_prop)
  have hkl : IsClosed {z : RectangleState | ℓ/2 ≤ z.1.1} :=
    isClosed_le continuous_const (by fun_prop)
  have hkn : IsClosed {z : RectangleState | ℓ/2 ≤ -z.2.2.1} :=
    isClosed_le continuous_const (by fun_prop)
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_right (hkr.inter (hkl.inter hkn))
  let : FiniteDimensional ℝ ContinuationStateJet := ContinuousLinearMap.finiteDimensional
  let : ProperSpace ContinuationStateJet := FiniteDimensional.proper ℝ _
  let J : Set (RectangleState × ContinuationStateJet) := K ×ˢ closedBall 0 (4*B₀)
  have hJ : IsCompact J := hK.prod (isCompact_closedBall _ _)
  have hc : ContinuousOn normalizationJet J := by
    intro p hp
    have hl : p.1.1.1 ≠ 0 := ne_of_gt (lt_of_lt_of_le (by positivity) hp.1.2.2.1)
    have hn : p.1.2.2.1 ≠ 0 := ne_of_lt (by linarith only [hp.1.2.2.2,hℓ])
    have hr : p.1.2.1 ≠ 0 := ne_of_gt (lt_of_lt_of_le (by positivity) hp.1.2.1)
    have ca := contDiffAt_continuation_normalized_a hl
    have cb := contDiffAt_continuation_normalized_b hn
    have cm := contDiffAt_continuation_normalized_mu hr
    have cda : ContinuousAt (fun p : RectangleState × ContinuationStateJet =>
        (fderiv ℝ continuation_normalized_a p.1).comp p.2) p :=
      (((ca.fderiv_right (m := 1) (by norm_num)).continuousAt).comp continuousAt_fst).clm_comp
        continuousAt_snd
    have cdb : ContinuousAt (fun p : RectangleState × ContinuationStateJet =>
        (fderiv ℝ continuation_normalized_b p.1).comp p.2) p :=
      (((cb.fderiv_right (m := 1) (by norm_num)).continuousAt).comp continuousAt_fst).clm_comp
        continuousAt_snd
    exact ((ca.continuousAt.comp continuousAt_fst).prodMk
      ((cb.continuousAt.comp continuousAt_fst).prodMk
        (cda.prodMk (cdb.prodMk (cm.continuousAt.comp continuousAt_fst))))).continuousWithinAt
  let ε := min B₀ (ℓ/2)
  have hε : 0 < ε := lt_min (by linarith) (by positivity)
  obtain ⟨δ,hδ,huniform⟩ := Metric.uniformContinuousOn_iff.mp
    (hJ.uniformContinuousOn_of_continuous hc) ε hε
  obtain ⟨τ,hτ,htube⟩ := continuation_state_tube ℓ r₀ hℓ hr₀
  let ζ := min τ (min 1 (δ/2))
  let q := min 1 (δ/2)
  have hζ : 0 < ζ := lt_min hτ (lt_min zero_lt_one (by positivity))
  have hq : 0 < q := lt_min zero_lt_one (by positivity)
  refine ⟨ζ,hζ,q,hq,?_⟩
  intro w z L M hw hwr hwl hwn hwg hL hzw hML
  have hzτ : ‖z-w‖ ≤ τ := hzw.trans (min_le_left _ _)
  obtain ⟨hzbox,_hzregion,_hzn,_hzg,hzr,hzl,hzn,_hznum⟩ :=
    htube B₀ w z hw hwr hwl hwn hwg hzτ
  have hwK : w ∈ K := by
    refine ⟨?_,?_,?_,?_⟩
    · simpa only [mem_closedBall,dist_zero_right] using hw.trans (by linarith : B₀ ≤ B₀+1)
    · linarith only [hwr,hr₀]
    · linarith only [hwl,hℓ]
    · linarith only [hwn,hℓ]
  have hzK : z ∈ K := ⟨hzbox.1,hzr,hzl,hzn⟩
  have hM : ‖M‖ ≤ 4*B₀ := by
    have hq1 : q ≤ 1 := min_le_left _ _
    calc ‖M‖ = ‖(M-L)+L‖ := by rw [sub_add_cancel]
         _ ≤ ‖M-L‖+‖L‖ := norm_add_le _ _
         _ ≤ 1+B₀ := add_le_add (hML.trans hq1) hL
         _ ≤ 4*B₀ := by linarith only [hB]
  have hwJ : (w,L) ∈ J := ⟨hwK, by
    simpa only [mem_closedBall,dist_zero_right] using hL.trans (by linarith : B₀ ≤ 4*B₀)⟩
  have hzJ : (z,M) ∈ J := ⟨hzK, by simpa only [mem_closedBall,dist_zero_right] using hM⟩
  have hd : dist (z,M) (w,L) < δ := by
    rw [Prod.dist_eq,dist_eq_norm,dist_eq_norm]
    apply max_lt
    · exact (hzw.trans ((min_le_right _ _).trans (min_le_right _ _))).trans_lt (by linarith)
    · exact (hML.trans (min_le_right _ _)).trans_lt (by linarith)
  have hu := (huniform (z,M) hzJ (w,L) hwJ hd).le
  simp only [normalizationJet,dist_eq_norm,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,
    max_le_iff] at hu
  have hεB : ε ≤ B₀ := min_le_left _ _
  have hεℓ : ε ≤ ℓ/2 := min_le_right _ _
  refine ⟨hu.1.trans hεB,hu.2.1.trans hεB,hu.2.2.1.trans hεB,
    hu.2.2.2.1.trans hεB,?_,hzr,hzl,hzn⟩
  have hm := abs_le.mp (hu.2.2.2.2.trans hεℓ)
  linarith only [hm.2,hwg]

end EmcsfAcExtension.Local
