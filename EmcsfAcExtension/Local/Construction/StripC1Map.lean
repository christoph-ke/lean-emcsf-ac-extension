module

public import EmcsfAcExtension.Local.Construction.StripFunctionSpace
public import EmcsfAcExtension.Local.Construction.StripPicard
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # The C¹ rectangle Picard operator on a fixed unit square

Rescaling both characteristic coordinates makes the rectangle solution
an implicit function of its endpoint `(u,v)`. The square and its Banach
supremum space stay fixed. Exponential conjugation preserves the source
Lipschitz coefficient, and the weighted primitives supply `γ⁻¹`.
-/

public section

open Set MeasureTheory
open scoped Topology NNReal

namespace EmcsfAcExtension.Local

open StripFunctionSpace

variable {I O : Type*} [NormedAddCommGroup I] [NormedSpace ℝ I] [CompleteSpace I]
  [NormedAddCommGroup O] [NormedSpace ℝ O] [CompleteSpace O]

/-- The incoming normalized coordinate on the fixed square. -/
@[expose] noncomputable def stripUnitU : C(StripUnitSquare, ℝ) :=
  ⟨fun q => (q.1 : ℝ), continuous_subtype_val.comp continuous_fst⟩

/-- The outgoing normalized coordinate on the fixed square. -/
@[expose] noncomputable def stripUnitV : C(StripUnitSquare, ℝ) :=
  ⟨fun q => (q.2 : ℝ), continuous_subtype_val.comp continuous_snd⟩

/-- Exponential weight on the fixed normalized square. -/
@[expose] noncomputable def stripUnitWeight (γ : ℝ) : C(StripUnitSquare, ℝ) :=
  ⟨fun q => Real.exp (γ * ((q.1 : ℝ) + (q.2 : ℝ))), by fun_prop⟩

/-- Exponential square weights never vanish. -/
theorem stripUnitWeight_ne_zero (γ : ℝ) (q : StripUnitSquare) :
    stripUnitWeight γ q ≠ 0 := (Real.exp_pos _).ne'

/-- Affine incoming coordinate, with fixed lower endpoint and variable upper endpoint. -/
@[expose] noncomputable def stripCoordinateU (a : ℝ) (p : ℝ × ℝ) : C(StripUnitSquare, ℝ) :=
  (p.1 - a) • stripUnitU + ContinuousMap.const _ a

/-- Affine outgoing coordinate, with fixed lower endpoint and variable upper endpoint. -/
@[expose] noncomputable def stripCoordinateV (c : ℝ) (p : ℝ × ℝ) : C(StripUnitSquare, ℝ) :=
  (p.2 - c) • stripUnitV + ContinuousMap.const _ c

/-- Normalized incoming coordinates depend smoothly on the upper endpoint. -/
theorem contDiff_stripCoordinateU (a : ℝ) : ContDiff ℝ 1 (stripCoordinateU a) := by
  exact ((contDiff_fst.sub contDiff_const).smul contDiff_const).add contDiff_const

/-- Normalized outgoing coordinates depend smoothly on the upper endpoint. -/
theorem contDiff_stripCoordinateV (c : ℝ) : ContDiff ℝ 1 (stripCoordinateV c) := by
  exact ((contDiff_snd.sub contDiff_const).smul contDiff_const).add contDiff_const

/-- Entering traces on the normalized square in exponentially weighted coordinates. -/
@[expose] noncomputable def stripC1Boundary (a c γ : ℝ) (yi : ℝ → I) (xb : ℝ → O)
    (hyi : Continuous yi) (hxb : Continuous xb) (p : ℝ × ℝ) : C(StripUnitSquare, I × O) :=
  continuousMapSMul (inverseWeight (stripUnitWeight γ) (stripUnitWeight_ne_zero γ))
    (continuousMapPair (superposition yi hyi (stripCoordinateV c p),
      superposition xb hxb (stripCoordinateU a p)))

omit [CompleteSpace I] [CompleteSpace O] in
/-- C¹ entering data induce a C¹ Banach-space boundary map. Compact support
is only used to make their continuous first derivatives uniformly continuous. -/
theorem contDiff_stripC1Boundary (a c γ : ℝ) {yi : ℝ → I} {xb : ℝ → O}
    (hyi : ContDiff ℝ 1 yi) (hxb : ContDiff ℝ 1 xb)
    (hyiC : HasCompactSupport yi) (hxbC : HasCompactSupport xb) :
    ContDiff ℝ 1 (stripC1Boundary a c γ yi xb hyi.continuous hxb.continuous) := by
  exact (continuousMapSMul (inverseWeight (stripUnitWeight γ) (stripUnitWeight_ne_zero
      γ))).contDiff.comp
    (continuousMapPair.contDiff.comp
      (((contDiff_superposition_compactSupport hyi hyiC).comp (contDiff_stripCoordinateV c)).prodMk
        ((contDiff_superposition_compactSupport hxb hxbC).comp (contDiff_stripCoordinateU a))))

/-- The full normalized rectangle Picard map. Its domain is the product
of the physical upper endpoint and the fixed square's weighted state space. -/
@[expose] noncomputable def stripC1Picard (a c γ : ℝ) (hγ : 0 < γ)
    (yi : ℝ → I) (xb : ℝ → O) (fi : I × O → I) (fo : I × O → O)
    (hyi : Continuous yi) (hxb : Continuous xb) (hfi : Continuous fi) (hfo : Continuous fo)
    (q : (ℝ × ℝ) × C(StripUnitSquare, I × O)) : C(StripUnitSquare, I × O) :=
  stripC1Boundary a c γ yi xb hyi hxb q.1 + continuousMapPair
    ((q.1.1 - a) • stripWeightedIncomingIntegral γ hγ
      (weightedSuperposition (stripUnitWeight γ) (stripUnitWeight_ne_zero γ) fi hfi q.2),
    (q.1.2 - c) • stripWeightedOutgoingIntegral γ hγ
      (weightedSuperposition (stripUnitWeight γ) (stripUnitWeight_ne_zero γ) fo hfo q.2))

/-- The normalized Picard map is jointly C¹ in the endpoint and the
continuous candidate state. Only state derivatives of the source and
first derivatives of entering data are used. -/
theorem contDiff_stripC1Picard (a c γ : ℝ) (hγ : 0 < γ)
    {yi : ℝ → I} {xb : ℝ → O} {fi : I × O → I} {fo : I × O → O}
    (hyi : ContDiff ℝ 1 yi) (hxb : ContDiff ℝ 1 xb)
    (hfi : ContDiff ℝ 1 fi) (hfo : ContDiff ℝ 1 fo)
    (hyiC : HasCompactSupport yi) (hxbC : HasCompactSupport xb)
    (hfiC : HasCompactSupport fi) (hfoC : HasCompactSupport fo) :
    ContDiff ℝ 1 (stripC1Picard a c γ hγ yi xb fi fo
      hyi.continuous hxb.continuous hfi.continuous hfo.continuous) := by
  have hi : ContDiff ℝ 1 (fun q : (ℝ × ℝ) × C(StripUnitSquare,I × O) =>
      stripWeightedIncomingIntegral γ hγ
        (weightedSuperposition (stripUnitWeight γ) (stripUnitWeight_ne_zero γ) fi hfi.continuous
            q.2)) :=
    ((stripWeightedIncomingIntegral γ hγ).contDiff.comp
    (contDiff_weightedSuperposition (stripUnitWeight γ) (stripUnitWeight_ne_zero γ) hfi hfiC)).comp
      contDiff_snd
  have ho : ContDiff ℝ 1 (fun q : (ℝ × ℝ) × C(StripUnitSquare,I × O) =>
      stripWeightedOutgoingIntegral γ hγ
        (weightedSuperposition (stripUnitWeight γ) (stripUnitWeight_ne_zero γ) fo hfo.continuous
            q.2)) :=
    ((stripWeightedOutgoingIntegral γ hγ).contDiff.comp
    (contDiff_weightedSuperposition (stripUnitWeight γ) (stripUnitWeight_ne_zero γ) hfo hfoC)).comp
      contDiff_snd
  have hα : ContDiff ℝ 1 (fun q : (ℝ × ℝ) × C(StripUnitSquare,I × O) => q.1.1-a) :=
    (contDiff_fst.fst).sub contDiff_const
  have hβ : ContDiff ℝ 1 (fun q : (ℝ × ℝ) × C(StripUnitSquare,I × O) => q.1.2-c) :=
    (contDiff_fst.snd).sub contDiff_const
  exact ((contDiff_stripC1Boundary a c γ hyi hxb hyiC hxbC).comp contDiff_fst).add
    ((continuousMapPair (K := StripUnitSquare) (E := I) (G := O)).contDiff.comp
      ((hα.smul hi).prodMk (hβ.smul ho)))

/-- The normalized Picard map contracts in its weighted state variable
with coefficient at most `max(|u-a|,|v-c|) * L / γ`. The source coefficient
`L` is fixed before the candidate states or parameter point are chosen. -/
theorem norm_stripC1Picard_sub_le (a c γ : ℝ) (hγ : 0 < γ)
    (yi : ℝ → I) (xb : ℝ → O) (fi : I × O → I) (fo : I × O → O)
    (hyi : Continuous yi) (hxb : Continuous xb)
    {L : NNReal} (hfi : LipschitzWith L fi) (hfo : LipschitzWith L fo)
    (p : ℝ × ℝ) (z w : C(StripUnitSquare, I × O)) :
    ‖stripC1Picard a c γ hγ yi xb fi fo hyi hxb hfi.continuous hfo.continuous (p,z) -
        stripC1Picard a c γ hγ yi xb fi fo hyi hxb hfi.continuous hfo.continuous (p,w)‖ ≤
      max |p.1-a| |p.2-c| * γ⁻¹ * (L * ‖z-w‖) := by
  let Vi := stripWeightedIncomingIntegral (E := I) γ hγ
  let Vo := stripWeightedOutgoingIntegral (E := O) γ hγ
  let Wi := weightedSuperposition (stripUnitWeight γ) (stripUnitWeight_ne_zero γ) fi hfi.continuous
  let Wo := weightedSuperposition (stripUnitWeight γ) (stripUnitWeight_ne_zero γ) fo hfo.continuous
  have hWi : ‖Wi z-Wi w‖ ≤ L * ‖z-w‖ :=
    (lipschitzWith_weightedSuperposition (stripUnitWeight γ) (stripUnitWeight_ne_zero γ)
        hfi).norm_sub_le z w
  have hWo : ‖Wo z-Wo w‖ ≤ L * ‖z-w‖ :=
    (lipschitzWith_weightedSuperposition (stripUnitWeight γ) (stripUnitWeight_ne_zero γ)
        hfo).norm_sub_le z w
  have hi : ‖Vi (Wi z)-Vi (Wi w)‖ ≤ γ⁻¹ * (L * ‖z-w‖) := by
    rw [← map_sub]
    exact (Vi.le_opNorm _).trans (mul_le_mul
      (norm_stripWeightedIncomingIntegral_le (E := I) hγ) hWi
      (norm_nonneg _) (inv_nonneg.mpr hγ.le))
  have ho : ‖Vo (Wo z)-Vo (Wo w)‖ ≤ γ⁻¹ * (L * ‖z-w‖) := by
    rw [← map_sub]
    exact (Vo.le_opNorm _).trans (mul_le_mul
      (norm_stripWeightedOutgoingIntegral_le (E := O) hγ) hWo
      (norm_nonneg _) (inv_nonneg.mpr hγ.le))
  have hC : 0 ≤ γ⁻¹ * (L * ‖z-w‖) :=
    mul_nonneg (inv_nonneg.mpr hγ.le) (mul_nonneg L.2 (norm_nonneg _))
  apply (ContinuousMap.norm_le _ (mul_nonneg
    (mul_nonneg (le_max_of_le_left (abs_nonneg _)) (inv_nonneg.mpr hγ.le))
    (mul_nonneg L.2 (norm_nonneg _)))).mpr
  intro q
  change max
    ‖((stripC1Boundary a c γ yi xb hyi hxb p q).1 + (p.1-a) • Vi (Wi z) q) -
      ((stripC1Boundary a c γ yi xb hyi hxb p q).1 + (p.1-a) • Vi (Wi w) q)‖
    ‖((stripC1Boundary a c γ yi xb hyi hxb p q).2 + (p.2-c) • Vo (Wo z) q) -
      ((stripC1Boundary a c γ yi xb hyi hxb p q).2 + (p.2-c) • Vo (Wo w) q)‖ ≤ _
  simp only [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs]
  rw [mul_assoc]
  apply max_le
  · have hq : ‖Vi (Wi z) q - Vi (Wi w) q‖ ≤ γ⁻¹ * (L * ‖z-w‖) := by
      exact (show ‖Vi (Wi z) q-Vi (Wi w) q‖ ≤ ‖Vi (Wi z)-Vi (Wi w)‖ by
        simpa only [ContinuousMap.sub_apply] using (Vi (Wi z)-Vi (Wi w)).norm_coe_le_norm q).trans
            hi
    exact (mul_le_mul_of_nonneg_left hq (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hC)
  · have hq : ‖Vo (Wo z) q - Vo (Wo w) q‖ ≤ γ⁻¹ * (L * ‖z-w‖) := by
      exact (show ‖Vo (Wo z) q-Vo (Wo w) q‖ ≤ ‖Vo (Wo z)-Vo (Wo w)‖ by
        simpa only [ContinuousMap.sub_apply] using (Vo (Wo z)-Vo (Wo w)).norm_coe_le_norm q).trans
            ho
    exact (mul_le_mul_of_nonneg_left hq (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hC)

/-- A continuous physical state pulled back to the fixed square and
conjugated by the exponential weight. Its endpoint parameter need not
have any derivative. -/
@[expose] noncomputable def stripRescaledState (a c γ : ℝ) (F : ℝ × ℝ → I × O)
    (hF : Continuous F) (p : ℝ × ℝ) : C(StripUnitSquare, I × O) :=
  ⟨fun q => (stripUnitWeight γ q)⁻¹ •
    F ((p.1-a) * (q.1 : ℝ) + a, (p.2-c) * (q.2 : ℝ) + c),
    ((stripUnitWeight γ).continuous.inv₀ (stripUnitWeight_ne_zero γ)).smul
      (hF.comp (by fun_prop))⟩

omit [CompleteSpace I] [CompleteSpace O] in
/-- Pullback and weighting turn a jointly continuous physical state
into a continuous curve in the fixed square's Banach space. -/
theorem continuous_stripRescaledState (a c γ : ℝ) (F : ℝ × ℝ → I × O)
    (hF : Continuous F) : Continuous (stripRescaledState a c γ F hF) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun q : (ℝ × ℝ) × StripUnitSquare =>
    (stripUnitWeight γ q.2)⁻¹ •
      F ((q.1.1-a) * (q.2.1 : ℝ) + a, (q.1.2-c) * (q.2.2 : ℝ) + c))
  exact (((stripUnitWeight γ).continuous.comp continuous_snd).inv₀
    (fun q => stripUnitWeight_ne_zero γ q.2)).smul (hF.comp (by fun_prop))

omit [CompleteSpace O] in
/-- The incoming weighted primitive of the rescaled source is exactly
the rescaled ordinary primitive. This is an identity of actual integrals. -/
theorem stripWeightedIncomingIntegral_rescaled (a c γ : ℝ) (hγ : 0 < γ)
    (F : ℝ × ℝ → I × O) (hF : Continuous F)
    (fi : I × O → I) (hfi : Continuous fi) (p : ℝ × ℝ) (q : StripUnitSquare) :
    stripWeightedIncomingIntegral γ hγ
      (weightedSuperposition (stripUnitWeight γ) (stripUnitWeight_ne_zero γ) fi hfi
        (stripRescaledState a c γ F hF p)) q =
      (stripUnitWeight γ q)⁻¹ • ∫ s in 0..(q.1 : ℝ),
        fi (F ((p.1-a)*s+a, (p.2-c)*(q.2 : ℝ)+c)) := by
  rw [stripWeightedIncomingIntegral_apply, Real.exp_neg]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by
    rw [uIcc_of_le q.1.2.1] at ht
    exact ⟨ht.1, ht.2.trans q.1.2.2⟩
  dsimp only
  rw [projIcc_of_mem zero_le_one ht']
  simp [weightedSuperposition, continuousMapSMul, inverseWeight, superposition,
    stripRescaledState, stripUnitWeight, smul_smul]

omit [CompleteSpace I] in
/-- The outgoing weighted primitive of the rescaled source is exactly
the rescaled ordinary primitive. This also includes square endpoints. -/
theorem stripWeightedOutgoingIntegral_rescaled (a c γ : ℝ) (hγ : 0 < γ)
    (F : ℝ × ℝ → I × O) (hF : Continuous F)
    (fo : I × O → O) (hfo : Continuous fo) (p : ℝ × ℝ) (q : StripUnitSquare) :
    stripWeightedOutgoingIntegral γ hγ
      (weightedSuperposition (stripUnitWeight γ) (stripUnitWeight_ne_zero γ) fo hfo
        (stripRescaledState a c γ F hF p)) q =
      (stripUnitWeight γ q)⁻¹ • ∫ t in 0..(q.2 : ℝ),
        fo (F ((p.1-a)*(q.1 : ℝ)+a, (p.2-c)*t+c)) := by
  rw [stripWeightedOutgoingIntegral_apply, Real.exp_neg]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by
    rw [uIcc_of_le q.2.2.1] at ht
    exact ⟨ht.1, ht.2.trans q.2.2.2⟩
  dsimp only
  rw [projIcc_of_mem zero_le_one ht']
  simp [weightedSuperposition, continuousMapSMul, inverseWeight, superposition,
    stripRescaledState, stripUnitWeight, smul_smul]

private theorem strip_affine_mem {a b u s : ℝ} (hu : u ∈ Icc a b)
    (hs : s ∈ Icc (0 : ℝ) 1) : (u-a)*s+a ∈ Icc a b := by
  have hwidth : 0 ≤ u-a := sub_nonneg.mpr hu.1
  have hlo := mul_nonneg hwidth hs.1
  have hhi : (u-a)*s ≤ u-a := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hs.2 hwidth
  exact ⟨by linarith, by linarith [hu.2]⟩

/-- The actual characteristic integral equations identify the rescaled
continuous state as a fixed point of the normalized Picard operator.
This identity uses only continuity, without first jets. -/
theorem stripC1Picard_rescaled_fixedPoint {a b c d γ : ℝ} (hγ : 0 < γ)
    (F : ℝ × ℝ → I × O) (hF : Continuous F)
    (yi : ℝ → I) (xb : ℝ → O) (fi : I × O → I) (fo : I × O → O)
    (hyi : Continuous yi) (hxb : Continuous xb) (hfi : Continuous fi) (hfo : Continuous fo)
    (hYi : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      (F (u, v)).1 = yi v + ∫ s in a..u, fi (F (s, v)))
    (hXb : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      (F (u, v)).2 = xb u + ∫ t in c..v, fo (F (u, t)))
    {p : ℝ × ℝ} (hp : p ∈ Icc a b ×ˢ Icc c d) :
    stripC1Picard a c γ hγ yi xb fi fo hyi hxb hfi hfo
      (p, stripRescaledState a c γ F hF p) = stripRescaledState a c γ F hF p := by
  apply ContinuousMap.ext
  intro q
  have hu := strip_affine_mem hp.1 q.1.2
  have hv := strip_affine_mem hp.2 q.2.2
  apply Prod.ext
  · change (stripUnitWeight γ q)⁻¹ • yi ((p.2-c)*(q.2 : ℝ)+c) +
      (p.1-a) • stripWeightedIncomingIntegral γ hγ
        (weightedSuperposition (stripUnitWeight γ) (stripUnitWeight_ne_zero γ) fi hfi
          (stripRescaledState a c γ F hF p)) q =
      (stripUnitWeight γ q)⁻¹ • (F ((p.1-a)*(q.1 : ℝ)+a, (p.2-c)*(q.2 : ℝ)+c)).1
    rw [stripWeightedIncomingIntegral_rescaled]
    rw [hYi _ hu _ hv]
    have hchange := intervalIntegral.smul_integral_comp_mul_add
      (f := fun s => fi (F (s, (p.2-c)*(q.2 : ℝ)+c)))
      (a := 0) (b := (q.1 : ℝ)) (p.1-a) a
    simp only [mul_zero, zero_add] at hchange
    rw [← hchange, smul_add]
    simp only [smul_smul, mul_comm]
  · change (stripUnitWeight γ q)⁻¹ • xb ((p.1-a)*(q.1 : ℝ)+a) +
      (p.2-c) • stripWeightedOutgoingIntegral γ hγ
        (weightedSuperposition (stripUnitWeight γ) (stripUnitWeight_ne_zero γ) fo hfo
          (stripRescaledState a c γ F hF p)) q =
      (stripUnitWeight γ q)⁻¹ • (F ((p.1-a)*(q.1 : ℝ)+a, (p.2-c)*(q.2 : ℝ)+c)).2
    rw [stripWeightedOutgoingIntegral_rescaled]
    rw [hXb _ hu _ hv]
    have hchange := intervalIntegral.smul_integral_comp_mul_add
      (f := fun t => fo (F ((p.1-a)*(q.1 : ℝ)+a, t)))
      (a := 0) (b := (q.2 : ℝ)) (p.2-c) c
    simp only [mul_zero, zero_add] at hchange
    rw [← hchange, smul_add]
    simp only [smul_smul, mul_comm]

end EmcsfAcExtension.Local
