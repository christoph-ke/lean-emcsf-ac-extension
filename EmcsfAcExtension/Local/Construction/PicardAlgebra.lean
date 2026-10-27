module

public import EmcsfAcExtension.Local.Construction.PicardCarrier
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Algebra of compatible outgoing carriers

The chain and product rules hold in section interiors. Sectional FTC then
constructs continuous outgoing first jets on the whole closed wedge.
-/

public section

open Set MeasureTheory Filter Topology
open scoped Topology

namespace EmcsfAcExtension.Local

variable {c a L : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Add carriers by adding both values and first outgoing jets. -/
@[expose] noncomputable def picardCarrierAdd (ha : 0 ≤ a) (haL : a ≤ L)
    (z w : PicardCarrier c a L E) : PicardCarrier c a L E :=
  picardCarrierOfRawDeriv
    (fun u v => picardCarrierValue ha haL z u v + picardCarrierValue ha haL w u v)
    (z.1.1 + w.1.1) (z.1.2 + w.1.2)
    (by intro p; simp only [ContinuousMap.add_apply, picardCarrierValue_coe])
    (by
      intro p hp ht
      exact (picardCarrierValue_hasDerivAt ha haL z p hp ht).add
        (picardCarrierValue_hasDerivAt ha haL w p hp ht))
/-- Negate both components of an outgoing carrier. -/
@[expose] noncomputable def picardCarrierNeg (ha : 0 ≤ a) (haL : a ≤ L)
    (z : PicardCarrier c a L E) : PicardCarrier c a L E :=
  picardCarrierOfRawDeriv (fun u v => -picardCarrierValue ha haL z u v)
    (-z.1.1) (-z.1.2)
    (by intro p; simp only [ContinuousMap.neg_apply, picardCarrierValue_coe])
    (by intro p hp ht; exact (picardCarrierValue_hasDerivAt ha haL z p hp ht).neg)
/-- Apply a continuous real-linear map to values and outgoing jets. -/
@[expose] noncomputable def picardCarrierLinear {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (ha : 0 ≤ a) (haL : a ≤ L) (T : E →L[ℝ] F)
    (z : PicardCarrier c a L E) : PicardCarrier c a L F :=
  picardCarrierOfRawDeriv (fun u v => T (picardCarrierValue ha haL z u v))
    ⟨fun p => T (z.1.1 p), T.continuous.comp z.1.1.continuous⟩
    ⟨fun p => T (z.1.2 p), T.continuous.comp z.1.2.continuous⟩
    (by intro p; simp only [ContinuousMap.coe_mk, picardCarrierValue_coe])
    (by
      intro p hp ht
      exact T.hasFDerivAt.comp_hasDerivAt p.1.2
        (picardCarrierValue_hasDerivAt ha haL z p hp ht))
/-- Multiply real carriers with the product-rule outgoing jet. -/
@[expose] noncomputable def picardCarrierMul (ha : 0 ≤ a) (haL : a ≤ L)
    (z w : PicardCarrier c a L ℝ) : PicardCarrier c a L ℝ :=
  picardCarrierOfRawDeriv
    (fun u v => picardCarrierValue ha haL z u v * picardCarrierValue ha haL w u v)
    (z.1.1 * w.1.1) (z.1.2 * w.1.1 + z.1.1 * w.1.2)
    (by intro p; simp only [ContinuousMap.mul_apply, picardCarrierValue_coe])
    (by
      intro p hp ht
      simpa only [ContinuousMap.coe_mk, ContinuousMap.add_apply, ContinuousMap.mul_apply,
        Pi.mul_apply, picardCarrierValue_coe] using
        (picardCarrierValue_hasDerivAt ha haL z p hp ht).fun_mul
          (picardCarrierValue_hasDerivAt ha haL w p hp ht))
/-- Multiply complex carriers with the real-parameter product-rule outgoing jet. -/
@[expose] noncomputable def picardCarrierCMul (ha : 0 ≤ a) (haL : a ≤ L)
    (z w : PicardCarrier c a L ℂ) : PicardCarrier c a L ℂ :=
  picardCarrierOfRawDeriv
    (fun u v => picardCarrierValue ha haL z u v * picardCarrierValue ha haL w u v)
    (z.1.1 * w.1.1) (z.1.2 * w.1.1 + z.1.1 * w.1.2)
    (by intro p; simp only [ContinuousMap.mul_apply, picardCarrierValue_coe])
    (by
      intro p hp ht
      simpa only [ContinuousMap.coe_mk, ContinuousMap.add_apply, ContinuousMap.mul_apply,
        Pi.mul_apply, picardCarrierValue_coe] using
        (picardCarrierValue_hasDerivAt ha haL z p hp ht).fun_mul
          (picardCarrierValue_hasDerivAt ha haL w p hp ht))
/-- Real exponentiation preserves outgoing first-jet compatibility. -/
@[expose] noncomputable def picardCarrierExp (ha : 0 ≤ a) (haL : a ≤ L)
    (z : PicardCarrier c a L ℝ) : PicardCarrier c a L ℝ :=
  picardCarrierOfRawDeriv (fun u v => Real.exp (picardCarrierValue ha haL z u v))
    ⟨fun p => Real.exp (z.1.1 p), (Real.continuous_exp.comp z.1.1.continuous)⟩
    ⟨fun p => Real.exp (z.1.1 p) * z.1.2 p,
      (Real.continuous_exp.comp z.1.1.continuous).mul z.1.2.continuous⟩
    (by intro p; simp only [ContinuousMap.coe_mk, picardCarrierValue_coe])
    (by
      intro p hp ht
      simpa only [ContinuousMap.coe_mk, ContinuousMap.add_apply, ContinuousMap.mul_apply,
        Pi.mul_apply, picardCarrierValue_coe] using
        (picardCarrierValue_hasDerivAt ha haL z p hp ht).exp)
/-- Complex exponentiation preserves outgoing first-jet compatibility. -/
@[expose] noncomputable def picardCarrierCexp (ha : 0 ≤ a) (haL : a ≤ L)
    (z : PicardCarrier c a L ℂ) : PicardCarrier c a L ℂ :=
  picardCarrierOfRawDeriv (fun u v => Complex.exp (picardCarrierValue ha haL z u v))
    ⟨fun p => Complex.exp (z.1.1 p), Complex.continuous_exp.comp z.1.1.continuous⟩
    ⟨fun p => Complex.exp (z.1.1 p) * z.1.2 p,
      (Complex.continuous_exp.comp z.1.1.continuous).mul z.1.2.continuous⟩
    (by intro p; simp only [ContinuousMap.coe_mk, picardCarrierValue_coe])
    (by
      intro p hp ht
      simpa only [ContinuousMap.coe_mk, ContinuousMap.add_apply, ContinuousMap.mul_apply,
        Pi.mul_apply, picardCarrierValue_coe] using
        (picardCarrierValue_hasDerivAt ha haL z p hp ht).cexp)

end EmcsfAcExtension.Local
