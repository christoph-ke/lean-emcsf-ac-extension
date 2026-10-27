module

public import EmcsfAcExtension.Local.Construction.PicardIncoming
public import EmcsfAcExtension.Local.Construction.PicardDivision

/-! # Quantitative carrier algebra

The metric size is the maximum value/jet norm. Incoming integration gains its
strip length, and multiplication has the explicit universal C1 product bound.
-/

public section

open Set MeasureTheory Filter Topology
open scoped Topology

namespace EmcsfAcExtension.Local

variable {c a L : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The maximum of the value and outgoing-jet sup norms. -/
@[expose] noncomputable def picardCarrierSize (F : PicardCarrier c a L E) : ℝ := max ‖F.1.1‖ ‖F.1.2‖
/-- The carrier size is nonnegative, universally in the target and geometry. -/
theorem picardCarrierSize_nonneg (F : PicardCarrier c a L E) : 0 ≤ picardCarrierSize F :=
  (norm_nonneg _).trans (le_max_left _ _)
/-- The value sup norm is at most the carrier size, with universal constant one. -/
theorem picardCarrierSize_values_le (F : PicardCarrier c a L E) : ‖F.1.1‖ ≤ picardCarrierSize F :=
    le_max_left _ _
/-- The outgoing-jet sup norm is at most the carrier size, with universal constant one. -/
theorem picardCarrierSize_jets_le (F : PicardCarrier c a L E) : ‖F.1.2‖ ≤ picardCarrierSize F :=
    le_max_right _ _
/-- A constant carrier has size at most its value norm, uniformly even on an empty domain. -/
theorem picardCarrierSize_const_le (k : E) : picardCarrierSize (picardCarrierConst (c := c) (a := a)
    (L := L) k) ≤ ‖k‖ := by
  apply max_le
  · exact (ContinuousMap.norm_le _ (norm_nonneg k)).mpr (fun _ => le_rfl)
  · apply (ContinuousMap.norm_le _ (norm_nonneg k)).mpr
    intro p
    change ‖(0 : E)‖ ≤ ‖k‖
    simpa only [norm_zero] using norm_nonneg k
/-- Distance from the zero carrier equals the carrier size. -/
theorem picardCarrier_dist_zero (F : PicardCarrier c a L E) :
    dist F (picardCarrierConst 0) = picardCarrierSize F := by
  change max (dist F.1.1 (ContinuousMap.const _ 0)) (dist F.1.2 (ContinuousMap.const _ 0)) = _
  simp only [show (ContinuousMap.const (PicardDomain c a L) (0 : E)) = 0 from rfl, dist_zero_right,
      picardCarrierSize]
/-- The carrier size obeys the metric triangle inequality with universal coefficient one. -/
theorem picardCarrierSize_le_dist_add (F G : PicardCarrier c a L E) : picardCarrierSize F ≤ dist F G
    + picardCarrierSize G := by
  rw [←picardCarrier_dist_zero F, ←picardCarrier_dist_zero G]
  exact dist_triangle F G (picardCarrierConst 0)

/-- Incoming integration gains the strip width `a` in carrier size,
uniformly in `c,L, E` and the candidate. -/
theorem picardCarrierSize_incoming_le [CompleteSpace E] (ha : 0 ≤ a) (haL : a ≤ L)
    (F : PicardCarrier c a L E) : picardCarrierSize (picardIncoming ha haL F) ≤ a *
        picardCarrierSize F := by
  have h0 : picardIncomingComponent ha haL (0 : C(PicardDomain c a L, E)) = 0 := by
    ext p
    simp [picardIncomingComponent]
  have hn (f : C(PicardDomain c a L, E)) : ‖picardIncomingComponent ha haL f‖ ≤ a * ‖f‖ := by
    simpa only [h0, dist_zero_right] using picardIncomingComponent_dist_le ha haL f 0
  exact max_le ((hn F.1.1).trans (mul_le_mul_of_nonneg_left (picardCarrierSize_values_le F) ha))
    ((hn F.1.2).trans (mul_le_mul_of_nonneg_left (picardCarrierSize_jets_le F) ha))
/-- Carrier addition has the universal size bound given by the sum of sizes. -/
theorem picardCarrierSize_add_le [CompleteSpace E] (ha : 0 ≤ a) (haL : a ≤ L)
    (F G : PicardCarrier c a L E) : picardCarrierSize (picardCarrierAdd ha haL F G) ≤
        picardCarrierSize F + picardCarrierSize G := by
  change max ‖F.1.1 + G.1.1‖ ‖F.1.2 + G.1.2‖ ≤ _
  exact max_le ((norm_add_le _ _).trans (add_le_add (picardCarrierSize_values_le F)
      (picardCarrierSize_values_le G)))
    ((norm_add_le _ _).trans (add_le_add (picardCarrierSize_jets_le F) (picardCarrierSize_jets_le
        G)))
/-- Carrier negation preserves size. -/
theorem picardCarrierSize_neg [CompleteSpace E] (ha : 0 ≤ a) (haL : a ≤ L)
    (F : PicardCarrier c a L E) : picardCarrierSize (picardCarrierNeg ha haL F) = picardCarrierSize
        F := by
  change max ‖ - F.1.1‖ ‖ - F.1.2‖ = _
  simp only [norm_neg, picardCarrierSize]

private theorem picard_jet_product_size_aux {R : Type*} [NormedRing R] (F G : R × R) :
    max ‖F.1 * G.1‖ ‖F.2 * G.1 + F.1 * G.2‖ ≤ 2 * (max ‖F.1‖ ‖F.2‖) * (max ‖G.1‖ ‖G.2‖) := by
  let B := max ‖F.1‖ ‖F.2‖
  let C := max ‖G.1‖ ‖G.2‖
  have hB : 0 ≤ B := (norm_nonneg _).trans (le_max_left _ _)
  have hC : 0 ≤ C := (norm_nonneg _).trans (le_max_left _ _)
  have h11 : ‖F.1 * G.1‖ ≤ B * C := (norm_mul_le _ _).trans
    (mul_le_mul (le_max_left _ _) (le_max_left _ _) (norm_nonneg _) hB)
  have h21 : ‖F.2 * G.1‖ ≤ B * C := (norm_mul_le _ _).trans
    (mul_le_mul (le_max_right _ _) (le_max_left _ _) (norm_nonneg _) hB)
  have h12 : ‖F.1 * G.2‖ ≤ B * C := (norm_mul_le _ _).trans
    (mul_le_mul (le_max_left _ _) (le_max_right _ _) (norm_nonneg _) hB)
  apply max_le
  · exact h11.trans (by change B * C ≤ 2 * B * C; linarith only [mul_nonneg hB hC])
  · exact (norm_add_le _ _).trans ((add_le_add h21 h12).trans_eq (by ring))

/-- Real carrier multiplication has size at most twice the product of sizes.
The numerical factor two is universal in the geometry and candidates. -/
theorem picardCarrierSize_mul_le (ha : 0 ≤ a) (haL : a ≤ L) (F G : PicardCarrier c a L ℝ) :
    picardCarrierSize (picardCarrierMul ha haL F G) ≤ 2 * picardCarrierSize F * picardCarrierSize G
        :=
  picard_jet_product_size_aux F.1 G.1
/-- Complex carrier multiplication has size at most twice the product of sizes.
The numerical factor two is universal in the geometry and candidates. -/
theorem picardCarrierSize_cmul_le (ha : 0 ≤ a) (haL : a ≤ L) (F G : PicardCarrier c a L ℂ) :
    picardCarrierSize (picardCarrierCMul ha haL F G) ≤ 2 * picardCarrierSize F * picardCarrierSize G
        :=
  picard_jet_product_size_aux F.1 G.1

end EmcsfAcExtension.Local
