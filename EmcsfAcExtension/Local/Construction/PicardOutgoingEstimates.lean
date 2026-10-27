module

public import EmcsfAcExtension.Local.Construction.PicardIntegral
public import EmcsfAcExtension.Local.Construction.PicardCarrierBounds
public import EmcsfAcExtension.Local.Construction.PicardCoefficients

/-! # Quantitative outgoing primitives and axis evaluation

Outgoing integration and axis evaluation preserve uniform bounds without
any incoming derivative of a candidate. All displayed constants are explicit.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

variable {c a L : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Outgoing integration has sup-distance bound `L`, uniformly in the
incoming width, cone position, target, and both continuous profiles. -/
theorem picardOutgoingComponent_dist_le (ha : 0 ≤ a) (haL : a ≤ L)
    (f g : C(PicardDomain c a L, E)) :
    dist (picardOutgoingComponent ha haL f) (picardOutgoingComponent ha haL g) ≤ L * dist f g := by
  have hL : 0 ≤ L := ha.trans haL
  apply (ContinuousMap.dist_le (by positivity)).mpr
  intro p
  have hi (f : C(PicardDomain c a L, E)) : IntervalIntegrable
      (fun s => f (picardClamp ha haL (p.1.1, s))) volume p.1.1 p.1.2 :=
    (f.continuous.comp ((continuous_picardClamp ha haL).comp
      (continuous_const.prodMk continuous_id))).intervalIntegrable _ _
  change dist (∫ s in p.1.1..p.1.2, f (picardClamp ha haL (p.1.1, s)))
    (∫ s in p.1.1..p.1.2, g (picardClamp ha haL (p.1.1, s))) ≤ _
  rw [dist_eq_norm, ←intervalIntegral.integral_sub (hi f) (hi g)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun s => f (picardClamp ha haL (p.1.1, s)) - g (picardClamp ha haL (p.1.1, s)))
    (a := p.1.1) (b := p.1.2) (fun s _ => by
      simpa only [dist_eq_norm] using ContinuousMap.dist_apply_le_dist
        (f := f) (g := g) (picardClamp ha haL (p.1.1, s)))
  rw [abs_of_nonneg (sub_nonneg.mpr p.2.1.2.1)] at hb
  have hw : p.1.2 - p.1.1 ≤ L := by linarith [p.2.1.1, p.2.1.2.2]
  exact hb.trans (by
    simpa only [mul_comm, dist_eq_norm] using
      mul_le_mul_of_nonneg_left hw (dist_nonneg : 0 ≤ dist f g))

/-- An outgoing primitive has carrier distance at most `(1+L)` times its
source-profile distance, uniformly in cone position and incoming width. -/
theorem picardOutgoing_dist_le [CompleteSpace E] (ha : 0 ≤ a) (haL : a ≤ L)
    (f g : C(PicardDomain c a L, E)) :
    dist (picardOutgoing ha haL f) (picardOutgoing ha haL g) ≤ (1 + L) * dist f g := by
  have hL : 0 ≤ L := ha.trans haL
  change max (dist (picardOutgoingComponent ha haL f) (picardOutgoingComponent ha haL g)) (dist f g)
      ≤ _
  apply max_le
  · exact (picardOutgoingComponent_dist_le ha haL f g).trans
      (mul_le_mul_of_nonneg_right (by linarith) dist_nonneg)
  · have h0 := mul_nonneg hL (dist_nonneg : 0 ≤ dist f g)
    nlinarith only [h0]

/-- An outgoing primitive has carrier size at most `(1+L)` times its
source norm, uniformly in cone position and incoming width. -/
theorem picardOutgoing_size_le [CompleteSpace E] (ha : 0 ≤ a) (haL : a ≤ L)
    (f : C(PicardDomain c a L, E)) :
    picardCarrierSize (picardOutgoing ha haL f) ≤ (1 + L) * ‖f‖ := by
  have hz : picardOutgoing ha haL (0 : C(PicardDomain c a L, E)) = picardCarrierConst 0 := by
    apply Subtype.ext
    apply Prod.ext <;> apply ContinuousMap.ext <;> intro p
    · simp [picardOutgoing, picardOutgoingComponent, picardCarrierOfRawDeriv, picardCarrierConst]
    · rfl
  have h := picardOutgoing_dist_le ha haL f (0 : C(PicardDomain c a L, E))
  simpa only [hz, picardCarrier_dist_zero, dist_zero_right] using h

/-- Axis evaluation has size bound `U` if the candidate expansion has that
bound. Its outgoing jet is zero, independently of the incoming axis trace. -/
theorem picardAxisLam_size_le (ha : 0 ≤ a) (haL : a ≤ L) (U : ℝ) (hU : 0 ≤ U)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hz : ∀ p, |(z.1.1 p).1| ≤ U) :
    picardCarrierSize (picardAxisLam ha haL z) ≤ U := by
  apply max_le
  · apply (ContinuousMap.norm_le _ hU).mpr
    intro p
    exact hz (picardRadialPoint p 0)
  · simpa only [picardAxisLam, picardCarrierOfRawDeriv, picardCarrierSize,
      norm_zero, show (ContinuousMap.const (PicardDomain c a L) (0 : ℝ)) = 0 from rfl] using hU

/-- Axis evaluation has universal carrier Lipschitz constant one. -/
theorem picardAxisLam_dist_le (ha : 0 ≤ a) (haL : a ≤ L)
    (z w : PicardCarrier c a L (ℝ × ℂ)) :
    dist (picardAxisLam ha haL z) (picardAxisLam ha haL w) ≤ dist z w := by
  apply max_le
  · apply (ContinuousMap.dist_le dist_nonneg).mpr
    intro p
    exact (le_max_left _ _).trans (picardCarrier_dist_value_le z w (picardRadialPoint p 0))
  · simpa only [picardAxisLam, picardCarrierOfRawDeriv, dist_self] using
      (dist_nonneg : 0 ≤ dist z w)

end EmcsfAcExtension.Local
