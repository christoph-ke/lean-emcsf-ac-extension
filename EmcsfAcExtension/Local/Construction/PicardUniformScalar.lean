module

public import EmcsfAcExtension.Local.Construction.PicardChargeEstimates
public import EmcsfAcExtension.Local.Construction.PicardCarrierBounds

/-! # Scalar and charge bounds uniform in short cone length

The displayed upper cone length is fixed before the actual length. This
quantifier order is needed for the uniform restart time in internal project record E5.
-/

public section

namespace EmcsfAcExtension.Local

variable {c a L : ℝ}

/-- A carrier-size bound controls both values and both outgoing jets with
universal coordinate constant one, uniformly in all domain points. -/
theorem picardCarrier_pointwise_bounds_of_size (B : ℝ)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hz : picardCarrierSize z ≤ B) :
    (∀ p, |(z.1.1 p).1| ≤ B) ∧ (∀ p, ‖(z.1.1 p).2‖ ≤ B) ∧
      (∀ p, |(z.1.2 p).1| ≤ B) ∧ (∀ p, ‖(z.1.2 p).2‖ ≤ B) := by
  have hv (p : PicardDomain c a L) : ‖z.1.1 p‖ ≤ B :=
    (z.1.1.norm_coe_le_norm p).trans ((picardCarrierSize_values_le z).trans hz)
  have hj (p : PicardDomain c a L) : ‖z.1.2 p‖ ≤ B :=
    (z.1.2.norm_coe_le_norm p).trans ((picardCarrierSize_jets_le z).trans hz)
  exact ⟨fun p => (norm_fst_le _).trans (hv p), fun p => (norm_snd_le _).trans (hv p),
    fun p => (norm_fst_le _).trans (hj p), fun p => (norm_snd_le _).trans (hj p)⟩

/-- The scalar remainder, scalar value and first jet, charge kernel and
normalized cubic charge have a common positive size and comparison constant.
It depends only on `ell,B,R,|e|`, uniformly in cone position, incoming width,
and every actual cone length `0 ≤ L ≤ R`. -/
theorem picardScalarCharge_uniform (ell B R e : ℝ) (he : 0 < ell)
    (hB : 0 ≤ B) (hR : 0 ≤ R) :
    ∃ C > 0, ∀ (c a L : ℝ), 0 ≤ L → L ≤ R →
      ∀ (z w : PicardCarrier c a L (ℝ × ℂ))
        (hlz : ∀ q, ell ≤ (z.1.1 q).1) (hlw : ∀ q, ell ≤ (w.1.1 q).1),
      picardCarrierSize z ≤ B → picardCarrierSize w ≤ B →
      ‖picardScalarRemainder ell he z hlz‖ ≤ C ∧
      dist (picardScalarRemainder ell he z hlz) (picardScalarRemainder ell he w hlw) ≤ C * dist z w
          ∧
      ‖picardPhiValues ell he z hlz‖ ≤ C ∧
      dist (picardPhiValues ell he z hlz) (picardPhiValues ell he w hlw) ≤ C * dist z w ∧
      ‖picardPhiJets ell he z hlz‖ ≤ C ∧
      dist (picardPhiJets ell he z hlz) (picardPhiJets ell he w hlw) ≤ C * dist z w ∧
      ‖picardChargeKernel e ell he z hlz‖ ≤ C ∧
      dist (picardChargeKernel e ell he z hlz) (picardChargeKernel e ell he w hlw) ≤ C * dist z w ∧
      ‖picardChargeRemainder e ell he z hlz‖ ≤ C ∧
      dist (picardChargeRemainder e ell he z hlz) (picardChargeRemainder e ell he w hlw) ≤ C * dist
          z w := by
  let F := ell⁻¹ * (B * B / 2)
  let Cf := ell⁻¹ * ((B + B) / 2) + ell⁻¹ ^ 2 * (B * B / 2)
  let V := B + R * F
  let Cv := 1 + R * Cf
  let J := B * ell⁻¹ * F
  let Cj := B * ell⁻¹ * Cf + (ell⁻¹ + B * ell⁻¹ ^ 2) * F
  let Q := |e| * B * B * V * F
  let Cq := |e| * (B * B * (V * Cf + Cv * F) + (2 * B) * (V * F))
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hCf : 0 ≤ Cf := by dsimp [Cf]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hCv : 0 ≤ Cv := by dsimp [Cv]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hCj : 0 ≤ Cj := by dsimp [Cj]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hCq : 0 ≤ Cq := by dsimp [Cq]; positivity
  let C := 1 + F + Cf + V + Cv + J + Cj + Q + Cq
  have hC : 0 < C := by dsimp [C]; positivity
  have hFC : F ≤ C := by dsimp [C]; linarith only [hCf, hV, hCv, hJ, hCj, hQ, hCq]
  have hCfC : Cf ≤ C := by dsimp [C]; linarith only [hF, hV, hCv, hJ, hCj, hQ, hCq]
  have hVC : V ≤ C := by dsimp [C]; linarith only [hF, hCf, hCv, hJ, hCj, hQ, hCq]
  have hCvC : Cv ≤ C := by dsimp [C]; linarith only [hF, hCf, hV, hJ, hCj, hQ, hCq]
  have hJC : J ≤ C := by dsimp [C]; linarith only [hF, hCf, hV, hCv, hCj, hQ, hCq]
  have hCjC : Cj ≤ C := by dsimp [C]; linarith only [hF, hCf, hV, hCv, hJ, hQ, hCq]
  have hQC : Q ≤ C := by dsimp [C]; linarith only [hF, hCf, hV, hCv, hJ, hCj, hCq]
  have hCqC : Cq ≤ C := by dsimp [C]; linarith only [hF, hCf, hV, hCv, hJ, hCj, hQ]
  refine ⟨C, hC, ?_⟩
  intro c a L hL hLR z w hlz hlw hz hw
  obtain ⟨hzl, hzh, _, hzj⟩ := picardCarrier_pointwise_bounds_of_size B z hz
  obtain ⟨hwl, hwh, _, hwj⟩ := picardCarrier_pointwise_bounds_of_size B w hw
  have hfn := picardScalarRemainder_norm_le ell B B he hB hB z hlz hzl hzj
  have hfd := picardScalarRemainder_dist_le ell B B he hB hB z w hlz hlw hzl hwl hzj hwj
  have hvn : ‖picardPhiValues ell he z hlz‖ ≤ V :=
    (picardPhiValues_norm_le ell B B B he hB hB hB hL z hlz hzl hzj hzh).trans
      (by change B + L * F ≤ B + R * F; gcongr)
  have hvd : dist (picardPhiValues ell he z hlz) (picardPhiValues ell he w hlw) ≤ Cv * dist z w :=
    (picardPhiValues_dist_le ell B B he hB hB z w hlz hlw hzl hwl hzj hwj hL).trans
      (mul_le_mul_of_nonneg_right (by change 1 + L * Cf ≤ 1 + R * Cf; gcongr) dist_nonneg)
  have hjn := picardPhiJets_norm_le ell B B he hB hB z hlz hzl hzj
  have hjd := picardPhiJets_dist_le ell B B he hB hB z w hlz hlw hzl hwl hzj hwj
  have hkn : ‖picardChargeKernel e ell he z hlz‖ ≤ Q :=
    (picardChargeKernel_norm_le ell B B B e he hB hB hB hL z hlz hzl hzj hzh).trans
      (by change |e| * B * B * (B + L * F) * F ≤ Q; dsimp only [Q, V]; gcongr)
  have hkd : dist (picardChargeKernel e ell he z hlz) (picardChargeKernel e ell he w hlw) ≤ Cq *
      dist z w :=
    (picardChargeKernel_dist_le ell B B B e he hB hB hB hL z w hlz hlw hzl hwl hzj hwj hzh
        hwh).trans
      (mul_le_mul_of_nonneg_right (by
        change |e| * (B * B * ((B + L * F) * Cf + (1 + L * Cf) * F) +
          (2 * B) * ((B + L * F) * F)) ≤ Cq
        dsimp only [Cq, V, Cv]
        gcongr) dist_nonneg)
  have hqn : ‖picardChargeRemainder e ell he z hlz‖ ≤ Q :=
    (picardChargeRemainder_norm_le ell B B B e he hB hB hB hL z hlz hzl hzj hzh).trans
      (by change |e| * B * B * (B + L * F) * F ≤ Q; dsimp only [Q, V]; gcongr)
  have hqd : dist (picardChargeRemainder e ell he z hlz) (picardChargeRemainder e ell he w hlw) ≤ Cq
      * dist z w :=
    (picardChargeRemainder_dist_le ell B B B e he hB hB hB hL z w hlz hlw hzl hwl hzj hwj hzh
        hwh).trans
      (mul_le_mul_of_nonneg_right (by
        change |e| * (B * B * ((B + L * F) * Cf + (1 + L * Cf) * F) +
          (2 * B) * ((B + L * F) * F)) ≤ Cq
        dsimp only [Cq, V, Cv]
        gcongr) dist_nonneg)
  exact ⟨hfn.trans hFC, hfd.trans (mul_le_mul_of_nonneg_right hCfC dist_nonneg),
    hvn.trans hVC, hvd.trans (mul_le_mul_of_nonneg_right hCvC dist_nonneg),
    hjn.trans hJC, hjd.trans (mul_le_mul_of_nonneg_right hCjC dist_nonneg),
    hkn.trans hQC, hkd.trans (mul_le_mul_of_nonneg_right hCqC dist_nonneg),
    hqn.trans hQC, hqd.trans (mul_le_mul_of_nonneg_right hCqC dist_nonneg)⟩

end EmcsfAcExtension.Local
