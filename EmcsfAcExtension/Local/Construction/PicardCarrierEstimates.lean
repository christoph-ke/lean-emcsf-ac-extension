module

public import EmcsfAcExtension.Local.Construction.PicardOutgoingEstimates
public import EmcsfAcExtension.Local.Construction.PicardPolynomial

/-! # Pointwise estimates for the outgoing carrier metric

The carrier norm and distance are exactly maxima of value and outgoing-jet
sup norms. Weighted axis profiles therefore give estimates at the axis as
well as off it.
-/

public section

namespace EmcsfAcExtension.Local

variable {c a L : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- First projection of a continuous product-valued profile. -/
@[expose] def picardProfileFst {A X Y : Type*} [TopologicalSpace A]
    [TopologicalSpace X] [TopologicalSpace Y] (F : C(A, X × Y)) : C(A, X) :=
  ⟨fun p => (F p).1, F.continuous.fst⟩

/-- Second projection of a continuous product-valued profile. -/
@[expose] def picardProfileSnd {A X Y : Type*} [TopologicalSpace A]
    [TopologicalSpace X] [TopologicalSpace Y] (F : C(A, X × Y)) : C(A, Y) :=
  ⟨fun p => (F p).2, F.continuous.snd⟩

/-- First projection has universal sup-norm bound one. -/
theorem picardProfileFst_norm_le {A X Y : Type*} [TopologicalSpace A] [CompactSpace A]
    [NormedAddCommGroup X] [NormedAddCommGroup Y] (F : C(A, X × Y)) :
    ‖picardProfileFst F‖ ≤ ‖F‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro p
  exact (norm_fst_le (F p)).trans (F.norm_coe_le_norm p)

/-- Second projection has universal sup-norm bound one. -/
theorem picardProfileSnd_norm_le {A X Y : Type*} [TopologicalSpace A] [CompactSpace A]
    [NormedAddCommGroup X] [NormedAddCommGroup Y] (F : C(A, X × Y)) :
    ‖picardProfileSnd F‖ ≤ ‖F‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro p
  exact (norm_snd_le (F p)).trans (F.norm_coe_le_norm p)

/-- First projection has universal sup-distance bound one. -/
theorem picardProfileFst_dist_le {A X Y : Type*} [TopologicalSpace A] [CompactSpace A]
    [NormedAddCommGroup X] [NormedAddCommGroup Y] (F G : C(A, X × Y)) :
    dist (picardProfileFst F) (picardProfileFst G) ≤ dist F G := by
  apply (ContinuousMap.dist_le dist_nonneg).mpr
  intro p
  exact (le_max_left _ _).trans (ContinuousMap.dist_apply_le_dist (f := F) (g := G) p)

/-- Second projection has universal sup-distance bound one. -/
theorem picardProfileSnd_dist_le {A X Y : Type*} [TopologicalSpace A] [CompactSpace A]
    [NormedAddCommGroup X] [NormedAddCommGroup Y] (F G : C(A, X × Y)) :
    dist (picardProfileSnd F) (picardProfileSnd G) ≤ dist F G := by
  apply (ContinuousMap.dist_le dist_nonneg).mpr
  intro p
  exact (le_max_right _ _).trans (ContinuousMap.dist_apply_le_dist (f := F) (g := G) p)

/-- Uniform pointwise value and jet bounds give a carrier-size bound with
universal constant one. -/
theorem picardCarrierSize_le_of_pointwise (C : ℝ) (hC : 0 ≤ C)
    (F : PicardCarrier c a L E) (hv : ∀ p, ‖F.1.1 p‖ ≤ C)
    (hj : ∀ p, ‖F.1.2 p‖ ≤ C) : picardCarrierSize F ≤ C :=
  max_le ((ContinuousMap.norm_le _ hC).mpr hv) ((ContinuousMap.norm_le _ hC).mpr hj)

/-- Uniform pointwise value and jet comparisons give a carrier-distance
bound with universal constant one. -/
theorem picardCarrier_dist_le_of_pointwise (C : ℝ) (hC : 0 ≤ C)
    (F G : PicardCarrier c a L E) (hv : ∀ p, dist (F.1.1 p) (G.1.1 p) ≤ C)
    (hj : ∀ p, dist (F.1.2 p) (G.1.2 p) ≤ C) : dist F G ≤ C :=
  max_le ((ContinuousMap.dist_le hC).mpr hv) ((ContinuousMap.dist_le hC).mpr hj)

/-- A width-weighted profile has its exact power bound with upper length
`R`, uniformly in cone position, incoming width, profile and point. -/
theorem picard_width_pow_norm_le_aux (R : ℝ) (hLR : L ≤ R)
    (p : PicardDomain c a L) (n : ℕ) (v : E) :
    ‖(p.1.2 - p.1.1) ^ n • v‖ ≤ R ^ n * ‖v‖ := by
  have hx : 0 ≤ p.1.2 - p.1.1 := sub_nonneg.mpr p.2.1.2.1
  have hxR : p.1.2 - p.1.1 ≤ R :=
    (by linarith [p.2.1.1, p.2.1.2.2] : p.1.2 - p.1.1 ≤ L).trans hLR
  rw [norm_smul, Real.norm_eq_abs, abs_pow, abs_of_nonneg hx]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx hxR n) (norm_nonneg _)

/-- A common width factor preserves the profile comparison with the exact
factor `R^n`, uniformly in geometry and both continuous profiles. -/
theorem picard_width_pow_dist_le_aux (R : ℝ) (hR : 0 ≤ R) (hLR : L ≤ R)
    (p : PicardDomain c a L) (n : ℕ) (F G : C(PicardDomain c a L, E)) :
    dist ((p.1.2 - p.1.1) ^ n • F p) ((p.1.2 - p.1.1) ^ n • G p) ≤
      R ^ n * dist F G := by
  rw [dist_eq_norm, ←smul_sub]
  exact (picard_width_pow_norm_le_aux R hLR p n (F p - G p)).trans
    (mul_le_mul_of_nonneg_left (by
      simpa only [dist_eq_norm] using ContinuousMap.dist_apply_le_dist (f := F) (g := G) p)
      (pow_nonneg hR n))

/-- Two bounded comparison profiles with exact width powers give complete
carrier bounds. The displayed constant depends only on `R,B,m,n`, uniformly
in geometry, carriers, profiles and the nonnegative comparison distance `Δ`. -/
theorem picardCarrier_bounds_of_weighted_profiles (R B Δ : ℝ)
    (hR : 0 ≤ R) (hB : 0 ≤ B) (hΔ : 0 ≤ Δ) (hLR : L ≤ R) (m n : ℕ)
    (F G : PicardCarrier c a L E) (V V' J J' : C(PicardDomain c a L, E))
    (hv : ∀ p, F.1.1 p = (p.1.2 - p.1.1) ^ m • V p)
    (hv' : ∀ p, G.1.1 p = (p.1.2 - p.1.1) ^ m • V' p)
    (hj : ∀ p, F.1.2 p = (p.1.2 - p.1.1) ^ n • J p)
    (hj' : ∀ p, G.1.2 p = (p.1.2 - p.1.1) ^ n • J' p)
    (hnV : ‖V‖ ≤ B) (hnJ : ‖J‖ ≤ B)
    (hdV : dist V V' ≤ B * Δ) (hdJ : dist J J' ≤ B * Δ) :
    picardCarrierSize F ≤ (R ^ m + R ^ n) * B ∧
      dist F G ≤ ((R ^ m + R ^ n) * B) * Δ := by
  have hC : 0 ≤ (R ^ m + R ^ n) * B := by positivity
  have hVm : R ^ m * B ≤ (R ^ m + R ^ n) * B := by
    calc
      _ ≤ R ^ m * B + R ^ n * B := le_add_of_nonneg_right (by positivity)
      _ = _ := by ring
  have hJn : R ^ n * B ≤ (R ^ m + R ^ n) * B := by
    calc
      _ ≤ R ^ m * B + R ^ n * B := le_add_of_nonneg_left (by positivity)
      _ = _ := by ring
  refine ⟨picardCarrierSize_le_of_pointwise _ hC F ?_ ?_,
    picardCarrier_dist_le_of_pointwise _ (mul_nonneg hC hΔ) F G ?_ ?_⟩
  · intro p
    rw [hv p]
    exact ((picard_width_pow_norm_le_aux R hLR p m _).trans
      (mul_le_mul_of_nonneg_left ((V.norm_coe_le_norm p).trans hnV) (pow_nonneg hR m))).trans hVm
  · intro p
    rw [hj p]
    exact ((picard_width_pow_norm_le_aux R hLR p n _).trans
      (mul_le_mul_of_nonneg_left ((J.norm_coe_le_norm p).trans hnJ) (pow_nonneg hR n))).trans hJn
  · intro p
    rw [hv p, hv' p]
    exact (((picard_width_pow_dist_le_aux R hR hLR p m V V').trans
      (mul_le_mul_of_nonneg_left hdV (pow_nonneg hR m))).trans_eq
        (by ring : R ^ m * (B * Δ) = (R ^ m * B) * Δ)).trans
          (mul_le_mul_of_nonneg_right hVm hΔ)
  · intro p
    rw [hj p, hj' p]
    exact (((picard_width_pow_dist_le_aux R hR hLR p n J J').trans
      (mul_le_mul_of_nonneg_left hdJ (pow_nonneg hR n))).trans_eq
        (by ring : R ^ n * (B * Δ) = (R ^ n * B) * Δ)).trans
          (mul_le_mul_of_nonneg_right hJn hΔ)

/-- A fixed continuous real-linear map has its operator-norm Lipschitz
bound on complete carriers, uniformly in geometry and both candidates. -/
theorem picardCarrierLinear_dist_le {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] [CompleteSpace E] [CompleteSpace Y]
    (ha : 0 ≤ a) (haL : a ≤ L) (T : E →L[ℝ] Y)
    (F G : PicardCarrier c a L E) :
    dist (picardCarrierLinear ha haL T F) (picardCarrierLinear ha haL T G) ≤ ‖T‖ * dist F G := by
  apply picardCarrier_dist_le_of_pointwise _ (by positivity)
  · intro p
    rw [dist_eq_norm, picardCarrierLinear_value, picardCarrierLinear_value, ←map_sub]
    exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (by simpa only [dist_eq_norm] using picardCarrier_dist_value_le F G p) (norm_nonneg _))
  · intro p
    rw [dist_eq_norm, picardCarrierLinear_jet, picardCarrierLinear_jet, ←map_sub]
    exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (by simpa only [dist_eq_norm] using picardCarrier_dist_jet_le F G p) (norm_nonneg _))

/-- Carrier negation preserves distance, uniformly in geometry and target. -/
theorem picardCarrierNeg_dist [CompleteSpace E] (ha : 0 ≤ a) (haL : a ≤ L)
    (F G : PicardCarrier c a L E) :
    dist (picardCarrierNeg ha haL F) (picardCarrierNeg ha haL G) = dist F G := by
  change max (dist (-F.1.1) (-G.1.1)) (dist (-F.1.2) (-G.1.2)) = _
  simp only [dist_neg_neg]
  rfl

end EmcsfAcExtension.Local
