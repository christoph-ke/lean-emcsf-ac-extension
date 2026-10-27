module

public import EmcsfAcExtension.Local.Construction.PicardUniformMass
public import EmcsfAcExtension.Local.Construction.PicardCarrierEstimates
public import EmcsfAcExtension.Local.Construction.PicardRealSources
public import EmcsfAcExtension.Local.Construction.PicardSources
import EmcsfAcExtension.Local.Construction.PicardIncomingEstimates

/-! # Uniform bounds for the basic radial reconstruction carriers

The radius, scalar and charge carriers retain both their values and outgoing
jets, with constants chosen before the actual cone length.
-/

public section

namespace EmcsfAcExtension.Local

/-- The radius carrier has a positive uniform size and comparison constant
depending only on `B,R`, for every cone position, incoming width and actual
length at most `R`. -/
theorem picardRadiusRecon_uniform (B R : ℝ) (hB : 0 ≤ B) (hR : 0 ≤ R) :
    ∃ C > 0, ∀ (c a L : ℝ) (ha : 0 ≤ a) (haL : a ≤ L), L ≤ R →
      ∀ (z w : PicardCarrier c a L (ℝ × ℂ)),
      picardCarrierSize z ≤ B → picardCarrierSize w ≤ B →
      picardCarrierSize (picardRadiusRecon ha haL z) ≤ C ∧
      dist (picardRadiusRecon ha haL z) (picardRadiusRecon ha haL w) ≤ C * dist z w := by
  let C := 1 + (1 + R) * B + (1 + R)
  have hC : 0 < C := by dsimp [C]; positivity
  have hCB : (1 + R) * B ≤ C := by dsimp [C]; linarith only [hR]
  have hCR : 1 + R ≤ C := by
    have h0 : 0 ≤ (1 + R) * B := by positivity
    dsimp [C]
    linarith only [h0]
  refine ⟨C, hC, ?_⟩
  intro c a L ha haL hLR z w hz _
  have hn : ‖picardLamValues z‖ ≤ B := (ContinuousMap.norm_le _ hB).mpr
    (picardCarrier_pointwise_bounds_of_size B z hz).1
  have hv : picardCarrierSize (picardRadiusRecon ha haL z) ≤ (1 + R) * B :=
    (picardOutgoing_size_le ha haL _).trans (by gcongr)
  have hd : dist (picardRadiusRecon ha haL z) (picardRadiusRecon ha haL w) ≤
      (1 + R) * dist z w :=
    (picardOutgoing_dist_le ha haL _ _).trans (by gcongr; exact picardLamValues_dist_le z w)
  exact ⟨hv.trans hCB, hd.trans (mul_le_mul_of_nonneg_right hCR dist_nonneg)⟩

/-- The scalar reconstruction has a positive uniform C1 size and comparison
constant depending only on `ell,B,R`, before all cone geometry and candidates. -/
theorem picardScalarRecon_uniform (ell B R : ℝ) (he : 0 < ell) (hB : 0 ≤ B) (hR : 0 ≤ R) :
    ∃ C > 0, ∀ (c a L : ℝ) (ha : 0 ≤ a) (haL : a ≤ L), L ≤ R →
      ∀ (z w : PicardCarrier c a L (ℝ × ℂ))
        (hlz : ∀ q, ell ≤ (z.1.1 q).1) (hlw : ∀ q, ell ≤ (w.1.1 q).1),
      picardCarrierSize z ≤ B → picardCarrierSize w ≤ B →
      picardCarrierSize (picardScalarRecon ha haL ell he z hlz) ≤ C ∧
      dist (picardScalarRecon ha haL ell he z hlz) (picardScalarRecon ha haL ell he w hlw) ≤ C *
          dist z w := by
  obtain ⟨C, hC, hc⟩ := picardScalarCharge_uniform ell B R 0 he hB hR
  refine ⟨C, hC, ?_⟩
  intro c a L ha haL hLR z w hlz hlw hz hw
  obtain ⟨_, _, hv, hdv, hj, hdj, _⟩ := hc c a L (ha.trans haL) hLR z w hlz hlw hz hw
  exact ⟨max_le hv hj, max_le hdv hdj⟩

/-- The charge carrier has a positive uniform C1 size and comparison
constant depending only on `ell,B,R,|e|`, before all geometry and candidates. -/
theorem picardChargeRecon_uniform (ell B R e : ℝ) (he : 0 < ell) (hB : 0 ≤ B) (hR : 0 ≤ R) :
    ∃ C > 0, ∀ (c a L : ℝ) (ha : 0 ≤ a) (haL : a ≤ L), L ≤ R →
      ∀ (z w : PicardCarrier c a L (ℝ × ℂ))
        (hlz : ∀ q, ell ≤ (z.1.1 q).1) (hlw : ∀ q, ell ≤ (w.1.1 q).1),
      picardCarrierSize z ≤ B → picardCarrierSize w ≤ B →
      picardCarrierSize (picardChargeRecon ha haL e ell he z hlz) ≤ C ∧
      dist (picardChargeRecon ha haL e ell he z hlz) (picardChargeRecon ha haL e ell he w hlw) ≤ C *
          dist z w := by
  obtain ⟨S, hS, hs⟩ := picardScalarCharge_uniform ell B R e he hB hR
  let C := 1 + (R ^ 3 + R ^ 2) * S
  have hC : 0 < C := by dsimp [C]; positivity
  have hCC : (R ^ 3 + R ^ 2) * S ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro c a L ha haL hLR z w hlz hlw hz hw
  obtain ⟨_, _, _, _, _, _, hkn, hkd, hqn, hqd⟩ :=
    hs c a L (ha.trans haL) hLR z w hlz hlw hz hw
  obtain ⟨hn, hd⟩ := picardCarrier_bounds_of_weighted_profiles R S (dist z w)
    hR hS.le dist_nonneg hLR 3 2
    (picardChargeRecon ha haL e ell he z hlz) (picardChargeRecon ha haL e ell he w hlw)
    (picardChargeRemainder e ell he z hlz) (picardChargeRemainder e ell he w hlw)
    (picardChargeKernel e ell he z hlz) (picardChargeKernel e ell he w hlw)
    (fun p =>
        by simpa only [smul_eq_mul] using picardChargeRecon_normalized ha haL e ell he z hlz p)
    (fun p =>
        by simpa only [smul_eq_mul] using picardChargeRecon_normalized ha haL e ell he w hlw p)
    (fun p => by simpa only [smul_eq_mul] using picardChargeRecon_jet ha haL e ell he z hlz p)
    (fun p => by simpa only [smul_eq_mul] using picardChargeRecon_jet ha haL e ell he w hlw p)
    hqn hkn hqd hkd
  exact ⟨hn.trans hCC, hd.trans (mul_le_mul_of_nonneg_right hCC dist_nonneg)⟩

/-- The complete mass carrier has a positive uniform C1 size and comparison
constant depending only on `ell,B,R,|e|`, before all geometry and candidates.
The estimate retains the cubic value and quadratic outgoing-jet orders. -/
theorem picardMassRecon_uniform (ell B R e : ℝ) (he : 0 < ell) (hB : 0 ≤ B) (hR : 0 ≤ R) :
    ∃ C > 0, ∀ (c a L : ℝ) (ha : 0 ≤ a) (haL : a ≤ L), L ≤ R →
      ∀ (z w : PicardCarrier c a L (ℝ × ℂ))
        (hlz : ∀ q, ell ≤ (z.1.1 q).1) (hlw : ∀ q, ell ≤ (w.1.1 q).1),
      picardCarrierSize z ≤ B → picardCarrierSize w ≤ B →
      picardCarrierSize (picardMassRecon ha haL e ell he z hlz) ≤ C ∧
      dist (picardMassRecon ha haL e ell he z hlz) (picardMassRecon ha haL e ell he w hlw) ≤ C *
          dist z w := by
  obtain ⟨M, hM, hm⟩ := picardMass_uniform ell B R e he hB hR
  let S := R ^ 3 * M + (R ^ 2 * M + M * (R ^ 3 * M))
  let K := (R ^ 3 + R ^ 3 * M) * (M + R * M * M) + R ^ 2 * M + R ^ 3 * M * M
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨1 + S + K, by positivity, ?_⟩
  intro c a L ha haL hLR z w hlz hlw hz hw
  have hL : 0 ≤ L := ha.trans haL
  obtain ⟨hamz, hkernelz, hrestz, had, hkd, _⟩ := hm c a L hL hLR z w hlz hlw hz hw
  have hkernelw := (hm c a L hL hLR w z hlw hlz hw hz).2.1
  have hvalue (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
      (hz : picardCarrierSize z ≤ B) (p : PicardDomain c a L) :
      ‖(picardMassRecon ha haL e ell he z hl).1.1 p‖ ≤ R ^ 3 * M := by
    have hrest := (hm c a L hL hLR z z hl hl hz hz).2.2.1
    rw [picardMassRecon_normalized]
    exact (picard_width_pow_norm_le_aux (E := ℝ) R hLR p 3 _).trans
      (mul_le_mul_of_nonneg_left (((picardMassRemainder e ell he z hl).norm_coe_le_norm p).trans
          hrest)
        (pow_nonneg hR 3))
  have hsize : picardCarrierSize (picardMassRecon ha haL e ell he z hlz) ≤ S := by
    apply picardCarrierSize_le_of_pointwise S hS
    · intro p
      have h0 : 0 ≤ R ^ 2 * M + M * (R ^ 3 * M) := by positivity
      exact (hvalue z hlz hz p).trans (by dsimp [S]; linarith only [h0])
    · intro p
      rw [picardMassRecon_jet]
      have hbm : ‖picardMassBm e ell he z hlz p‖ ≤ R ^ 2 * M := by
        exact (picard_width_pow_norm_le_aux (E := ℝ) R hLR p 2 _).trans
          (mul_le_mul_of_nonneg_left (((picardMassKernel e ell he z hlz).norm_coe_le_norm p).trans
              hkernelz)
            (sq_nonneg R))
      have ham : ‖picardMassAm ell he z hlz p‖ ≤ M :=
        ((picardMassAm ell he z hlz).norm_coe_le_norm p).trans hamz
      calc
        _ ≤ ‖picardMassBm e ell he z hlz p‖ +
            ‖picardMassAm ell he z hlz p * (picardMassRecon ha haL e ell he z hlz).1.1 p‖ :=
                norm_sub_le _ _
        _ ≤ R ^ 2 * M + M * (R ^ 3 * M) := add_le_add hbm
          ((norm_mul_le _ _).trans (mul_le_mul ham (hvalue z hlz hz p) (norm_nonneg _) hM.le))
        _ ≤ S := by
          have h0 : 0 ≤ R ^ 3 * M := by positivity
          dsimp [S]
          linarith only [h0]
  have hdist : dist (picardMassRecon ha haL e ell he z hlz)
      (picardMassRecon ha haL e ell he w hlw) ≤ K * dist z w := by
    have h := picardMassRecon_dist_le_coefficients ha haL e ell he z w hlz hlw
    dsimp only at h
    calc
      _ ≤ (L ^ 3 + L ^ 3 * ‖picardMassAm ell he z hlz‖) *
          (dist (picardMassKernel e ell he z hlz) (picardMassKernel e ell he w hlw) +
            L * ‖picardMassKernel e ell he w hlw‖ * dist (picardMassAm ell he z hlz) (picardMassAm
                ell he w hlw)) +
          L ^ 2 * dist (picardMassKernel e ell he z hlz) (picardMassKernel e ell he w hlw) +
          L ^ 3 * ‖picardMassKernel e ell he w hlw‖ * dist (picardMassAm ell he z hlz) (picardMassAm
              ell he w hlw) := h
      _ ≤ (R ^ 3 + R ^ 3 * M) * (M * dist z w + R * M * (M * dist z w)) +
          R ^ 2 * (M * dist z w) + R ^ 3 * M * (M * dist z w) := by gcongr
      _ = K * dist z w := by dsimp [K]; ring
  exact ⟨hsize.trans (by linarith only [hK]),
    hdist.trans (mul_le_mul_of_nonneg_right (by linarith only [hS]) dist_nonneg)⟩

/-- The normalized scalar difference `h-phi` has a positive uniform C1 size
and comparison constant depending only on `ell,B,R`, before all geometry and
candidates. This uses the existing derivative-compatible difference carrier. -/
theorem picardScalarDifferenceRecon_uniform (ell B R : ℝ) (he : 0 < ell)
    (hB : 0 ≤ B) (hR : 0 ≤ R) :
    ∃ C > 0, ∀ (c a L : ℝ) (ha : 0 ≤ a) (haL : a ≤ L), L ≤ R →
      ∀ (z w : PicardCarrier c a L (ℝ × ℂ))
        (hlz : ∀ q, ell ≤ (z.1.1 q).1) (hlw : ∀ q, ell ≤ (w.1.1 q).1),
      picardCarrierSize z ≤ B → picardCarrierSize w ≤ B →
      picardCarrierSize (picardScalarDifferenceRecon ha haL ell he z hlz) ≤ C ∧
      dist (picardScalarDifferenceRecon ha haL ell he z hlz)
        (picardScalarDifferenceRecon ha haL ell he w hlw) ≤ C * dist z w := by
  obtain ⟨S, hS, hs⟩ := picardScalarRecon_uniform ell B R he hB hR
  let C := 1 + (B + S) + (1 + S)
  have hC : 0 < C := by dsimp [C]; positivity
  have hBC : B + S ≤ C := by dsimp [C]; linarith only [hS]
  have hSC : 1 + S ≤ C := by dsimp [C]; linarith only [hB, hS]
  refine ⟨C, hC, ?_⟩
  intro c a L ha haL hLR z w hlz hlw hz hw
  obtain ⟨hphin, hphid⟩ := hs c a L ha haL hLR z w hlz hlw hz hw
  let Hz := picardCarrierLinear ha haL (ContinuousLinearMap.snd ℝ ℝ ℂ) z
  let Hw := picardCarrierLinear ha haL (ContinuousLinearMap.snd ℝ ℝ ℂ) w
  have hHz : picardCarrierSize Hz ≤ B :=
    (picardCarrierLinear_size_le ha haL _ z).trans
      ((mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_snd_le ℝ ℝ ℂ)
        (picardCarrierSize_nonneg z)).trans (by simpa only [one_mul] using hz))
  have hH : dist Hz Hw ≤ dist z w :=
    (picardCarrierLinear_dist_le ha haL _ z w).trans
      (by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_snd_le ℝ ℝ ℂ)
            (dist_nonneg : 0 ≤ dist z w))
  have hn : picardCarrierSize (picardScalarDifferenceRecon ha haL ell he z hlz) ≤ B + S := by
    change picardCarrierSize (picardCarrierAdd ha haL Hz
      (picardCarrierNeg ha haL (picardScalarRecon ha haL ell he z hlz))) ≤ _
    exact (picardCarrierSize_add_le ha haL _ _).trans
      (add_le_add hHz (by simpa only [picardCarrierSize_neg] using hphin))
  have hd : dist (picardScalarDifferenceRecon ha haL ell he z hlz)
      (picardScalarDifferenceRecon ha haL ell he w hlw) ≤ (1 + S) * dist z w := by
    calc
      _ ≤ dist Hz Hw + dist (picardCarrierNeg ha haL (picardScalarRecon ha haL ell he z hlz))
          (picardCarrierNeg ha haL (picardScalarRecon ha haL ell he w hlw)) :=
              picardCarrierAdd_dist_le ha haL _ _ _ _
      _ ≤ dist z w + S * dist z w := add_le_add hH
        (by simpa only [picardCarrierNeg_dist] using hphid)
      _ = _ := by ring
  exact ⟨hn.trans hBC, hd.trans (mul_le_mul_of_nonneg_right hSC dist_nonneg)⟩

end EmcsfAcExtension.Local
