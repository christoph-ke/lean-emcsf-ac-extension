module

public import EmcsfAcExtension.Local.Construction.PicardUpdateBounds

/-! # Uniform Picard constants for both signs of the coupling

Taking maxima of the two landed signed-coupling estimates fixes the
constants before the signed coupling, cone geometry and candidate data.
-/

public section

namespace EmcsfAcExtension.Local

/-- The two real couplings of a fixed absolute value exhaust the class.
The conclusion also includes zero without a separate convention. -/
theorem wire_coupling_cases {e E : ℝ} (he : |e| = E) : e = E ∨ e = -E := by
  rcases le_total 0 e with h | h
  · exact Or.inl ((abs_of_nonneg h).symm.trans he)
  · right
    have h' : -e = E := (abs_of_nonpos h).symm.trans he
    linarith only [h']

/-- E3 with constants depending only on `ell,B,R,κ,E`, before the signed
coupling of absolute value `E`, all cone geometry, centers and candidates.
The numerical displacement and Lipschitz width factors remain exactly `a`. -/
theorem picardCarrierUpdate_uniform_abs (ell B R κ E : ℝ) (he : 0 < ell)
    (hκ : 0 < κ) (hB : 0 ≤ B) (hR : 0 ≤ R) :
    ∃ K > 0, ∃ C > 0, ∀ e : ℝ, |e| = E →
      ∀ (c a L : ℝ) (ha : 0 ≤ a) (haL : a ≤ L), L ≤ R → a ≤ 1 →
      ∀ (center z w : PicardCarrier c a L (ℝ × ℂ))
        (hlz : ∀ q, ell ≤ (z.1.1 q).1) (hlw : ∀ q, ell ≤ (w.1.1 q).1)
        (hgz : ∀ q, κ ≤ 1 - picardMuValues e ell he z hlz q)
        (hgw : ∀ q, κ ≤ 1 - picardMuValues e ell he w hlw q),
      picardCarrierSize center ≤ B → picardCarrierSize z ≤ B → picardCarrierSize w ≤ B →
      dist (picardCarrierUpdate ha haL e ell κ he hκ center z hlz hgz) center ≤ a * K ∧
      dist (picardCarrierUpdate ha haL e ell κ he hκ center z hlz hgz)
        (picardCarrierUpdate ha haL e ell κ he hκ center w hlw hgw) ≤ a * C * dist z w := by
  obtain ⟨Kp, hKp, Cp, hCp, hp⟩ := picardCarrierUpdate_uniform ell B R κ E he hκ hB hR
  obtain ⟨Km, hKm, Cm, hCm, hm⟩ := picardCarrierUpdate_uniform ell B R κ (-E) he hκ hB hR
  refine ⟨max Kp Km, lt_max_of_lt_left hKp, max Cp Cm, lt_max_of_lt_left hCp, ?_⟩
  intro e habs
  rcases wire_coupling_cases habs with rfl | rfl
  · intro c a L ha haL hLR ha1 center z w hlz hlw hgz hgw hc hz hw
    obtain ⟨hd, hl⟩ := hp c a L ha haL hLR ha1 center z w hlz hlw hgz hgw hc hz hw
    exact ⟨hd.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) ha),
      hl.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_max_left _ _) ha) dist_nonneg)⟩
  · intro c a L ha haL hLR ha1 center z w hlz hlw hgz hgw hc hz hw
    obtain ⟨hd, hl⟩ := hm c a L ha haL hLR ha1 center z w hlz hlw hgz hgw hc hz hw
    exact ⟨hd.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) ha),
      hl.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_max_right _ _) ha) dist_nonneg)⟩

end EmcsfAcExtension.Local
