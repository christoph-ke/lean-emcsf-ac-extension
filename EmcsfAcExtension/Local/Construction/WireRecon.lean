module

public import EmcsfAcExtension.Local.Construction.WireCarrier

/-! # Locality of the literal radial reconstruction

All radial formulas read only the closed outgoing section ending at the
evaluation point. This permits different total representatives of a carrier.
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- Equal value pairs on one closed outgoing section give equal literal
radial reconstructions there. This uses no differentiability or bounds and
includes the diagonal, where the scalar has its prescribed axis value. -/
theorem recon_eq_of_pair_eqOn {e u v : ℝ} {lam lam' : ℝ → ℝ → ℝ}
    {hh hh' : ℝ → ℝ → ℂ} (huv : u ≤ v)
    (hl : EqOn (lam u) (lam' u) (Icc u v))
    (hhEq : EqOn (hh u) (hh' u) (Icc u v)) :
    Recon.r lam u v = Recon.r lam' u v ∧
    Recon.phi lam hh u v = Recon.phi lam' hh' u v ∧
    Recon.ratio lam hh u v = Recon.ratio lam' hh' u v ∧
    Recon.Q e lam hh u v = Recon.Q e lam' hh' u v ∧
    Recon.m e lam hh u v = Recon.m e lam' hh' u v ∧
    Recon.mu e lam hh u v = Recon.mu e lam' hh' u v ∧
    Recon.z e lam hh u v = Recon.z e lam' hh' u v ∧
    Recon.nu e lam hh u v = Recon.nu e lam' hh' u v ∧
    Recon.A e lam hh u v = Recon.A e lam' hh' u v := by
  have hsub {t s : ℝ} (ht : t ∈ Icc u v) (hs : s ∈ uIcc u t) : s ∈ Icc u v := by
    rw [uIcc_of_le ht.1] at hs
    exact ⟨hs.1, hs.2.trans ht.2⟩
  have hr (t : ℝ) (ht : t ∈ Icc u v) : Recon.r lam u t = Recon.r lam' u t := by
    apply intervalIntegral.integral_congr
    intro s hs
    exact hl (hsub ht hs)
  have hp (t : ℝ) (ht : t ∈ Icc u v) :
      Recon.phi lam hh u t = Recon.phi lam' hh' u t := by
    simp only [Recon.phi, hr t ht]
    split_ifs
    · congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      dsimp only
      rw [hl (hsub ht hs), hhEq (hsub ht hs)]
    · exact hhEq ⟨le_rfl, huv⟩
  have hf (t : ℝ) (ht : t ∈ Icc u v) :
      Recon.ratio lam hh u t = Recon.ratio lam' hh' u t := by
    simp only [Recon.ratio, hhEq ht, hp t ht]
  have hQ (t : ℝ) (ht : t ∈ Icc u v) :
      Recon.Q e lam hh u t = Recon.Q e lam' hh' u t := by
    simp only [Recon.Q]
    congr 2
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' := hsub ht hs
    dsimp only
    rw [hr s hs', hl hs', hp s hs', hhEq hs']
  have hm (t : ℝ) (ht : t ∈ Icc u v) :
      Recon.m e lam hh u t = Recon.m e lam' hh' u t := by
    simp only [Recon.m]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' := hsub ht hs
    dsimp only
    rw [hl hs', hf s hs', hQ s hs', hr s hs']
    congr 3
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (show s ≤ t by
      rw [uIcc_of_le ht.1] at hs
      exact hs.2)] at hx
    have hx' : x ∈ Icc u v := ⟨hs'.1.trans hx.1, hx.2.trans ht.2⟩
    dsimp only
    rw [hl hx', hf x hx', hr x hx']
  have hmu (t : ℝ) (ht : t ∈ Icc u v) :
      Recon.mu e lam hh u t = Recon.mu e lam' hh' u t := by
    simp only [Recon.mu, hm t ht, hr t ht]
  have hz (t : ℝ) (ht : t ∈ Icc u v) :
      Recon.z e lam hh u t = Recon.z e lam' hh' u t := by
    simp only [Recon.z, hmu t ht, hQ t ht, hr t ht]
  have hn (t : ℝ) (ht : t ∈ Icc u v) :
      Recon.nu e lam hh u t = Recon.nu e lam' hh' u t := by
    simp only [Recon.nu, hl ⟨le_rfl, huv⟩]
    congr 2
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' := hsub ht hs
    dsimp only
    rw [hl hs', hr s hs', hz s hs']
  have hA : Recon.A e lam hh u v = Recon.A e lam' hh' u v := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' := hsub (show v ∈ Icc u v from ⟨huv, le_rfl⟩) hs
    dsimp only
    rw [hn s hs', hl hs', hQ s hs', hmu s hs', hr s hs']
  have hv : v ∈ Icc u v := ⟨huv, le_rfl⟩
  exact ⟨hr v hv, hp v hv, hf v hv, hQ v hv, hm v hv, hmu v hv, hz v hv, hn v hv, hA⟩

end EmcsfAcExtension.Local
