module

public import EmcsfAcExtension.Local.Construction.ContinuationInputs
import EmcsfAcExtension.Local.Construction.WireRecon
import EmcsfAcExtension.Local.Construction.PicardCoefficientContinuity
import EmcsfAcExtension.Local.Construction.FullSystemCarrier

/-! # Discharging C¹ system recovery

The compatible pair supplies the raw carrier facts. Coefficient continuity
comes from the literal Picard reconstructions; internal project record then recovers the
full C¹ solution on the original closed wedge.
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- Discharge the continuation recovery input from the complete outgoing-jet
carrier and internal project record's `smooth_full_system`. The fixed positive expansion
and gap margins precede the pair. No higher regularity or new constant enters. -/
theorem continuation_recovery_input : ContinuationRecoveryInput := by
  intro c a L e ℓ κ lam₀ h₀ Z ha haL hℓ hκ cl₀ ch₀ hb hfixed
  let z := Z.toPicardCarrier
  let lam := picardCandidateLam ha.le haL z
  let hh := picardCandidateH ha.le haL z
  have heq (p : ℝ × ℝ) (hp : p ∈ continuationWedge c a L) :
      lam p.1 p.2 = Z.lam p.1 p.2 ∧ hh p.1 p.2 = Z.hh p.1 p.2 := by
    exact ⟨picardCandidateLam_coe ha.le haL z ⟨p, hp⟩,
      picardCandidateH_coe ha.le haL z ⟨p, hp⟩⟩
  have hrad (p : ℝ × ℝ) (hp : p ∈ continuationWedge c a L) :=
    recon_eq_of_pair_eqOn (e := e) hp.1.2.1
      (fun v hv => (heq (p.1, v)
        ⟨⟨hp.1.1, hv.1, hv.2.trans hp.1.2.2⟩, hp.2⟩).1)
      (fun v hv => (heq (p.1, v)
        ⟨⟨hp.1.1, hv.1, hv.2.trans hp.1.2.2⟩, hp.2⟩).2)
  have hl : ∀ q : PicardDomain c a L, ℓ ≤ (z.1.1 q).1 :=
    fun q => (hb q.1 q.2).1
  have hg : ∀ q : PicardDomain c a L, κ ≤ 1 - picardMuValues e ℓ hℓ z hl q := by
    intro q
    rw [picardMuValues_eq_recon ha.le haL]
    change κ ≤ 1 - Recon.mu e lam hh q.1.1 q.1.2
    rw [(hrad q.1 q.2).2.2.2.2.2.1]
    exact (hb q.1 q.2).2
  obtain ⟨cG, cA, cP⟩ := picard_coefficients_continuousOn ha.le haL e ℓ κ hℓ hκ z hl hg
  have cG' : ContinuousOn (fun p : ℝ × ℝ =>
      Recon.nu e Z.lam Z.hh p.1 p.2 / Recon.r Z.lam p.1 p.2 *
        Recon.z e Z.lam Z.hh p.1 p.2) (continuationWedge c a L) := by
    apply cG.congr
    intro p hp
    symm
    obtain ⟨hr, _, _, _, _, _, hz, hn, _⟩ := hrad p hp
    dsimp only
    change Recon.nu e lam hh p.1 p.2 / Recon.r lam p.1 p.2 * Recon.z e lam hh p.1 p.2 = _
    rw [hr, hz, hn]
  have cA' : ContinuousOn (Function.uncurry (Recon.A e Z.lam Z.hh))
      (continuationWedge c a L) := by
    apply cA.congr
    intro p hp
    exact (hrad p hp).2.2.2.2.2.2.2.2.symm
  have cP' : ContinuousOn (fun p : ℝ × ℝ =>
      ((-Recon.nu e Z.lam Z.hh p.1 p.2 / Recon.r Z.lam p.1 p.2 : ℝ) : ℂ) *
        ((Recon.z e Z.lam Z.hh p.1 p.2 : ℂ) * Recon.ratio Z.lam Z.hh p.1 p.2 +
          Complex.I * e * Recon.Q e Z.lam Z.hh p.1 p.2 * Recon.phi Z.lam Z.hh p.1 p.2 /
            (1 - (Recon.mu e Z.lam Z.hh p.1 p.2 : ℂ)))) (continuationWedge c a L) := by
    apply cP.congr
    intro p hp
    symm
    obtain ⟨hr, hp', hf, hQ, _, hmu, hz, hn, _⟩ := hrad p hp
    dsimp only
    change ((-Recon.nu e lam hh p.1 p.2 / Recon.r lam p.1 p.2 : ℝ) : ℂ) *
      ((Recon.z e lam hh p.1 p.2 : ℂ) * Recon.ratio lam hh p.1 p.2 +
        Complex.I * e * Recon.Q e lam hh p.1 p.2 * Recon.phi lam hh p.1 p.2 /
          (1 - (Recon.mu e lam hh p.1 p.2 : ℂ))) = _
    rw [hr, hp', hf, hQ, hmu, hz, hn]
  exact (Null.smooth_full_system (by linarith only [ha]) (by linarith only [haL])
    hℓ hκ cl₀ ch₀ Z.continuous_lam Z.continuous_hh Z.continuous_lamV Z.continuous_hhV
    Z.integral_lam Z.integral_hh cG' cA' cP'
    (fun p hp => (hfixed p hp).1) (fun p hp => (hfixed p hp).2)
    (fun p hp => (hb p hp).1) (fun p hp => (hb p hp).2)).1

end EmcsfAcExtension.Local
