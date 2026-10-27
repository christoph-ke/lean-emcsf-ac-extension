module

public import EmcsfAcExtension.Local.Construction.ContinuationInputs
import EmcsfAcExtension.Local.Construction.WireBall
import EmcsfAcExtension.Local.Construction.WireUniform
import EmcsfAcExtension.Local.Construction.PicardShortConeContraction

/-! # Discharging the uniform short-cone input

E5's exact fixed point is transferred to compatible continuation pairs.
The minimum of the two signed times fixes one time before signed coupling,
cone position, cone length and C¹ data.
-/

public section

open Set

namespace EmcsfAcExtension.Local

private theorem wire_short_picard_signed (B ℓ e : ℝ) (hB : 1 ≤ B) (hℓ : 0 < ℓ) :
    ∃ τ : ℝ, 0 < τ ∧
      ∀ (c L : ℝ) (lam₀ : ℝ → ℝ) (h₀ : ℝ → ℂ), 0 < L → L ≤ τ →
      ContDiffOn ℝ 1 lam₀ (Icc c (c + L)) →
      ContDiffOn ℝ 1 h₀ (Icc c (c + L)) →
      (∀ v ∈ Icc c (c + L), ℓ ≤ lam₀ v ∧ |lam₀ v| ≤ B ∧ ‖h₀ v‖ ≤ B ∧
        |derivWithin lam₀ (Icc c (c + L)) v| ≤ B ∧
        ‖derivWithin h₀ (Icc c (c + L)) v‖ ≤ B) →
      ∃ Z : ContinuationPair c L L,
        Z.IsFixedPoint e lam₀ h₀ ∧ Z.InConeBall lam₀ h₀ (min (1 / 128) (ℓ / 4)) ∧
        ∀ p ∈ continuationWedge c L L,
          ℓ / 2 ≤ Z.lam p.1 p.2 ∧ 3 / 4 ≤ 1 - Recon.mu e Z.lam Z.hh p.1 p.2 := by
  obtain ⟨ρ, hρ, hρsmall, hρell, τ, hτ, _, hmain⟩ :=
    picardShortCone_contraction B ℓ e hB hℓ
  refine ⟨τ, hτ, ?_⟩
  intro c L lam₀ h₀ hL hLτ cl ch hb
  let datum : ℝ → ℝ × ℂ := fun v => (lam₀ v, h₀ v)
  have hc : ContDiffOn ℝ 1 datum (Icc c (c + L)) := cl.prodMk ch
  have hjet (v : ℝ) (hv : v ∈ Icc c (c + L)) :
      derivWithin datum (Icc c (c + L)) v =
        (derivWithin lam₀ (Icc c (c + L)) v, derivWithin h₀ (Icc c (c + L)) v) := by
    exact (((cl.differentiableOn (by norm_num)) v hv).hasDerivWithinAt.prodMk
      ((ch.differentiableOn (by norm_num)) v hv).hasDerivWithinAt).derivWithin
        (uniqueDiffOn_Icc (by linarith only [hL]) v hv)
  have hd (v : ℝ) (hv : v ∈ Icc c (c + L)) :
      ‖datum v‖ ≤ B ∧ ‖derivWithin datum (Icc c (c + L)) v‖ ≤ B := by
    obtain ⟨_, hl, hh, hjl, hjh⟩ := hb v hv
    rw [hjet v hv]
    simpa only [datum, Prod.norm_def, Real.norm_eq_abs, max_le_iff] using
      (show (‖lam₀ v‖ ≤ B ∧ ‖h₀ v‖ ≤ B) ∧
        ‖derivWithin lam₀ (Icc c (c + L)) v‖ ≤ B ∧
          ‖derivWithin h₀ (Icc c (c + L)) v‖ ≤ B from
        ⟨⟨by simpa only [Real.norm_eq_abs] using hl, hh⟩,
          by simpa only [Real.norm_eq_abs] using hjl, hjh⟩)
  let center := picardConeCenterOfContDiff (a := L) datum hL hc
  obtain ⟨F, hF, _, ⟨x, hx, _⟩, hbounds⟩ :=
    hmain c L hL hLτ datum hc hd (fun v hv => (hb v hv).1)
  let Z := picardCarrierContinuationPair hL.le le_rfl x.1
  have hZ : Z.IsFixedPoint e lam₀ h₀ := by
    intro p hp
    let q : PicardDomain c L L := ⟨p, hp⟩
    have h := hF x q
    rw [hx] at h
    obtain ⟨hl, hh, _, _⟩ := picardCarrierContinuationPair_coe hL.le le_rfl x.1 q
    exact ⟨(congrArg Prod.fst h).symm.trans hl.symm,
      (congrArg Prod.snd h).symm.trans hh.symm⟩
  have hj (p : PicardDomain c L L) : center.1.2 p =
      (derivWithin lam₀ (Icc c (c + L)) p.1.2,
        derivWithin h₀ (Icc c (c + L)) p.1.2) :=
    hjet p.1.2 ⟨p.2.1.1.trans p.2.1.2.1, p.2.1.2.2⟩
  have hball : Z.InConeBall lam₀ h₀ ρ :=
    (picardCarrierContinuationPair_inConeBall_iff hL.le le_rfl lam₀ h₀ ρ hρ.le
      center x.1 (fun _ => rfl) hj).mpr ((mem_picardBallSet_iff _ _ _ _).mp x.2).2
  refine ⟨Z, hZ, ?_, ?_⟩
  · intro p hp
    obtain ⟨hl, hh, hjl, hjh⟩ := hball p hp
    have hm : ρ ≤ min (1 / 128) (ℓ / 4) := le_min hρsmall hρell
    exact ⟨hl.trans hm, hh.trans hm, hjl.trans hm, hjh.trans hm⟩
  · intro p hp
    obtain ⟨hl, _, _, _⟩ := picardCarrierContinuationPair_coe hL.le le_rfl x.1 ⟨p, hp⟩
    exact ⟨by rw [hl]; exact (hbounds x ⟨p, hp⟩).1, (hbounds x ⟨p, hp⟩).2⟩

/-- Discharge E5's continuation input. The common time depends only on
`B,ℓ,E`, before both signs of the coupling, cone position, length and data.
Only the displayed first derivatives enter the class; all radius and margin
constants are the numerical ones in the continuation contract. -/
theorem continuation_short_picard_input : ContinuationShortPicardInput := by
  intro B ℓ E hB hℓ _hE
  obtain ⟨τp, hτp, hp⟩ := wire_short_picard_signed B ℓ E hB hℓ
  obtain ⟨τm, hτm, hm⟩ := wire_short_picard_signed B ℓ (-E) hB hℓ
  refine ⟨min τp τm, lt_min hτp hτm, ?_⟩
  intro e he
  rcases wire_coupling_cases he with rfl | rfl
  · intro c L lam₀ h₀ hL hLτ cl ch hb
    exact hp c L lam₀ h₀ hL (hLτ.trans (min_le_left _ _)) cl ch hb
  · intro c L lam₀ h₀ hL hLτ cl ch hb
    exact hm c L lam₀ h₀ hL (hLτ.trans (min_le_right _ _)) cl ch hb

end EmcsfAcExtension.Local
