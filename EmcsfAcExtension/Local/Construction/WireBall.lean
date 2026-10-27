module

public import EmcsfAcExtension.Local.Construction.WireCarrier

/-! # Realizing the full canonical continuation ball

The complete affine Picard ball represents every compatible continuation
pair in the prescribed four-component ball, with its exact inherited metric.
-/

public section

open Set

namespace EmcsfAcExtension.Local

variable {c a L : ℝ}

/-- For a center with the literal data values and jets, the metric ball
condition is exactly the four component inequalities of `InConeBall`.
The radius and the evaluation constant are unchanged. -/
theorem picardCarrierContinuationPair_inConeBall_iff (ha : 0 ≤ a) (haL : a ≤ L)
    (lam₀ : ℝ → ℝ) (h₀ : ℝ → ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (center z : PicardCarrier c a L (ℝ × ℂ))
    (hc : ∀ p : PicardDomain c a L,
      center.1.1 p = (lam₀ p.1.2, h₀ p.1.2))
    (hj : ∀ p : PicardDomain c a L, center.1.2 p =
      (derivWithin lam₀ (Icc c (c + L)) p.1.2,
        derivWithin h₀ (Icc c (c + L)) p.1.2)) :
    (picardCarrierContinuationPair ha haL z).InConeBall lam₀ h₀ ρ ↔ dist z center ≤ ρ := by
  rw [picardCarrierContinuationPair_dist_le_iff ha haL z center ρ hρ]
  have hcenter (p : ℝ × ℝ) (hp : p ∈ continuationWedge c a L) :=
    picardCarrierContinuationPair_coe ha haL center ⟨p, hp⟩
  simp only [hc, hj] at hcenter
  simp only [ContinuationPair.InConeBall]
  constructor <;> intro h p hp
  · obtain ⟨hl, hh, hlv, hhv⟩ := h p hp
    obtain ⟨cl, ch, cj, ck⟩ := hcenter p hp
    rw [cl, ch, cj, ck]
    exact max_le (max_le hl hh) (max_le hlv hhv)
  · have hb := h p hp
    obtain ⟨cl, ch, cj, ck⟩ := hcenter p hp
    rw [cl, ch, cj, ck] at hb
    exact ⟨(max_le_iff.mp (max_le_iff.mp hb).1).1,
      (max_le_iff.mp (max_le_iff.mp hb).1).2,
      (max_le_iff.mp (max_le_iff.mp hb).2).1,
      (max_le_iff.mp (max_le_iff.mp hb).2).2⟩

/-- Build the continuation interface from the entire complete canonical
Picard ball and an exact self-map. Its coefficient is the displayed `C`;
the Lipschitz estimate retains the literal width factor `a`. Every compatible
pair in the canonical affine ball is represented, with no invariant subset
substituted for that ball. All quantitative premises are explicit. -/
@[expose] noncomputable def continuationPicardBall_of_update
    (ha : 0 ≤ a) (haL : a ≤ L) (e ρ ℓ κ C : ℝ)
    (lam₀ : ℝ → ℝ) (h₀ : ℝ → ℂ)
    (center : PicardCarrier c a L (ℝ × ℂ)) (hρ : 0 ≤ ρ)
    (hc : ∀ p : PicardDomain c a L, center.1.1 p = (lam₀ p.1.2, h₀ p.1.2))
    (hj : ∀ p : PicardDomain c a L, center.1.2 p =
      (derivWithin lam₀ (Icc c (c + L)) p.1.2,
        derivWithin h₀ (Icc c (c + L)) p.1.2))
    (F : PicardBall (fun v => (lam₀ v, h₀ v)) center ρ →
      PicardBall (fun v => (lam₀ v, h₀ v)) center ρ)
    (hF : ∀ z p, (F z).1.1.1 p =
      (Recon.picardLam e (picardCandidateLam ha haL z.1)
        (picardCandidateH ha haL z.1) c lam₀ p.1.1 p.1.2,
       Recon.picardH e (picardCandidateLam ha haL z.1)
        (picardCandidateH ha haL z.1) c h₀ p.1.1 p.1.2))
    (hC : 0 < C) (haC : a * C < 1)
    (hlip : ∀ z w, dist (F z) (F w) ≤ (a * C) * dist z w)
    (hb : ∀ (z : PicardBall (fun v => (lam₀ v, h₀ v)) center ρ) p,
      ℓ ≤ (z.1.1.1 p).1 ∧ κ ≤ 1 - Recon.mu e
        (picardCandidateLam ha haL z.1) (picardCandidateH ha haL z.1) p.1.1 p.1.2) :
    ContinuationPicardBall e c a L lam₀ h₀ ρ ℓ κ where
  Carrier := PicardBall (fun v => (lam₀ v, h₀ v)) center ρ
  metric := inferInstance
  complete := inferInstance
  nonempty := picardBall_nonempty
    ((mem_picardInitialSet_iff _ _).mpr (fun p _ => hc p)) hρ
  state z := picardCarrierContinuationPair ha haL z.1
  state_ball z := (picardCarrierContinuationPair_inConeBall_iff
    ha haL lam₀ h₀ ρ hρ center z.1 hc hj).mpr
      ((mem_picardBallSet_iff _ _ _ _).mp z.2).2
  state_initial := by
    intro z v hv
    let p : PicardDomain c a L :=
      ⟨(c, v), ⟨⟨le_rfl, hv⟩, by change c ≤ c + a; exact le_add_of_nonneg_right ha⟩⟩
    have hz := (mem_picardInitialSet_iff _ _).mp
      ((mem_picardBallSet_iff _ _ _ _).mp z.2).1 p rfl
    obtain ⟨hl, hh, _, _⟩ := picardCarrierContinuationPair_coe ha haL z.1 p
    exact ⟨hl.trans (congrArg Prod.fst hz), hh.trans (congrArg Prod.snd hz)⟩
  represents := by
    intro Z hball hinit
    let z := Z.toPicardCarrier
    have hstate : (picardCarrierContinuationPair ha haL z).InConeBall lam₀ h₀ ρ := by
      intro p hp
      obtain ⟨hl, hh, hjl, hjh⟩ := picardCarrierContinuationPair_coe ha haL z ⟨p, hp⟩
      change (picardCarrierContinuationPair ha haL z).lam p.1 p.2 = Z.lam p.1 p.2 at hl
      change (picardCarrierContinuationPair ha haL z).hh p.1 p.2 = Z.hh p.1 p.2 at hh
      change (picardCarrierContinuationPair ha haL z).lamV p.1 p.2 = Z.lamV p.1 p.2 at hjl
      change (picardCarrierContinuationPair ha haL z).hhV p.1 p.2 = Z.hhV p.1 p.2 at hjh
      rw [hl, hh, hjl, hjh]
      exact hball p hp
    have hdist := (picardCarrierContinuationPair_inConeBall_iff
      ha haL lam₀ h₀ ρ hρ center z hc hj).mp hstate
    have hinitial : z ∈ picardInitialSet (fun v => (lam₀ v, h₀ v)) := by
      apply (mem_picardInitialSet_iff _ _).mpr
      intro p hp
      have hv : p.1.2 ∈ Icc c (c + L) := ⟨p.2.1.1.trans p.2.1.2.1, p.2.1.2.2⟩
      change (Z.lam p.1.1 p.1.2, Z.hh p.1.1 p.1.2) = _
      rw [hp, (hinit p.1.2 hv).1, (hinit p.1.2 hv).2]
    refine ⟨⟨z, (mem_picardBallSet_iff _ _ _ _).mpr ⟨hinitial, hdist⟩⟩, ?_⟩
    intro p hp
    exact picardCarrierContinuationPair_coe ha haL z ⟨p, hp⟩
  distance_le_iff z w r hr := picardCarrierContinuationPair_dist_le_iff ha haL z.1 w.1 r hr
  update := F
  update_exact := by
    intro z p hp
    let q : PicardDomain c a L := ⟨p, hp⟩
    have he := hF z q
    obtain ⟨hl, hh, _, _⟩ := picardCarrierContinuationPair_coe ha haL (F z).1 q
    exact ⟨(congrArg Prod.fst he).symm.trans hl.symm,
      (congrArg Prod.snd he).symm.trans hh.symm⟩
  coefficient := C
  coefficient_pos := hC
  coefficient_small := haC
  update_lipschitz := hlip
  state_bounds := by
    intro z p hp
    obtain ⟨hl, _, _, _⟩ := picardCarrierContinuationPair_coe ha haL z.1 ⟨p, hp⟩
    exact ⟨by rw [hl]; exact (hb z ⟨p, hp⟩).1, (hb z ⟨p, hp⟩).2⟩

end EmcsfAcExtension.Local
