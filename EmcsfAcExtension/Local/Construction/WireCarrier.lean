module

public import EmcsfAcExtension.Local.Construction.ContinuationInputs
public import EmcsfAcExtension.Local.Construction.PicardBall

/-! # Identifying the two outgoing-jet carriers

Restriction and clamped extension identify the representation-independent
continuation pairs with the concrete complete Picard carrier on the wedge.
The comparison includes all four components, including collapsed sections.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

variable {c a L : ℝ}

/-- Restrict a compatible continuation pair to the compact Picard domain.
No values or outgoing jets outside that domain enter the carrier. -/
@[expose] noncomputable def ContinuationPair.toPicardCarrier (Z : ContinuationPair c a L) :
    PicardCarrier c a L (ℝ × ℂ) := by
  let F : C(PicardDomain c a L, ℝ × ℂ) :=
    ⟨fun p => (Z.lam p.1.1 p.1.2, Z.hh p.1.1 p.1.2),
      (continuousOn_iff_continuous_domRestrict.mp Z.continuous_lam).prodMk
        (continuousOn_iff_continuous_domRestrict.mp Z.continuous_hh)⟩
  let J : C(PicardDomain c a L, ℝ × ℂ) :=
    ⟨fun p => (Z.lamV p.1.1 p.1.2, Z.hhV p.1.1 p.1.2),
      (continuousOn_iff_continuous_domRestrict.mp Z.continuous_lamV).prodMk
        (continuousOn_iff_continuous_domRestrict.mp Z.continuous_hhV)⟩
  refine ⟨(F, J), ?_⟩
  intro p
  have hi : IntervalIntegrable (fun s => J (picardSectionPoint p s)) volume p.1.1 p.1.2 :=
    (J.continuous.comp (continuous_picardSectionPoint p)).intervalIntegrable _ _
  have hproj (s : ℝ) (hs : s ∈ uIcc p.1.1 p.1.2) :
      (picardSectionPoint p s).1 = (p.1.1, s) := by
    rw [uIcc_of_le p.2.1.2.1] at hs
    exact picardSectionPoint_of_mem p ⟨hs.1, hs.2.trans p.2.1.2.2⟩
  apply Prod.ext
  · have he := (ContinuousLinearMap.fst ℝ ℝ ℂ).intervalIntegral_comp_comm hi
    change (∫ s in p.1.1..p.1.2, (J (picardSectionPoint p s)).1) =
      (∫ s in p.1.1..p.1.2, J (picardSectionPoint p s)).1 at he
    change (F p).1 = (F (picardSectionPoint p p.1.1)).1 +
      (∫ s in p.1.1..p.1.2, J (picardSectionPoint p s)).1
    rw [← he]
    have heq := intervalIntegral.integral_congr (μ := volume) (fun s hs =>
      congrArg (fun q : ℝ × ℝ => Z.lamV q.1 q.2) (hproj s hs))
    change Z.lam p.1.1 p.1.2 = Z.lam (picardSectionPoint p p.1.1).1.1
      (picardSectionPoint p p.1.1).1.2 + _
    rw [picardSectionPoint_of_mem p ⟨le_rfl, p.2.1.2.1.trans p.2.1.2.2⟩]
    exact (Z.integral_lam p.1 p.2).trans (congrArg (_ + ·) heq.symm)
  · have he := (ContinuousLinearMap.snd ℝ ℝ ℂ).intervalIntegral_comp_comm hi
    change (∫ s in p.1.1..p.1.2, (J (picardSectionPoint p s)).2) =
      (∫ s in p.1.1..p.1.2, J (picardSectionPoint p s)).2 at he
    change (F p).2 = (F (picardSectionPoint p p.1.1)).2 +
      (∫ s in p.1.1..p.1.2, J (picardSectionPoint p s)).2
    rw [← he]
    have heq := intervalIntegral.integral_congr (μ := volume) (fun s hs =>
      congrArg (fun q : ℝ × ℝ => Z.hhV q.1 q.2) (hproj s hs))
    change Z.hh p.1.1 p.1.2 = Z.hh (picardSectionPoint p p.1.1).1.1
      (picardSectionPoint p p.1.1).1.2 + _
    rw [picardSectionPoint_of_mem p ⟨le_rfl, p.2.1.2.1.trans p.2.1.2.2⟩]
    exact (Z.integral_hh p.1 p.2).trans (congrArg (_ + ·) heq.symm)

/-- Extend a concrete carrier by the explicit wedge clamp. This supplies
continuous total representatives without imposing ambient derivatives. -/
@[expose] noncomputable def picardCarrierContinuationPair (ha : 0 ≤ a) (haL : a ≤ L)
    (z : PicardCarrier c a L (ℝ × ℂ)) : ContinuationPair c a L where
  lam := picardCandidateLam ha haL z
  hh := picardCandidateH ha haL z
  lamV u v := (z.1.2 (picardClamp ha haL (u, v))).1
  hhV u v := (z.1.2 (picardClamp ha haL (u, v))).2
  continuous_lam := (continuous_picardCandidateLam ha haL z).continuousOn
  continuous_hh := (continuous_picardCandidateH ha haL z).continuousOn
  continuous_lamV := (z.1.2.continuous.comp (continuous_picardClamp ha haL)).fst.continuousOn
  continuous_hhV := (z.1.2.continuous.comp (continuous_picardClamp ha haL)).snd.continuousOn
  integral_lam := by
    intro p hp
    let q : PicardDomain c a L := ⟨p, hp⟩
    have hi : IntervalIntegrable (fun s => z.1.2 (picardSectionPoint q s)) volume p.1 p.2 :=
      (z.1.2.continuous.comp (continuous_picardSectionPoint q)).intervalIntegrable _ _
    have he := (ContinuousLinearMap.fst ℝ ℝ ℂ).intervalIntegral_comp_comm hi
    change (∫ s in p.1..p.2, (z.1.2 (picardSectionPoint q s)).1) =
      (∫ s in p.1..p.2, z.1.2 (picardSectionPoint q s)).1 at he
    have h := congrArg Prod.fst (z.2 q)
    change (z.1.1 q).1 = (z.1.1 (picardSectionPoint q p.1)).1 + _ at h
    rw [← he] at h
    have haxis := picardCandidateLam_coe ha haL z (picardSectionPoint q p.1)
    rw [picardSectionPoint_of_mem q ⟨le_rfl, q.2.1.2.1.trans q.2.1.2.2⟩] at haxis
    rw [picardCandidateLam_coe ha haL z q, haxis]
    have hclamp (s : ℝ) : picardClamp ha haL (p.1, s) = picardSectionPoint q s :=
      picardClamp_sectionPoint ha haL q s
    simpa only [hclamp] using h
  integral_hh := by
    intro p hp
    let q : PicardDomain c a L := ⟨p, hp⟩
    have hi : IntervalIntegrable (fun s => z.1.2 (picardSectionPoint q s)) volume p.1 p.2 :=
      (z.1.2.continuous.comp (continuous_picardSectionPoint q)).intervalIntegrable _ _
    have he := (ContinuousLinearMap.snd ℝ ℝ ℂ).intervalIntegral_comp_comm hi
    change (∫ s in p.1..p.2, (z.1.2 (picardSectionPoint q s)).2) =
      (∫ s in p.1..p.2, z.1.2 (picardSectionPoint q s)).2 at he
    have h := congrArg Prod.snd (z.2 q)
    change (z.1.1 q).2 = (z.1.1 (picardSectionPoint q p.1)).2 + _ at h
    rw [← he] at h
    have haxis := picardCandidateH_coe ha haL z (picardSectionPoint q p.1)
    rw [picardSectionPoint_of_mem q ⟨le_rfl, q.2.1.2.1.trans q.2.1.2.2⟩] at haxis
    rw [picardCandidateH_coe ha haL z q, haxis]
    have hclamp (s : ℝ) : picardClamp ha haL (p.1, s) = picardSectionPoint q s :=
      picardClamp_sectionPoint ha haL q s
    simpa only [hclamp] using h

/-- Evaluation of the extended carrier recovers all four stored components
at every wedge point, including the axis and the terminal vertex. -/
theorem picardCarrierContinuationPair_coe (ha : 0 ≤ a) (haL : a ≤ L)
    (z : PicardCarrier c a L (ℝ × ℂ)) (p : PicardDomain c a L) :
    let Z := picardCarrierContinuationPair ha haL z
    Z.lam p.1.1 p.1.2 = (z.1.1 p).1 ∧ Z.hh p.1.1 p.1.2 = (z.1.1 p).2 ∧
    Z.lamV p.1.1 p.1.2 = (z.1.2 p).1 ∧ Z.hhV p.1.1 p.1.2 = (z.1.2 p).2 := by
  exact ⟨picardCandidateLam_coe ha haL z p, picardCandidateH_coe ha haL z p,
    by change (z.1.2 (picardClamp ha haL p.1)).1 = _; rw [picardClamp_coe],
    by change (z.1.2 (picardClamp ha haL p.1)).2 = _; rw [picardClamp_coe]⟩

/-- The carrier metric is exactly the pointwise maximum of the four
component distances. The evaluation constant one is universal. -/
theorem picardCarrierContinuationPair_dist_le_iff (ha : 0 ≤ a) (haL : a ≤ L)
    (z w : PicardCarrier c a L (ℝ × ℂ)) (r : ℝ) (hr : 0 ≤ r) :
    dist z w ≤ r ↔ ∀ p ∈ continuationWedge c a L,
      let Z := picardCarrierContinuationPair ha haL z
      let W := picardCarrierContinuationPair ha haL w
      max (max |Z.lam p.1 p.2 - W.lam p.1 p.2| ‖Z.hh p.1 p.2 - W.hh p.1 p.2‖)
        (max |Z.lamV p.1 p.2 - W.lamV p.1 p.2| ‖Z.hhV p.1 p.2 - W.hhV p.1 p.2‖) ≤ r := by
  change max (dist z.1.1 w.1.1) (dist z.1.2 w.1.2) ≤ r ↔ _
  rw [max_le_iff, ContinuousMap.dist_le hr, ContinuousMap.dist_le hr]
  constructor
  · rintro ⟨hv, hj⟩ p hp
    let q : PicardDomain c a L := ⟨p, hp⟩
    obtain ⟨zl, zh, zj, zk⟩ := picardCarrierContinuationPair_coe ha haL z q
    obtain ⟨wl, wh, wj, wk⟩ := picardCarrierContinuationPair_coe ha haL w q
    dsimp only
    rw [zl, zh, zj, zk, wl, wh, wj, wk]
    simpa only [Prod.dist_eq, Real.dist_eq, dist_eq_norm, Prod.norm_def, Prod.fst_sub,
      Prod.snd_sub, Real.norm_eq_abs] using max_le (hv q) (hj q)
  · intro h
    have hpoint (q : PicardDomain c a L) :
        max (max |(z.1.1 q).1 - (w.1.1 q).1| ‖(z.1.1 q).2 - (w.1.1 q).2‖)
          (max |(z.1.2 q).1 - (w.1.2 q).1| ‖(z.1.2 q).2 - (w.1.2 q).2‖) ≤ r := by
      have hp := h q.1 q.2
      obtain ⟨zl, zh, zj, zk⟩ := picardCarrierContinuationPair_coe ha haL z q
      obtain ⟨wl, wh, wj, wk⟩ := picardCarrierContinuationPair_coe ha haL w q
      dsimp only at hp
      rwa [zl, zh, zj, zk, wl, wh, wj, wk] at hp
    exact ⟨fun q => by simpa only [Prod.dist_eq, Real.dist_eq, dist_eq_norm, Prod.norm_def,
        Prod.fst_sub,
      Prod.snd_sub, Real.norm_eq_abs]
      using (max_le_iff.mp (hpoint q)).1,
      fun q => by simpa only [Prod.dist_eq, Real.dist_eq, dist_eq_norm, Prod.norm_def, Prod.fst_sub,
      Prod.snd_sub, Real.norm_eq_abs]
        using (max_le_iff.mp (hpoint q)).2⟩

end EmcsfAcExtension.Local
