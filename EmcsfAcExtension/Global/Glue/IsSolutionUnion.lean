/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Frozen.IsSolution
public import EmcsfAcExtension.Frozen.Fields.EqOn
public import EmcsfAcExtension.Global.Glue.AxisSeam
import EmcsfAcExtension.Local.Api.EqOn
import EmcsfAcExtension.Local.Api.Mono
import EmcsfAcExtension.Infra.Null.IntegralForm
import EmcsfAcExtension.Infra.AC.Intervals

/-! # The frozen solution class on a characteristic union

The closed pieces must have a characteristic segment cover: outgoing segments
stay in one piece, and incoming segments stay in one piece or split into two
closed subsegments with a common endpoint. Closedness alone is insufficient.
The final construction discharges these geometric hypotheses on precisely
`origDomain ui ∪ triangle us vp`, as in internal project record's continuation argument.
-/

public section

namespace EmcsfAcExtension.Global

open Set MeasureTheory Filter Topology
open scoped ENNReal

private theorem integralForm_congr_on {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f g f' g' : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (h : IntegralForm f g a b) (hf : Set.EqOn f f' (Icc a b))
    (hg : Set.EqOn g g' (Icc a b)) : IntegralForm f' g' a b := by
  have hg' : Set.EqOn g g' (uIcc a b) := by rwa [uIcc_of_le hab]
  refine ⟨h.1.congr (hg'.mono uIoc_subset_uIcc), ?_⟩
  rw [← hf (left_mem_Icc.mpr hab), ← hf (right_mem_Icc.mpr hab), h.2]
  exact intervalIntegral.integral_congr hg'

private theorem ac_congr_on {E : Type*} [PseudoMetricSpace E]
    {f g : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (h : AbsolutelyContinuousOnInterval f a b) (he : Set.EqOn f g (Icc a b)) :
    AbsolutelyContinuousOnInterval g a b :=
  h.congr (by rwa [uIcc_of_le hab])

private theorem variation_le_congr {E : Type*} [PseudoEMetricSpace E]
    {f g : ℝ → E} {s : Set ℝ} {B : ℝ≥0∞}
    (h : eVariationOn f s ≤ B) (he : Set.EqOn f g s) : eVariationOn g s ≤ B := by
  rwa [← eVariationOn.eq_of_eqOn he]

private theorem rhs_eq {S T : Fields} {D : Set (ℝ × ℝ)}
    (he : S.EqOn T D) (e : ℝ) {u v : ℝ} (hp : (u, v) ∈ D) :
    S.rUV u v = T.rUV u v ∧ S.mV u v = T.mV u v ∧ S.mU u v = T.mU u v ∧
    S.QV e u v = T.QV e u v ∧ S.QU e u v = T.QU e u v ∧ S.AV u v = T.AV u v ∧
    S.phiV u v = T.phiV u v ∧ S.phiU e u v = T.phiU e u v ∧
    S.xiV e u v = T.xiV e u v ∧ S.thetaU e u v = T.thetaU e u v := by
  simp only [Fields.rUV, Fields.mV, Fields.mU, Fields.QV, Fields.QU, Fields.AV,
    Fields.phiV, Fields.phiU, Fields.xiV, Fields.thetaU, Fields.waveSource,
    he.r hp, he.lam hp, he.nu hp, he.Q hp, he.phi hp, he.A hp,
    he.theta hp, he.xi hp, he.mu hp, and_self]

/-- Pointwise agreement of all nine primary fields transports every frozen class
clause, including the rational right sides, normalized fields and axis moduli. -/
theorem isSolution_congr {e : ℝ} {S T : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (he : S.EqOn T D) : IsSolution e T D where
  subset := hS.subset
  r_pos := by
    intro p hp hu
    simpa only [he.r hp] using hS.r_pos p hp hu
  lam_pos := by
    intro p hp
    simpa only [he.lam hp] using hS.lam_pos p hp
  nu_neg := by
    intro p hp
    simpa only [he.nu hp] using hS.nu_neg p hp
  one_sub_mu_pos := by
    intro p hp
    simpa only [he.mu hp] using hS.one_sub_mu_pos p hp
  cont_r := hS.cont_r.congr (fun _ hp => (he.r hp).symm)
  cont_lam := hS.cont_lam.congr (fun _ hp => (he.lam hp).symm)
  cont_nu := hS.cont_nu.congr (fun _ hp => (he.nu hp).symm)
  cont_m := hS.cont_m.congr (fun _ hp => (he.m hp).symm)
  cont_Q := hS.cont_Q.congr (fun _ hp => (he.Q hp).symm)
  cont_phi := hS.cont_phi.congr (fun _ hp => (he.phi hp).symm)
  cont_A := hS.cont_A.congr (fun _ hp => (he.A hp).symm)
  cont_theta := hS.cont_theta.congr (fun _ hp => (he.theta hp).symm)
  cont_xi := hS.cont_xi.congr (fun _ hp => (he.xi hp).symm)
  eq_out := by
    intro u a b hua hab hs
    have hp : ∀ x ∈ Icc a b, (u, x) ∈ D := fun x hx => hs ⟨rfl, hx⟩
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hS.eq_out u a b hua hab hs
    exact ⟨integralForm_congr_on hab h1 (fun x hx => he.r (hp x hx))
        (fun x hx => he.lam (hp x hx)),
      integralForm_congr_on hab h2 (fun x hx => he.nu (hp x hx))
        (fun x hx => (rhs_eq he e (hp x hx)).1),
      integralForm_congr_on hab h3 (fun x hx => he.m (hp x hx))
        (fun x hx => (rhs_eq he e (hp x hx)).2.1),
      integralForm_congr_on hab h4 (fun x hx => he.Q (hp x hx))
        (fun x hx => (rhs_eq he e (hp x hx)).2.2.2.1),
      integralForm_congr_on hab h5 (fun x hx => he.A (hp x hx))
        (fun x hx => (rhs_eq he e (hp x hx)).2.2.2.2.2.1),
      integralForm_congr_on hab h6 (fun x hx => he.phi (hp x hx))
        (fun x hx => (rhs_eq he e (hp x hx)).2.2.2.2.2.2.1),
      integralForm_congr_on hab h7 (fun x hx => he.xi (hp x hx))
        (fun x hx => (rhs_eq he e (hp x hx)).2.2.2.2.2.2.2.2.1)⟩
  eq_in := by
    intro a b v hab hbv hs
    have hp : ∀ x ∈ Icc a b, (x, v) ∈ D := fun x hx => hs ⟨hx.1, hx.2, rfl⟩
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS.eq_in a b v hab hbv hs
    exact ⟨integralForm_congr_on hab h1 (fun x hx => he.r (hp x hx))
        (fun x hx => he.nu (hp x hx)),
      integralForm_congr_on hab h2 (fun x hx => he.lam (hp x hx))
        (fun x hx => (rhs_eq he e (hp x hx)).1),
      integralForm_congr_on hab h3 (fun x hx => he.m (hp x hx))
        (fun x hx => (rhs_eq he e (hp x hx)).2.2.1),
      integralForm_congr_on hab h4 (fun x hx => he.Q (hp x hx))
        (fun x hx => (rhs_eq he e (hp x hx)).2.2.2.2.1),
      integralForm_congr_on hab h5 (fun x hx => he.phi (hp x hx))
        (fun x hx => (rhs_eq he e (hp x hx)).2.2.2.2.2.2.2.1),
      integralForm_congr_on hab h6 (fun x hx => he.theta (hp x hx))
        (fun x hx => (rhs_eq he e (hp x hx)).2.2.2.2.2.2.2.2.2)⟩
  ac_out := by
    intro u a b hab hs
    have hp : ∀ x ∈ Icc a b, (u, x) ∈ D := fun x hx => hs ⟨rfl, hx⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := hS.ac_out u a b hab hs
    exact ⟨ac_congr_on hab h1 (fun x hx => he.r (hp x hx)),
      ac_congr_on hab h2 (fun x hx => he.m (hp x hx)),
      ac_congr_on hab h3 (fun x hx => he.Q (hp x hx)),
      ac_congr_on hab h4 (fun x hx => he.phi (hp x hx)),
      ac_congr_on hab h5 (fun x hx => he.a (hp x hx))⟩
  ac_in := by
    intro a b v hab hs
    have hp : ∀ x ∈ Icc a b, (x, v) ∈ D := fun x hx => hs ⟨hx.1, hx.2, rfl⟩
    obtain ⟨h1, h2, h3, h4⟩ := hS.ac_in a b v hab hs
    exact ⟨ac_congr_on hab h1 (fun x hx => he.r (hp x hx)),
      ac_congr_on hab h2 (fun x hx => he.m (hp x hx)),
      ac_congr_on hab h3 (fun x hx => he.Q (hp x hx)),
      ac_congr_on hab h4 (fun x hx => he.phi (hp x hx))⟩
  bv_loc := by
    intro K hKD hK
    obtain ⟨B, hB, ho, hi⟩ := hS.bv_loc K hKD hK
    refine ⟨B, hB, ?_, ?_⟩
    · intro u a b hs
      have hp : ∀ x ∈ Icc a b, (u, x) ∈ D := fun x hx => hKD (hs ⟨rfl, hx⟩)
      obtain ⟨h1, h2, h3, h4⟩ := ho u a b hs
      exact ⟨variation_le_congr h1 (fun x hx => he.lam (hp x hx)),
        variation_le_congr h2 (fun x hx => he.nu (hp x hx)),
        variation_le_congr h3 (fun x hx => he.a (hp x hx)),
        variation_le_congr h4 (fun x hx => he.b (hp x hx))⟩
    · intro a b v hs
      have hp : ∀ x ∈ Icc a b, (x, v) ∈ D := fun x hx => hKD (hs ⟨hx.1, hx.2, rfl⟩)
      obtain ⟨h1, h2, h3, h4⟩ := hi a b v hs
      exact ⟨variation_le_congr h1 (fun x hx => he.lam (hp x hx)),
        variation_le_congr h2 (fun x hx => he.nu (hp x hx)),
        variation_le_congr h3 (fun x hx => he.a (hp x hx)),
        variation_le_congr h4 (fun x hx => he.b (hp x hx))⟩
  axis_small_var := by
    intro t ht η hη
    obtain ⟨δ, hδ, ho, hi⟩ := hS.axis_small_var t ht η hη
    refine ⟨δ, hδ, ?_, ?_⟩
    · intro u a b hs
      exact variation_le_congr (ho u a b hs)
        (fun x hx => he.phi (hs (show (u, x) ∈ outSeg u a b from ⟨rfl, hx⟩)).1)
    · intro a b v hs
      exact variation_le_congr (hi a b v hs)
        (fun x hx => he.phi (hs ⟨hx.1, hx.2, rfl⟩).1)
  axis := by
    intro t ht
    simpa only [he.r ht, he.m ht, he.Q ht, he.lam ht, he.nu ht, he.a ht,
      he.b ht, he.phi ht] using hS.axis t ht
  axis_mu := by
    intro t ht
    apply (hS.axis_mu t ht).congr'
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact he.mu hp.1

/-- The frozen class glues on two closed pieces with the displayed characteristic
segment cover. The incoming alternative includes both endpoint representatives.
The compact BV bound is the sum of the two compact-piece bounds, with no constant
chosen independently of the data. -/
theorem isSolution_union_of_segment_cover {e : ℝ} {S : Fields}
    {D₁ D₂ : Set (ℝ × ℝ)} (h₁ : IsSolution e S D₁) (h₂ : IsSolution e S D₂)
    (hc₁ : IsClosed D₁) (hc₂ : IsClosed D₂)
    (hout : ∀ u a b, a ≤ b → outSeg u a b ⊆ D₁ ∪ D₂ →
      outSeg u a b ⊆ D₁ ∨ outSeg u a b ⊆ D₂)
    (hin : ∀ a b v, a ≤ b → inSeg a b v ⊆ D₁ ∪ D₂ →
      inSeg a b v ⊆ D₁ ∨ inSeg a b v ⊆ D₂ ∨
      ∃ c, a ≤ c ∧ c ≤ b ∧ inSeg a c v ⊆ D₁ ∧ inSeg c b v ⊆ D₂) :
    IsSolution e S (D₁ ∪ D₂) where
  subset := union_subset h₁.subset h₂.subset
  r_pos := fun p hp => hp.elim (h₁.r_pos p) (h₂.r_pos p)
  lam_pos := fun p hp => hp.elim (h₁.lam_pos p) (h₂.lam_pos p)
  nu_neg := fun p hp => hp.elim (h₁.nu_neg p) (h₂.nu_neg p)
  one_sub_mu_pos := fun p hp => hp.elim (h₁.one_sub_mu_pos p) (h₂.one_sub_mu_pos p)
  cont_r := h₁.cont_r.union_of_isClosed h₂.cont_r hc₁ hc₂
  cont_lam := h₁.cont_lam.union_of_isClosed h₂.cont_lam hc₁ hc₂
  cont_nu := h₁.cont_nu.union_of_isClosed h₂.cont_nu hc₁ hc₂
  cont_m := h₁.cont_m.union_of_isClosed h₂.cont_m hc₁ hc₂
  cont_Q := h₁.cont_Q.union_of_isClosed h₂.cont_Q hc₁ hc₂
  cont_phi := h₁.cont_phi.union_of_isClosed h₂.cont_phi hc₁ hc₂
  cont_A := h₁.cont_A.union_of_isClosed h₂.cont_A hc₁ hc₂
  cont_theta := h₁.cont_theta.union_of_isClosed h₂.cont_theta hc₁ hc₂
  cont_xi := h₁.cont_xi.union_of_isClosed h₂.cont_xi hc₁ hc₂
  eq_out := by
    intro u a b hua hab hs
    rcases hout u a b hab hs with h | h
    · exact h₁.eq_out u a b hua hab h
    · exact h₂.eq_out u a b hua hab h
  eq_in := by
    intro a b v hab hbv hs
    rcases hin a b v hab hs with h | h | ⟨c, hac, hcb, hl, hr⟩
    · exact h₁.eq_in a b v hab hbv h
    · exact h₂.eq_in a b v hab hbv h
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h₁.eq_in a c v hac (hcb.trans_lt hbv) hl
      obtain ⟨k1, k2, k3, k4, k5, k6⟩ := h₂.eq_in c b v hcb hbv hr
      exact ⟨h1.trans k1, h2.trans k2, h3.trans k3, h4.trans k4, h5.trans k5, h6.trans k6⟩
  ac_out := by
    intro u a b hab hs
    rcases hout u a b hab hs with h | h
    · exact h₁.ac_out u a b hab h
    · exact h₂.ac_out u a b hab h
  ac_in := by
    intro a b v hab hs
    rcases hin a b v hab hs with h | h | ⟨c, hac, hcb, hl, hr⟩
    · exact h₁.ac_in a b v hab h
    · exact h₂.ac_in a b v hab h
    · obtain ⟨h1, h2, h3, h4⟩ := h₁.ac_in a c v hac hl
      obtain ⟨k1, k2, k3, k4⟩ := h₂.ac_in c b v hcb hr
      exact ⟨h1.trans_real k1 hac hcb, h2.trans_real k2 hac hcb,
        h3.trans_real k3 hac hcb, h4.trans_complex k4 hac hcb⟩
  bv_loc := by
    intro K hKD hK
    obtain ⟨B₁, hB₁, ho₁, hi₁⟩ := h₁.bv_loc (K ∩ D₁) inter_subset_right (hK.inter_right hc₁)
    obtain ⟨B₂, hB₂, ho₂, hi₂⟩ := h₂.bv_loc (K ∩ D₂) inter_subset_right (hK.inter_right hc₂)
    refine ⟨B₁ + B₂, ENNReal.add_lt_top.mpr ⟨hB₁, hB₂⟩, ?_, ?_⟩
    · intro u a b hs
      by_cases hab : a ≤ b
      · rcases hout u a b hab (hs.trans hKD) with h | h
        · obtain ⟨h1, h2, h3, h4⟩ := ho₁ u a b (fun p hp => ⟨hs hp, h hp⟩)
          exact ⟨h1.trans le_self_add, h2.trans le_self_add,
            h3.trans le_self_add, h4.trans le_self_add⟩
        · obtain ⟨h1, h2, h3, h4⟩ := ho₂ u a b (fun p hp => ⟨hs hp, h hp⟩)
          exact ⟨h1.trans le_add_self, h2.trans le_add_self,
            h3.trans le_add_self, h4.trans le_add_self⟩
      · simp only [eVariationOn.subsingleton _ (subsingleton_Icc_of_ge (le_of_not_ge hab)),
          zero_le, and_self]
    · intro a b v hs
      by_cases hab : a ≤ b
      · rcases hin a b v hab (hs.trans hKD) with h | h | ⟨c, hac, hcb, hl, hr⟩
        · obtain ⟨h1, h2, h3, h4⟩ := hi₁ a b v (fun p hp => ⟨hs hp, h hp⟩)
          exact ⟨h1.trans le_self_add, h2.trans le_self_add,
            h3.trans le_self_add, h4.trans le_self_add⟩
        · obtain ⟨h1, h2, h3, h4⟩ := hi₂ a b v (fun p hp => ⟨hs hp, h hp⟩)
          exact ⟨h1.trans le_add_self, h2.trans le_add_self,
            h3.trans le_add_self, h4.trans le_add_self⟩
        · obtain ⟨h1, h2, h3, h4⟩ := hi₁ a c v
            (fun p hp => ⟨hs ⟨hp.1, hp.2.1.trans hcb, hp.2.2⟩, hl hp⟩)
          obtain ⟨k1, k2, k3, k4⟩ := hi₂ c b v
            (fun p hp => ⟨hs ⟨hac.trans hp.1, hp.2.1, hp.2.2⟩, hr hp⟩)
          rw [eVariationOn.Icc_eq_add _ hac hcb, eVariationOn.Icc_eq_add _ hac hcb,
            eVariationOn.Icc_eq_add _ hac hcb, eVariationOn.Icc_eq_add _ hac hcb]
          exact ⟨add_le_add h1 k1, add_le_add h2 k2, add_le_add h3 k3, add_le_add h4 k4⟩
      · simp only [eVariationOn.subsingleton _ (subsingleton_Icc_of_ge (le_of_not_ge hab)),
          zero_le, and_self]
  axis_small_var := fun t _ η hη =>
    axis_small_var_union_of_segment_cover h₁ h₂ hc₁ hc₂ hout hin t η hη
  axis := fun t ht => ht.elim (h₁.axis t) (h₂.axis t)
  axis_mu := fun t _ => axis_mu_union h₁ h₂ hc₁ hc₂ t

/-- Agreeing configurations on two closed characteristic pieces have a common
configuration in the frozen class on their union. The explicit segment cover is
essential: arbitrary closed unions do not have this property. -/
theorem glue_fields_of_segment_cover {e : ℝ} {S T : Fields}
    {D₁ D₂ : Set (ℝ × ℝ)} (hS : IsSolution e S D₁) (hT : IsSolution e T D₂)
    (he : S.EqOn T (D₁ ∩ D₂)) (hc₁ : IsClosed D₁) (hc₂ : IsClosed D₂)
    (hout : ∀ u a b, a ≤ b → outSeg u a b ⊆ D₁ ∪ D₂ →
      outSeg u a b ⊆ D₁ ∨ outSeg u a b ⊆ D₂)
    (hin : ∀ a b v, a ≤ b → inSeg a b v ⊆ D₁ ∪ D₂ →
      inSeg a b v ⊆ D₁ ∨ inSeg a b v ⊆ D₂ ∨
      ∃ c, a ≤ c ∧ c ≤ b ∧ inSeg a c v ⊆ D₁ ∧ inSeg c b v ⊆ D₂) :
    ∃ G : Fields, IsSolution e G (D₁ ∪ D₂) ∧ G.EqOn S D₁ ∧ G.EqOn T D₂ := by
  classical
  let G : Fields := {
    r := fun u v => if (u, v) ∈ D₁ then S.r u v else T.r u v
    lam := fun u v => if (u, v) ∈ D₁ then S.lam u v else T.lam u v
    nu := fun u v => if (u, v) ∈ D₁ then S.nu u v else T.nu u v
    m := fun u v => if (u, v) ∈ D₁ then S.m u v else T.m u v
    Q := fun u v => if (u, v) ∈ D₁ then S.Q u v else T.Q u v
    phi := fun u v => if (u, v) ∈ D₁ then S.phi u v else T.phi u v
    A := fun u v => if (u, v) ∈ D₁ then S.A u v else T.A u v
    theta := fun u v => if (u, v) ∈ D₁ then S.theta u v else T.theta u v
    xi := fun u v => if (u, v) ∈ D₁ then S.xi u v else T.xi u v
  }
  have he₁ : G.EqOn S D₁ := by
    rintro ⟨u, v⟩ hp
    simp only [G, ite_eq_left hp, and_self]
  have he₂ : G.EqOn T D₂ := by
    rintro ⟨u, v⟩ hp
    by_cases hm : (u, v) ∈ D₁
    · simpa only [G, ite_eq_left hm] using he (u, v) ⟨hm, hp⟩
    · simp only [G, ite_eq_right hm, and_self]
  exact ⟨G, isSolution_union_of_segment_cover (isSolution_congr hS he₁.symm)
    (isSolution_congr hT he₂.symm) hc₁ hc₂ hout hin, he₁, he₂⟩

namespace Closure

/-- [internal]
The field-gluing step on the exact frozen union, after pullback and overlap
uniqueness. All nine primary fields agree on the overlap. No covariance or
restart theorem is assumed or proved here (`charged_SF_new_version.tex:L4189`–L4190). -/
theorem glue_original_triangle (ui e us vp : ℝ) (S Snew : Fields)
    (_hui : ui < 0) (hus : us ∈ Ioo ui 0) (hvp : 0 < vp)
    (hold : IsSolution e S (origDomain ui)) (hnew : IsSolution e Snew (triangle us vp))
    (heq : Snew.EqOn S (origDomain ui ∩ triangle us vp)) :
    ∃ G : Fields, IsSolution e G (origDomain ui ∪ triangle us vp) ∧
      G.EqOn S (origDomain ui) ∧ G.EqOn Snew (triangle us vp) := by
  have hsub := old_patch_subset_origDomain (ui := ui) hus.2
  have hcover := old_patch_union_triangle (ui := ui) hus.2 hvp.le
  have he : S.EqOn Snew ((triangle ui 0 ∩ {p : ℝ × ℝ | p.1 ≤ us}) ∩ triangle us vp) :=
    heq.symm.mono (fun _ hp => ⟨hsub hp.1, hp.2⟩)
  obtain ⟨G, hG, hGo, hGn⟩ := glue_fields_of_segment_cover
    (Local.isSolution_mono hold hsub) hnew he (isClosed_old_patch ui us)
    (isClosed_triangle us vp)
    (fun _ _ _ _ hs => outSeg_subset_old_or_new hvp.le (hs.trans hcover.subset))
    (fun _ _ _ hab hs => inSeg_subset_old_or_new_or_split hus.1.le hvp.le hab
      (hs.trans hcover.subset))
  refine ⟨G, hcover ▸ hG, ?_, hGn⟩
  intro p hp
  by_cases hu : p.1 ≤ us
  · exact hGo p ⟨⟨hp.1, hp.2.2.1, hp.2.2.2⟩, hu⟩
  · have hn : p ∈ triangle us vp :=
      ⟨le_of_not_ge hu, hp.2.2.1, hp.2.2.2.trans hvp.le⟩
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hGn p hn
    obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := heq p ⟨hp, hn⟩
    exact ⟨h1.trans k1, h2.trans k2, h3.trans k3, h4.trans k4, h5.trans k5,
      h6.trans k6, h7.trans k7, h8.trans k8, h9.trans k9⟩

end Closure

end EmcsfAcExtension.Global
