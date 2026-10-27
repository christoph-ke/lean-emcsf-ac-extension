module

public import EmcsfAcExtension.Local.Construction.ContinuationInputs
public import EmcsfAcExtension.Local.Broad.RectangleState
import EmcsfAcExtension.Local.Construction.StripNormalized
import EmcsfAcExtension.Local.Construction.Strip
import EmcsfAcExtension.Local.Construction.StripGlue
import EmcsfAcExtension.Local.Construction.StripData
import EmcsfAcExtension.Local.Construction.ContinuationParameters
import EmcsfAcExtension.Local.Construction.ContinuationBridge
import EmcsfAcExtension.Local.Construction.Overlap
import EmcsfAcExtension.Local.Api.EqOn
import EmcsfAcExtension.Local.Broad.ScalarAverage
import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # Completing the positive-radius continuation strip

The lifespan is fixed before the old apex. Exact first-jet matching
glues the actual full-system strip to the old triangle. Broad uniqueness
on the original cone preserves its data above the old apex.
-/

public section

open Set MeasureTheory
open scoped NNReal

namespace EmcsfAcExtension.Local

open Broad

/-- [node restart-sec-independent-null-construction#positive-radius-strip]
The C¹ reading of charged_SF_new_version.tex:L6293–6372 admits a uniform full-system
strip. Its positive height depends on the fixed `e,T,B₀,ℓ,η,J,yi` and
original wedge, before the old apex and old solution. Primary values and
full first derivatives are bounded by `2*(4*B₀)` on the glued domain.
The expansion margin is `ℓ/2`, and the entering data are the original
datum on the complete new interval. Only old-axis gauge is asserted.
The complete `C1BoundOn` doubles from `B₀` to `2*B₀`, and the strip
radius is at least `3*ℓ*η/8`, uniformly in the old apex.
No pending input is needed beyond the actual old and original solutions. -/
theorem c1_positive_radius_strip
    {e T a : ℝ} {h : ℝ → ℂ} {F₀ : Fields}
    (B₀ ℓ η : ℝ) (J : ℝ≥0) (yi : ℝ → RectangleIncoming)
    (hT : 0 < T) (hB : 1 ≤ B₀) (hℓ : 0 < ℓ) (hη : 0 < η)
    (hℓB : ℓ ≤ B₀⁻¹) (hyi : LipschitzWith J yi)
    (hyic : ContDiffOn ℝ 1 yi (Icc 0 T))
    (ha : 0 < a) (haT : a ≤ T)
    (hF₀ : IsC1Solution e F₀ (continuationWedge 0 a T))
    (hdata₀ : IsRestartData F₀ h T)
    (hyi₀ : EqOn yi (fun v => (F₀.lam 0 v, F₀.theta 0 v)) (Icc 0 T)) :
    ∃ δ₀ > 0, ∀ S b : ℝ, 2*η < S → S < b → b-S ≤ δ₀ → b ≤ T →
      ∀ Old : Fields, IsC1Solution e Old (triangle 0 S) →
        IsRestartData Old h S → C1BoundOn Old (triangle 0 S) B₀ →
      let d := S-3*η/4
      ∃ H : Fields,
        IsC1Solution e H (triangle 0 S ∪ (Icc 0 d ×ˢ Icc S b)) ∧
        H.EqOn Old (triangle 0 S) ∧
        (∀ p ∈ triangle 0 S ∪ (Icc 0 d ×ˢ Icc S b),
          ∀ f ∈ ({H.lam} : Set (ℝ → ℝ → ℝ)),
            ‖f p.1 p.2‖ ≤ 2*(4*B₀) ∧
            ‖fderivWithin ℝ (Function.uncurry f)
              (triangle 0 S ∪ (Icc 0 d ×ˢ Icc S b)) p‖ ≤ 2*(4*B₀)) ∧
        (∀ p ∈ triangle 0 S ∪ (Icc 0 d ×ˢ Icc S b),
          ∀ f ∈ ({H.phi,H.theta} : Set (ℝ → ℝ → ℂ)),
            ‖f p.1 p.2‖ ≤ 2*(4*B₀) ∧
            ‖fderivWithin ℝ (Function.uncurry f)
              (triangle 0 S ∪ (Icc 0 d ×ˢ Icc S b)) p‖ ≤ 2*(4*B₀)) ∧
        (∀ p ∈ triangle 0 S ∪ (Icc 0 d ×ˢ Icc S b), ℓ/2 ≤ H.lam p.1 p.2) ∧
        (∀ v ∈ Icc 0 b, H.r 0 v = v/2 ∧ H.a 0 v = h v) ∧
        (∀ t ∈ Icc 0 S, H.A t t = 0) ∧
        (∀ p ∈ triangle 0 S ∪ (Icc 0 d ×ˢ Icc S b),
          ‖rectangle_state H p‖ ≤ 4*B₀ ∧
          ‖fderivWithin ℝ (rectangle_state H)
            (triangle 0 S ∪ (Icc 0 d ×ˢ Icc S b)) p‖ ≤ 4*B₀) ∧
        C1BoundOn H (triangle 0 S ∪ (Icc 0 d ×ˢ Icc S b)) (2*B₀) ∧
        ∀ p ∈ Icc 0 d ×ˢ Icc S b, 3*ℓ*η/8 ≤ H.r p.1 p.2 := by
  have hBpos : 0 < B₀ := zero_lt_one.trans_le hB
  obtain ⟨δ₀,hδ₀,hstrip⟩ := uniform_c1_bounded_strip_from_old e T B₀ ℓ η J yi
    hT hB hℓ hη hℓB hyi hyic
  refine ⟨δ₀,hδ₀,?_⟩
  intro S b hηS hSb hheight hbT Old hOld hdataOld hbound
  let d := S-3*η/4
  have hS : 0 < S := by linarith
  have hd : 0 < d := by dsimp [d]; linarith
  have hdS : d < S := by dsimp [d]; linarith
  have hsT : S ≤ T := hSb.le.trans hbT
  have hagree := c1_initial_cone_fields_agree ha haT hS hsT hF₀ hOld hdata₀ hdataOld
  have hOldYi : ∀ v ∈ Icc 0 S, (rectangle_state Old (0,v)).1 = yi v := by
    intro v hv
    have hvT : v ∈ Icc 0 T := ⟨hv.1,hv.2.trans hsT⟩
    have heq := (rectangle_state_eq_iff F₀ Old (0,v)).mpr
      (hagree (0,v) ⟨rfl,hv⟩)
    exact (congrArg Prod.fst heq).symm.trans (hyi₀ hvT).symm
  obtain ⟨Z,_hZ,hZc,hNew,hNewBound,hlower,hYi,_hX,hseam⟩ :=
    hstrip S b hηS hSb hheight hbT Old hOld hbound hOldYi
  let New := rectangle_fields Z
  have hstate : rectangle_state New = Z := rfl
  have hNew' : IsC1Solution e New (Icc 0 d ×ˢ Icc S b) := hNew
  have holdBound p (hp : p ∈ triangle 0 S) :
      ‖rectangle_state Old p‖ ≤ 4*B₀ ∧
      ‖fderivWithin ℝ (rectangle_state Old) (triangle 0 S) p‖ ≤ 4*B₀ := by
    exact ⟨(norm_continuation_state_le hbound hp).trans (by linarith),
      (norm_fderiv_continuation_state_le hOld (uniqueDiffOn_triangle hS) hbound hp).trans
        (by linarith)⟩
  have hnewBound p (hp : p ∈ Icc 0 d ×ˢ Icc S b) :
      ‖rectangle_state New p‖ ≤ 4*B₀ ∧
      ‖fderivWithin ℝ (rectangle_state New) (Icc 0 d ×ˢ Icc S b) p‖ ≤ 4*B₀ := by
    exact ⟨(norm_continuation_state_le hNewBound hp).trans (by linarith),
      (norm_fderiv_continuation_state_le hNew' (uniqueDiffOn_rectangle hd hSb)
        hNewBound hp).trans (by linarith)⟩
  have hnewLam p (hp : p ∈ Icc 0 d ×ˢ Icc S b) : ℓ/2 ≤ New.lam p.1 p.2 := by
    have heq : (2*B₀)⁻¹ = B₀⁻¹/2 := by simp [mul_inv_rev, div_eq_mul_inv]
    have hh := (hNewBound p hp).1
    rw [heq] at hh
    linarith
  obtain ⟨H,hH,hHO,hHN,hHbound,hHlam⟩ := c1_triangle_strip_glue_with_bounds hd hdS hSb
    hOld hNew' (fun u hu => by simpa only [hstate] using (hlower u hu).symm)
    (fun u hu => by simpa only [hstate] using (hseam u hu).symm)
    holdBound hnewBound
    (fun p hp => (by linarith [hℓB.trans (hbound p hp).1] : ℓ/2 ≤ Old.lam p.1 p.2))
    hnewLam
  have hfull : C1BoundOn H (triangle 0 S ∪ (Icc 0 d ×ˢ Icc S b)) (2*B₀) := by
    apply c1BoundOn_union_of_classical hH (uniqueDiffOn_triangle hS)
      (uniqueDiffOn_rectangle hd hSb)
    · exact C1BoundOn.congr hHO
        (continuation_c1BoundOn_weaken hBpos (by linarith) hbound)
    · exact C1BoundOn.congr hHN hNewBound
  have hU : UniqueDiffOn ℝ (triangle 0 S ∪ (Icc 0 d ×ˢ Icc S b)) := by
    intro p hp
    rcases hp with hp | hp
    · exact (uniqueDiffOn_triangle hS p hp).mono subset_union_left
    · exact (uniqueDiffOn_rectangle hd hSb p hp).mono subset_union_right
  have hprimary p hp := primary_cone_bounds_of_state_bound hH hU hp
    (hHbound p hp).1 (hHbound p hp).2
  have hBroad := IsC1Solution.toIsSolution_triangle_strip hS hd hdS hSb hH
  have hradius p (hp : p ∈ Icc 0 d ×ˢ Icc S b) : 3*ℓ*η/8 ≤ H.r p.1 p.2 := by
    have hsegment : outSeg p.1 p.1 p.2 ⊆
        triangle 0 S ∪ (Icc 0 d ×ˢ Icc S b) := by
      rintro ⟨u,v⟩ ⟨rfl,hv⟩
      by_cases hvS : v ≤ S
      · exact Or.inl ⟨hp.1.1,hv.1,hvS⟩
      · exact Or.inr ⟨hp.1,(lt_of_not_ge hvS).le,hv.2.trans hp.2.2⟩
    have horder : p.1 ≤ p.2 := hp.1.2.trans (hdS.le.trans hp.2.1)
    have hr := outgoing_radius_lower hBroad horder hsegment
      (fun v hv => hHlam (p.1,v) (hsegment ⟨rfl,hv⟩))
    have hsep : 3*η/4 ≤ p.2-p.1 := by
      have hu := hp.1.2
      change p.1 ≤ S-3*η/4 at hu
      linarith [hp.2.1]
    calc 3*ℓ*η/8 = (ℓ/2)*(3*η/4) := by ring
         _ ≤ (ℓ/2)*(p.2-p.1) := mul_le_mul_of_nonneg_left hsep (half_pos hℓ).le
         _ ≤ H.r p.1 p.2 := hr
  have hNewBroad := hNew'.toIsSolution_offAxis
    (isCompact_Icc.prod isCompact_Icc) (uniqueDiffOn_rectangle hd hSb)
    (fun p hp => hp.1.2.trans_lt (hdS.trans_le hp.2.1))
  have hinitial := c1_strip_initial_data ha haT hd.le hdS hSb.le hbT
    hF₀ hOld hdata₀ hdataOld hNewBroad
    (fun v hv => by
      have hy := hYi 0 ⟨le_rfl,hd.le⟩ v hv
      simp only [intervalIntegral.integral_same, add_zero] at hy
      exact hy.trans (hyi₀ ⟨hS.le.trans hv.1,hv.2.trans hbT⟩))
    (by simpa only [hstate] using congrArg Prod.snd (hlower 0 ⟨le_rfl,hd.le⟩))
  refine ⟨H,hH,hHO,?_,?_,hHlam,?_,?_,hHbound,hfull,hradius⟩
  · intro p hp f hf
    have hf' : f = H.lam := Set.mem_singleton_iff.mp hf
    subst f
    exact ⟨(hprimary p hp).1.1.trans (by linarith),
      (hprimary p hp).1.2.trans (by linarith)⟩
  · intro p hp f hf
    simp only [mem_insert_iff,mem_singleton_iff] at hf
    rcases hf with rfl | rfl
    · exact ⟨(hprimary p hp).2.1.1.trans (by linarith),
        (hprimary p hp).2.1.2.trans (by linarith)⟩
    · exact ⟨(hprimary p hp).2.2.1.trans (by linarith),
        (hprimary p hp).2.2.2.trans (by linarith)⟩
  · intro v hv
    by_cases hvS : v ≤ S
    · have hp : (0,v) ∈ triangle 0 S := ⟨le_rfl,hv.1,hvS⟩
      exact ⟨(hHO.r hp).trans (hdataOld.1 v ⟨hv.1,hvS⟩).1,
        (hHO.a hp).trans (hdataOld.1 v ⟨hv.1,hvS⟩).2⟩
    · have hvs : v ∈ Icc S b := ⟨(lt_of_not_ge hvS).le,hv.2⟩
      have hp : (0,v) ∈ Icc 0 d ×ˢ Icc S b := ⟨⟨le_rfl,hd.le⟩,hvs⟩
      exact ⟨(hHN.r hp).trans (hinitial.2 v hvs).1,
        (hHN.a hp).trans (hinitial.2 v hvs).2⟩
  · intro t ht
    exact (hHO.A ⟨ht.1,le_rfl,ht.2⟩).trans (hdataOld.2 t ht)

end EmcsfAcExtension.Local
