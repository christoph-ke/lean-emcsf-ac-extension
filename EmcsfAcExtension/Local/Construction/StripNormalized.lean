module

public import EmcsfAcExtension.Local.Defs.C1Bound
public import EmcsfAcExtension.Local.Construction.StripFields
public import EmcsfAcExtension.Local.Construction.ContinuationJetTube
import EmcsfAcExtension.Local.Construction.StripFromOld
import EmcsfAcExtension.Local.Construction.StripStateBounds
import EmcsfAcExtension.Local.Broad.ScalarAverage
import EmcsfAcExtension.Local.Calculus.C1ToSolution2
import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # The full doubled continuation bound on the constructed strip

The fixed normalization jet tube controls both normalized scalars and
all three nondegeneracy margins. Its tolerances are passed to the actual
strip constructor before the old apex and solution are selected.
-/

public section

open Set MeasureTheory
open scoped NNReal

namespace EmcsfAcExtension.Local

open Broad

/-- Chain rule for the actual outgoing normalized scalar and the full
within-domain first derivative of the characteristic state. -/
theorem fderivWithin_normalized_a_state {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : ContDiffOn ℝ 1 (rectangle_state S) D) (hU : UniqueDiffOn ℝ D)
    {p : ℝ × ℝ} (hp : p ∈ D) (hl : S.lam p.1 p.2 ≠ 0) :
    fderivWithin ℝ (Function.uncurry S.a) D p =
      (fderiv ℝ continuation_normalized_a (rectangle_state S p)).comp
        (fderivWithin ℝ (rectangle_state S) D p) := by
  have hd := ((contDiffAt_continuation_normalized_a hl).differentiableAt
    (by decide)).hasFDerivAt.comp_hasFDerivWithinAt p
    (hS.differentiableOn (by decide) p hp).hasFDerivWithinAt
  exact hd.fderivWithin (hU p hp)

/-- Chain rule for the actual incoming normalized scalar, requiring
only C¹ fields and a nonzero incoming expansion. -/
theorem fderivWithin_normalized_b_state {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : ContDiffOn ℝ 1 (rectangle_state S) D) (hU : UniqueDiffOn ℝ D)
    {p : ℝ × ℝ} (hp : p ∈ D) (hn : S.nu p.1 p.2 ≠ 0) :
    fderivWithin ℝ (Function.uncurry S.b) D p =
      (fderiv ℝ continuation_normalized_b (rectangle_state S p)).comp
        (fderivWithin ℝ (rectangle_state S) D p) := by
  have hd := ((contDiffAt_continuation_normalized_b hn).differentiableAt
    (by decide)).hasFDerivAt.comp_hasFDerivWithinAt p
    (hS.differentiableOn (by decide) p hp).hasFDerivWithinAt
  exact hd.fderivWithin (hU p hp)

/-- The product-state bounds and the two actual normalized-scalar
bounds give the literal frozen continuation bound with coefficient one.
This helper introduces no new bound or nondegeneracy constant. -/
theorem c1BoundOn_of_state_and_normalized_bounds {e C : ℝ} {S : Fields}
    {D : Set (ℝ × ℝ)} (hS : IsC1Solution e S D) (hU : UniqueDiffOn ℝ D)
    (hmargin : ∀ p ∈ D, C⁻¹ ≤ S.lam p.1 p.2 ∧
      C⁻¹ ≤ -S.nu p.1 p.2 ∧ C⁻¹ ≤ 1 - S.mu p.1 p.2)
    (hstate : ∀ p ∈ D, ‖rectangle_state S p‖ ≤ C ∧
      ‖fderivWithin ℝ (rectangle_state S) D p‖ ≤ C)
    (hnormalized : ∀ p ∈ D,
      ‖S.a p.1 p.2‖ ≤ C ∧ ‖S.b p.1 p.2‖ ≤ C ∧
      ‖fderivWithin ℝ (Function.uncurry S.a) D p‖ ≤ C ∧
      ‖fderivWithin ℝ (Function.uncurry S.b) D p‖ ≤ C) : C1BoundOn S D C := by
  intro p hp
  obtain ⟨hl,hn,hg⟩ := hmargin p hp
  obtain ⟨hv,hd⟩ := hstate p hp
  obtain ⟨ha,hb,hda,hdb⟩ := hnormalized p hp
  have dr := (hS.c1_r.differentiableOn (by decide) p hp).hasFDerivWithinAt
  have dl := (hS.c1_lam.differentiableOn (by decide) p hp).hasFDerivWithinAt
  have dn := (hS.c1_nu.differentiableOn (by decide) p hp).hasFDerivWithinAt
  have dm := (hS.c1_m.differentiableOn (by decide) p hp).hasFDerivWithinAt
  have dq := (hS.c1_Q.differentiableOn (by decide) p hp).hasFDerivWithinAt
  have dA := (hS.c1_A.differentiableOn (by decide) p hp).hasFDerivWithinAt
  have dp := (hS.c1_phi.differentiableOn (by decide) p hp).hasFDerivWithinAt
  have dt := (hS.c1_theta.differentiableOn (by decide) p hp).hasFDerivWithinAt
  have dx := (hS.c1_xi.differentiableOn (by decide) p hp).hasFDerivWithinAt
  have hfull := (dl.prodMk dt).prodMk
    (dr.prodMk (dn.prodMk (dm.prodMk (dq.prodMk (dA.prodMk (dp.prodMk dx))))))
  have heq := hfull.fderivWithin (hU p hp)
  simp only [Function.uncurry_def] at heq
  change ‖fderivWithin ℝ
    (fun q : ℝ × ℝ => ((S.lam q.1 q.2,S.theta q.1 q.2),
      (S.r q.1 q.2,S.nu q.1 q.2,S.m q.1 q.2,S.Q q.1 q.2,
        S.A q.1 q.2,S.phi q.1 q.2,S.xi q.1 q.2))) D p‖ ≤ C at hd
  rw [heq] at hd
  simp only [ContinuousLinearMap.opNorm_prod, Prod.norm_def, max_le_iff] at hd
  simp only [rectangle_state, Prod.norm_def, max_le_iff] at hv
  refine ⟨hl,hn,hg,?_,?_⟩
  · intro f hf
    simp only [mem_insert_iff,mem_singleton_iff] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨hv.2.1,hd.2.1⟩
    · exact ⟨hv.1.1,hd.1.1⟩
    · exact ⟨hv.2.2.1,hd.2.2.1⟩
    · exact ⟨hv.2.2.2.1,hd.2.2.2.1⟩
    · exact ⟨hv.2.2.2.2.1,hd.2.2.2.2.1⟩
    · exact ⟨hv.2.2.2.2.2.1,hd.2.2.2.2.2.1⟩
  · intro f hf
    simp only [mem_insert_iff,mem_singleton_iff] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · exact ⟨hv.2.2.2.2.2.2.1,hd.2.2.2.2.2.2.1⟩
    · exact ⟨hv.1.2,hd.1.2⟩
    · exact ⟨hv.2.2.2.2.2.2.2,hd.2.2.2.2.2.2.2⟩
    · exact ⟨ha,hda⟩
    · exact ⟨hb,hdb⟩

private theorem norm_le_double_of_difference {E : Type*} [NormedAddCommGroup E]
    {x y : E} {B : ℝ} (hxy : ‖x - y‖ ≤ B) (hy : ‖y‖ ≤ B) : ‖x‖ ≤ 2*B := by
  calc ‖x‖ = ‖(x-y)+y‖ := by rw [sub_add_cancel]
       _ ≤ ‖x - y‖+‖y‖ := norm_add_le _ _
       _ ≤ B+B := add_le_add hxy hy
       _ = 2*B := by ring

/-- The actual positive-radius strip satisfies the complete frozen
continuation bound `2*B₀`, including both normalized scalars, their full
first derivatives and every inverse-size geometric margin. The lifespan
depends only on the fixed `e,T,B₀,ℓ,η,J,yi`, before the old apex and old
solution. The canonical old margin `B₀⁻¹` supplies the doubled inverse
margin even if the source-tube parameter `ℓ` is smaller. -/
theorem uniform_c1_bounded_strip_from_old
    (e T B₀ ℓ η : ℝ) (J : ℝ≥0) (yi : ℝ → RectangleIncoming)
    (hT : 0 < T) (hB : 1 ≤ B₀) (hℓ : 0 < ℓ) (hη : 0 < η)
    (hℓB : ℓ ≤ B₀⁻¹) (hyi : LipschitzWith J yi)
    (hyic : ContDiffOn ℝ 1 yi (Icc 0 T)) :
    ∃ δ₀ > 0, ∀ S b : ℝ, 2*η < S → S < b → b-S ≤ δ₀ → b ≤ T →
      ∀ Old : Fields, IsC1Solution e Old (triangle 0 S) →
        C1BoundOn Old (triangle 0 S) B₀ →
        (∀ v ∈ Icc 0 S, (rectangle_state Old (0,v)).1 = yi v) →
      let d := S-3*η/4
      ∃ F : ℝ × ℝ → RectangleState,
        Continuous F ∧ ContDiffOn ℝ 1 F (Icc 0 d ×ˢ Icc S b) ∧
        IsC1Solution e (rectangle_fields F) (Icc 0 d ×ˢ Icc S b) ∧
        C1BoundOn (rectangle_fields F) (Icc 0 d ×ˢ Icc S b) (2*B₀) ∧
        (∀ u ∈ Icc 0 d, F (u,S) = rectangle_state Old (u,S)) ∧
        (∀ u ∈ Icc 0 d, ∀ v ∈ Icc S b,
          (F (u,v)).1 = yi v + ∫ s in 0..u, rectangle_in_source e (F (s,v))) ∧
        (∀ u ∈ Icc 0 d, ∀ v ∈ Icc S b,
          (F (u,v)).2 = (rectangle_state Old (u,S)).2 +
            ∫ t in S..v, rectangle_out_source e (F (u,t))) ∧
        (∀ u ∈ Icc 0 d,
          fderivWithin ℝ F (Icc 0 d ×ˢ Icc S b) (u,S) =
            fderivWithin ℝ (rectangle_state Old) (triangle 0 S) (u,S)) := by
  have hBpos : 0 < B₀ := zero_lt_one.trans_le hB
  have hiB : 0 < B₀⁻¹ := inv_pos.mpr hBpos
  let r₀ := 3*ℓ*η/8
  have hr₀ : 0 < r₀ := by dsimp [r₀]; positivity
  obtain ⟨ζ,hζ,q,hq,htube⟩ :=
    continuation_normalization_jet_tube B₀ B₀⁻¹ r₀ hB hiB hr₀
  obtain ⟨δ₀,hδ₀,hstrip⟩ := uniform_c1_strip_from_old_with_proximity
    e T B₀ ℓ η (min 1 ζ) (min B₀ q) J yi hT hBpos hℓ hη
    (lt_min zero_lt_one hζ) (lt_min hBpos hq) hℓB hyi hyic
  refine ⟨δ₀,hδ₀,?_⟩
  intro S b hηS hSb hheight hbT Old hOld hbound hOldYi
  let d := S-3*η/4
  have hS : 0 < S := by linarith
  have hd : 0 < d := by dsimp [d]; linarith
  have hdS : d < S := by dsimp [d]; linarith
  obtain ⟨F,hFc,hFC,hSol,_hK,_hOldK,hlower,hYi,hXb,hnear,hder,hseam,hsize⟩ :=
    hstrip S b hηS hSb hheight hbT Old hOld hbound hOldYi
  let New := rectangle_fields F
  let R := Icc 0 d ×ˢ Icc S b
  have hstate : rectangle_state New = F := rfl
  have hU : UniqueDiffOn ℝ R := uniqueDiffOn_rectangle hd hSb
  have hUold := uniqueDiffOn_triangle hS
  have hOldC := hOld.contDiffOn_rectangle_state
  have hNewC : ContDiffOn ℝ 1 (rectangle_state New) R := hFC
  have hpoint (p : ℝ × ℝ) (hp : p ∈ R) :
      ((2*B₀)⁻¹ ≤ New.lam p.1 p.2 ∧ (2*B₀)⁻¹ ≤ -New.nu p.1 p.2 ∧
        (2*B₀)⁻¹ ≤ 1 - New.mu p.1 p.2) ∧
      (‖rectangle_state New p‖ ≤ 2*B₀ ∧
        ‖fderivWithin ℝ (rectangle_state New) R p‖ ≤ 2*B₀) ∧
      (‖New.a p.1 p.2‖ ≤ 2*B₀ ∧ ‖New.b p.1 p.2‖ ≤ 2*B₀ ∧
        ‖fderivWithin ℝ (Function.uncurry New.a) R p‖ ≤ 2*B₀ ∧
        ‖fderivWithin ℝ (Function.uncurry New.b) R p‖ ≤ 2*B₀) := by
    have hpOld : (p.1,S) ∈ triangle 0 S := ⟨hp.1.1,hp.1.2.trans hdS.le,le_rfl⟩
    have hOldB := hbound (p.1,S) hpOld
    have hL := norm_fderiv_continuation_state_le hOld hUold hbound hpOld
    have hw := norm_continuation_state_le hbound hpOld
    have hrad := outgoing_radius_lower (hOld.toIsSolution hS) hpOld.2.1
      (show outSeg p.1 p.1 S ⊆ triangle 0 S from fun z hz =>
        ⟨by simpa only [hz.1] using hpOld.1,
          by simpa only [hz.1] using hz.2.1,hz.2.2⟩)
      (fun v hv => hℓB.trans (hbound (p.1,v) ⟨hpOld.1,hv.1,hv.2⟩).1)
    have hrOld : r₀ ≤ (rectangle_state Old (p.1,S)).2.1 := by
      apply le_trans _ hrad
      have hsep : 3*η/8 ≤ S-p.1 := by
        have hu := hp.1.2
        dsimp [d] at hu
        linarith
      calc r₀ = ℓ*(3*η/8) := by dsimp [r₀]; ring
           _ ≤ ℓ*(S-p.1) := mul_le_mul_of_nonneg_left hsep hℓ.le
    obtain ⟨hVa,hVb,hDa,hDb,hgap,_hrnew,hLam,hNu⟩ := htube
      (rectangle_state Old (p.1,S)) (F p)
      (fderivWithin ℝ (rectangle_state Old) (triangle 0 S) (p.1,S))
      (fderivWithin ℝ F R p) hw hrOld hOldB.1 hOldB.2.1 hOldB.2.2.1 hL
      ((hnear p.1 hp.1 p.2 hp.2).trans (min_le_right 1 ζ))
      (((hder p hp).1).trans (min_le_right B₀ q))
    have hLamOld : Old.lam p.1 S ≠ 0 := ne_of_gt (hiB.trans_le hOldB.1)
    have hNuOld : Old.nu p.1 S ≠ 0 := ne_of_lt (by linarith only [hiB,hOldB.2.1])
    have hLamNew : New.lam p.1 p.2 ≠ 0 := ne_of_gt (lt_of_lt_of_le (half_pos hiB) hLam)
    have hNuNew : New.nu p.1 p.2 ≠ 0 := by
      change (F p).2.2.1 ≠ 0
      apply ne_of_lt
      linarith only [hiB,hNu]
    have hDaeqOld := fderivWithin_normalized_a_state hOldC hUold hpOld hLamOld
    have hDbeqOld := fderivWithin_normalized_b_state hOldC hUold hpOld hNuOld
    have hDaeqNew := fderivWithin_normalized_a_state hNewC hU hp hLamNew
    have hDbeqNew := fderivWithin_normalized_b_state hNewC hU hp hNuNew
    have hDa' : ‖fderivWithin ℝ (Function.uncurry New.a) R p-
        fderivWithin ℝ (Function.uncurry Old.a) (triangle 0 S) (p.1,S)‖ ≤ B₀ := by
      rw [hDaeqNew,hDaeqOld]
      exact hDa
    have hDb' : ‖fderivWithin ℝ (Function.uncurry New.b) R p-
        fderivWithin ℝ (Function.uncurry Old.b) (triangle 0 S) (p.1,S)‖ ≤ B₀ := by
      rw [hDbeqNew,hDbeqOld]
      exact hDb
    have hInv : (2*B₀)⁻¹ = B₀⁻¹/2 := by field_simp
    refine ⟨?_,⟨?_,?_⟩,?_,?_,?_,?_⟩
    · rw [hInv]
      exact ⟨hLam,hNu,hgap⟩
    · exact (hsize p hp).1.trans (by linarith only [hB])
    · exact norm_le_double_of_difference ((hder p hp).1.trans (min_le_left B₀ q)) hL
    · exact norm_le_double_of_difference hVa (hOldB.2.2.2.2 Old.a (by simp)).1
    · exact norm_le_double_of_difference hVb (hOldB.2.2.2.2 Old.b (by simp)).1
    · exact norm_le_double_of_difference hDa' (hOldB.2.2.2.2 Old.a (by simp)).2
    · exact norm_le_double_of_difference hDb' (hOldB.2.2.2.2 Old.b (by simp)).2
  have hNewBound : C1BoundOn New R (2*B₀) :=
    c1BoundOn_of_state_and_normalized_bounds hSol hU
      (fun p hp => (hpoint p hp).1) (fun p hp => (hpoint p hp).2.1)
      (fun p hp => (hpoint p hp).2.2)
  exact ⟨F,hFc,hFC,hSol,hNewBound,hlower,hYi,hXb,fun u hu => (hseam u hu).2⟩

end EmcsfAcExtension.Local
