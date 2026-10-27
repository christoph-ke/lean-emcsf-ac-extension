module

public import EmcsfAcExtension.Local.Construction.Strip
public import EmcsfAcExtension.Local.Construction.StripFields
import EmcsfAcExtension.Local.Construction.StripExistence
import EmcsfAcExtension.Local.Construction.StripUniformJets
import EmcsfAcExtension.Local.Construction.StripTube
import EmcsfAcExtension.Local.Construction.StripData
import EmcsfAcExtension.Local.Construction.TraceExtension
import EmcsfAcExtension.Local.Broad.ScalarAverage
import EmcsfAcExtension.Local.Calculus.C1ToSolution2
import EmcsfAcExtension.Local.Api.Mono
import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # Uniform positive-radius strips from complete old triangles

The state tube, entering trace and geometric separation determine the
height before the old apex and old solution. An old rectangular band
supplies the transverse reference jets. All derivatives on that band
are identified with the old triangle derivatives by unique differentiation.
-/

public section

open Set MeasureTheory
open scoped NNReal

namespace EmcsfAcExtension.Local

open Broad

/-- A classical full system has a C¹ finite characteristic state on the
same domain. This assertion uses only the nine primary regularities. -/
theorem IsC1Solution.contDiffOn_rectangle_state {e : ℝ} {Old : Fields}
    {D : Set (ℝ × ℝ)} (hOld : IsC1Solution e Old D) :
    ContDiffOn ℝ 1 (rectangle_state Old) D := by
  unfold rectangle_state
  simpa only [Function.uncurry_def] using
    (hOld.c1_lam.prodMk hOld.c1_theta).prodMk
      (hOld.c1_r.prodMk (hOld.c1_nu.prodMk (hOld.c1_m.prodMk
        (hOld.c1_Q.prodMk (hOld.c1_A.prodMk (hOld.c1_phi.prodMk hOld.c1_xi))))))

/-- Construct a positive-radius full-system C¹ strip from any complete
old triangle with the fixed bound `B₀`. The lifespan depends only on
`e,T,B₀,ℓ,η,ε,q,J,yi`, before the old apex, upper strip label and old solution.
The fixed state box contains both the old comparison band and new strip.
The value and full-derivative tolerances `ε,q` are fixed before the
old apex and solution. The full derivative differs by at most `q`, and
exact seam matching holds for both old derivative domains.
No second derivative, old-solution modulus, or future-axis datum is used. -/
theorem uniform_c1_strip_from_old_with_proximity
    (e T B₀ ℓ η ε q : ℝ) (J : ℝ≥0) (yi : ℝ → RectangleIncoming)
    (hT : 0 < T) (hB : 0 < B₀) (hℓ : 0 < ℓ) (hη : 0 < η)
    (hε : 0 < ε) (hq : 0 < q)
    (hℓB : ℓ ≤ B₀⁻¹) (hyi : LipschitzWith J yi)
    (hyic : ContDiffOn ℝ 1 yi (Icc 0 T)) :
    let r₀ := 3*ℓ*η/8
    let ρ := min (r₀/2) (min (ℓ/2) (ℓ*r₀/2))
    let K := continuationStateBox ρ (B₀+1)
    ∃ δ₀ > 0, ∀ S b : ℝ, 2*η < S → S < b → b-S ≤ δ₀ → b ≤ T →
      ∀ Old : Fields, IsC1Solution e Old (triangle 0 S) →
        C1BoundOn Old (triangle 0 S) B₀ →
        (∀ v ∈ Icc 0 S, (rectangle_state Old (0,v)).1 = yi v) →
      let d := S-3*η/4
      let l := S-3*η/8
      ∃ F : ℝ × ℝ → RectangleState,
        Continuous F ∧ ContDiffOn ℝ 1 F (Icc 0 d ×ˢ Icc S b) ∧
        IsC1Solution e (rectangle_fields F) (Icc 0 d ×ˢ Icc S b) ∧
        MapsTo F (Icc 0 d ×ˢ Icc S b) K ∧
        MapsTo (rectangle_state Old) (Icc 0 d ×ˢ Icc l S) K ∧
        (∀ u ∈ Icc 0 d, F (u,S) = rectangle_state Old (u,S)) ∧
        (∀ u ∈ Icc 0 d, ∀ v ∈ Icc S b,
          (F (u,v)).1 = yi v + ∫ s in 0..u, rectangle_in_source e (F (s,v))) ∧
        (∀ u ∈ Icc 0 d, ∀ v ∈ Icc S b,
          (F (u,v)).2 = (rectangle_state Old (u,S)).2 +
            ∫ t in S..v, rectangle_out_source e (F (u,t))) ∧
        (∀ u ∈ Icc 0 d, ∀ v ∈ Icc S b, ‖F (u,v)-rectangle_state Old (u,S)‖ ≤ ε) ∧
        (∀ p ∈ Icc 0 d ×ˢ Icc S b,
          ‖fderivWithin ℝ F (Icc 0 d ×ˢ Icc S b) p -
            fderivWithin ℝ (rectangle_state Old) (triangle 0 S) (p.1,S)‖ ≤ q ∧
          ‖fderivWithin ℝ F (Icc 0 d ×ˢ Icc S b) p‖ ≤ 4*B₀) ∧
        (∀ u ∈ Icc 0 d,
          fderivWithin ℝ F (Icc 0 d ×ˢ Icc S b) (u,S) =
            fderivWithin ℝ (rectangle_state Old) (Icc 0 d ×ˢ Icc l S) (u,S) ∧
          fderivWithin ℝ F (Icc 0 d ×ˢ Icc S b) (u,S) =
            fderivWithin ℝ (rectangle_state Old) (triangle 0 S) (u,S)) ∧
        (∀ p ∈ Icc 0 d ×ˢ Icc S b,
          ‖F p‖ ≤ B₀+1 ∧ ℓ/2 ≤ (F p).1.1) := by
  let r₀ := 3*ℓ*η/8
  let ρ := min (r₀/2) (min (ℓ/2) (ℓ*r₀/2))
  let K := continuationStateBox ρ (B₀+1)
  have hr₀ : 0 < r₀ := by dsimp [r₀]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hK : IsCompact K := isCompact_continuationStateBox _ _
  have hconv : Convex ℝ K := convex_continuationStateBox _ _
  have hregion : K ⊆ rectangle_state_region := continuationStateBox_subset_region hρ
  let qeff := min B₀ q
  have hqeff : 0 < qeff := lt_min hB hq
  obtain ⟨ζ,hζ,δjet,hδjet,hjets⟩ :=
    exists_uniform_goursat_jet_bounds e hK hconv hregion hT hB hqeff hyic
  obtain ⟨τ,hτ,htube⟩ := continuation_state_tube ℓ r₀ hℓ hr₀
  let r := min ζ (min 1 (min τ ε))
  have hr : 0 < r := lt_min hζ (lt_min zero_lt_one (lt_min hτ hε))
  obtain ⟨δexist,hδexist,hexist⟩ :=
    c1_rectangle_strip_of_lower_trace e ℓ r₀ B₀ T J r hℓ hr₀ hT.le hr
  refine ⟨min δexist δjet,lt_min hδexist hδjet,?_⟩
  intro S b hηS hSb hheight hbT Old hOld hbound hOldYi
  let d := S-3*η/4
  let l := S-3*η/8
  have hS : 0 < S := by linarith
  have hd : 0 < d := by dsimp [d]; linarith
  have hl : 0 ≤ l := by dsimp [l]; linarith
  have hdl : d < l := by dsimp [d,l]; linarith
  have hlS : l < S := by dsimp [l]; linarith
  have hdS : d < S := hdl.trans hlS
  have hsub : Icc 0 d ×ˢ Icc l S ⊆ triangle 0 S := by
    intro p hp
    exact ⟨hp.1.1,hp.1.2.trans (hdl.le.trans hp.2.1),hp.2.2⟩
  have hside : MapsTo (fun u => (u,S)) (Icc 0 d) (triangle 0 S) :=
    fun u hu => ⟨hu.1,hu.2.trans hdS.le,le_rfl⟩
  have hOldC := hOld.contDiffOn_rectangle_state
  have hWC : ContDiffOn ℝ 1 (rectangle_state Old) (Icc 0 d ×ˢ Icc l S) := hOldC.mono hsub
  have hU : UniqueDiffOn ℝ (Icc 0 d ×ˢ Icc l S) :=
    (uniqueDiffOn_Icc hd).prod (uniqueDiffOn_Icc hlS)
  have hfd p (hp : p ∈ Icc 0 d ×ˢ Icc l S) :
      fderivWithin ℝ (rectangle_state Old) (Icc 0 d ×ˢ Icc l S) p =
        fderivWithin ℝ (rectangle_state Old) (triangle 0 S) p :=
    fderivWithin_subset hsub (hU p hp) (hOldC.differentiableOn (by norm_num) p (hsub hp))
  have hWB p (hp : p ∈ Icc 0 d ×ˢ Icc l S) :
      ‖fderivWithin ℝ (rectangle_state Old) (Icc 0 d ×ˢ Icc l S) p‖ ≤ B₀ := by
    rw [hfd p hp]
    exact norm_fderiv_continuation_state_le hOld (uniqueDiffOn_triangle hS) hbound (hsub hp)
  have hstates p (hp : p ∈ Icc 0 d ×ˢ Icc l S) :
      ‖rectangle_state Old p‖ ≤ B₀ ∧ r₀ ≤ (rectangle_state Old p).2.1 ∧
      ℓ ≤ (rectangle_state Old p).1.1 ∧ ℓ ≤ -(rectangle_state Old p).2.2.1 ∧
      ℓ ≤ 1-2*(rectangle_state Old p).2.2.2.1/(rectangle_state Old p).2.1 := by
    have hpT := hsub hp
    have hrad := outgoing_radius_lower (hOld.toIsSolution hS) hpT.2.1
      (show outSeg p.1 p.1 p.2 ⊆ triangle 0 S from fun q hq =>
        ⟨by simpa only [hq.1] using hpT.1,
          by simpa only [hq.1] using hq.2.1,hq.2.2.trans hpT.2.2⟩)
      (fun v hv => hℓB.trans (hbound (p.1,v) ⟨hpT.1,hv.1,hv.2.trans hpT.2.2⟩).1)
    have hsep : 3*η/8 ≤ p.2-p.1 := by
      have hu := hp.1.2
      have hv := hp.2.1
      dsimp [d,l] at hu hv
      linarith
    have hr : r₀ ≤ Old.r p.1 p.2 :=
      (show r₀ ≤ ℓ*(p.2-p.1) by
        dsimp [r₀]
        calc 3*ℓ*η/8 = ℓ*(3*η/8) := by ring
             _ ≤ ℓ*(p.2-p.1) := mul_le_mul_of_nonneg_left hsep hℓ.le).trans hrad
    refine ⟨norm_continuation_state_le hbound hpT,hr,
      hℓB.trans (hbound p hpT).1,hℓB.trans (hbound p hpT).2.1,?_⟩
    simpa only [rectangle_state,Fields.mu] using hℓB.trans (hbound p hpT).2.2.1
  have hWK : MapsTo (rectangle_state Old) (Icc 0 d ×ˢ Icc l S) K := by
    intro p hp
    obtain ⟨hn,hr,hl,hm,hg⟩ := hstates p hp
    exact (htube B₀ (rectangle_state Old p) (rectangle_state Old p) hn hr hl hm hg
      (by simpa using hτ.le)).1
  let xb₀ := fun u => (rectangle_state Old (u,l)).2
  have hxb₀ : ContDiffOn ℝ 1 xb₀ (Icc 0 d) :=
    hWC.snd.comp (contDiffOn_id.prodMk contDiffOn_const)
      (fun u hu => ⟨hu,le_rfl,hlS.le⟩)
  have hBroad := isSolution_mono (hOld.toIsSolution hS) hsub
  obtain ⟨hYiW,hXbW⟩ := broad_rectangle_goursat_eq hd.le hlS.le hdl hBroad
    (fun v hv => hOldYi v ⟨hl.trans hv.1,hv.2⟩) (fun _ _ => rfl)
  have htrace : ContDiffOn ℝ 1 (fun u => rectangle_state Old (u,S)) (Icc 0 d) :=
    hOldC.comp (contDiffOn_id.prodMk contDiffOn_const) hside
  obtain ⟨w,hw,hwEq⟩ := exists_contDiff_one_extension_Icc hd htrace
  have hwMatch : ∀ u ∈ Icc 0 d, w u = rectangle_state Old (u,S) :=
    fun u hu => hwEq hu
  have hwIn : ∀ u ∈ Icc 0 d,
      (w u).1 = yi S+∫ t in 0..u, rectangle_in_source e (w t) := by
    intro u hu
    rw [hwMatch u hu,hYiW u hu S ⟨hlS.le,le_rfl⟩]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hu.1] at ht
    change rectangle_in_source e (rectangle_state Old (t,S)) = rectangle_in_source e (w t)
    rw [hwMatch t ⟨ht.1,ht.2.trans hu.2⟩]
  have hwBounds u (hu : u ∈ Icc 0 d) := hstates (u,S) ⟨hu,hlS.le,le_rfl⟩
  have hwBounds' : ∀ u ∈ Icc 0 d,
      ‖w u‖ ≤ B₀ ∧ r₀ ≤ (w u).2.1 ∧ ℓ ≤ (w u).1.1 ∧
      ℓ ≤ -(w u).2.2.1 ∧ ℓ ≤ 1-2*(w u).2.2.2.1/(w u).2.1 := by
    intro u hu
    rw [hwMatch u hu]
    exact hwBounds u hu
  obtain ⟨F,hFc,hFC,hSol,hYi,hXb,hLower,hNear⟩ :=
    hexist yi hyi hyic S d (b-S) hd hdS (sub_pos.mpr hSb)
      (hheight.trans (min_le_left _ _)) (by linarith) w Old (triangle 0 S)
      hw.continuous hw.contDiffOn hOld hside (fun u hu => (hwMatch u hu).symm) hwBounds' hwIn
  have heq : S+(b-S) = b := by ring
  rw [heq] at hFC hSol hYi hXb hNear
  have hNearOld u (hu : u ∈ Icc 0 d) v (hv : v ∈ Icc S b) :
      ‖F (u,v)-rectangle_state Old (u,S)‖ ≤ r := by
    rw [← hwMatch u hu]
    exact hNear u hu v hv
  have hFK : MapsTo F (Icc 0 d ×ˢ Icc S b) K := by
    intro p hp
    obtain ⟨hn,hr,hl,hm,hg⟩ := hwBounds p.1 hp.1
    exact (htube B₀ (rectangle_state Old (p.1,S)) (F p) hn hr hl hm hg
      ((hNearOld p.1 hp.1 p.2 hp.2).trans
        ((min_le_right ζ (min 1 (min τ ε))).trans
          ((min_le_right 1 (min τ ε)).trans (min_le_left τ ε))))).1
  have hXbOld : ∀ u ∈ Icc 0 d, ∀ v ∈ Icc S b,
      (F (u,v)).2 = (rectangle_state Old (u,S)).2 +
        ∫ t in S..v, rectangle_out_source e (F (u,t)) := by
    intro u hu v hv
    rw [← hwMatch u hu]
    exact hXb u hu v hv
  have hLowerOld : ∀ u ∈ Icc 0 d, F (u,S) = rectangle_state Old (u,S) :=
    fun u hu => (hLower u hu).trans (hwMatch u hu)
  have hj := hjets hl hlS hSb hbT hd hdS (hheight.trans (min_le_right _ _))
    hWC hFC hWK hFK hxb₀ hYiW hXbW hYi hXbOld hWB
    (fun p hp => (hNearOld p.1 hp.1 p.2 hp.2).trans (min_le_left _ _))
  have hSeam := goursat_seam_fderiv_eq e hK hconv hregion hd hlS hSb hB.le
    (hyic.mono (Icc_subset_Icc hl hbT)) hWC hFC hWK hFK hxb₀
    hYiW hXbW hYi hXbOld hWB hLowerOld
  refine ⟨F,hFc,hFC,hSol,hFK,hWK,hLowerOld,hYi,hXbOld,?_,?_,?_,?_⟩
  · intro u hu v hv
    exact (hNearOld u hu v hv).trans ((min_le_right ζ (min 1 (min τ ε))).trans
      ((min_le_right 1 (min τ ε)).trans (min_le_right τ ε)))
  · intro p hp
    have hcompare := (hj p hp).1
    rw [hfd (p.1,S) ⟨hp.1,hlS.le,le_rfl⟩] at hcompare
    exact ⟨hcompare.trans (min_le_right B₀ q),(hj p hp).2.2.2⟩
  · intro u hu
    exact ⟨hSeam u hu,(hSeam u hu).trans (hfd (u,S) ⟨hu,hlS.le,le_rfl⟩)⟩
  · intro p hp
    obtain ⟨hn,hr,hl,hm,hg⟩ := hwBounds p.1 hp.1
    obtain ⟨_,_,_,_,_,hLam,_,_⟩ :=
      htube B₀ (rectangle_state Old (p.1,S)) (F p) hn hr hl hm hg
        ((hNearOld p.1 hp.1 p.2 hp.2).trans
          ((min_le_right ζ (min 1 (min τ ε))).trans
          ((min_le_right 1 (min τ ε)).trans (min_le_left τ ε))))
    refine ⟨?_,hLam⟩
    simpa only [Metric.mem_closedBall,dist_zero_right] using (hFK hp).1


end EmcsfAcExtension.Local
