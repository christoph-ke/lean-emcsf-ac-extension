module

public import EmcsfAcExtension.Local.Construction.StripFields
public import EmcsfAcExtension.Local.Construction.Strip
import EmcsfAcExtension.Local.Construction.StripTube
import EmcsfAcExtension.Local.Construction.StripC0
import EmcsfAcExtension.Local.Construction.StripSources
import EmcsfAcExtension.Local.Construction.StripRegularity
import EmcsfAcExtension.Local.Broad.RectangleLipschitz

/-! # Uniform positive-radius classical strip construction

Continuous Picard existence stays in a fixed geometric tube. The literal
rational source equations then recover joint C¹ and all unused incoming
constraints. The lifespan precedes the old apex and its lower trace.
The uniform first-jet estimate is added in the continuation assembly.
-/

public section

open Set MeasureTheory
open scoped NNReal

namespace EmcsfAcExtension.Local

open Broad

/-- Construct actual full-system C¹ strips uniformly over bounded lower
traces in a fixed positive-radius class. The positive height depends on
`e,ℓ,r₀,B,T,J,r` before the entering datum, apex and lower trace. The
prescribed proximity `r` can be reduced for first-jet comparison. All
literal characteristic equations and exact lower trace are retained.
The old solution is used only to recover the four unused constraints. -/
theorem c1_rectangle_strip_of_lower_trace
    (e ℓ r₀ B T : ℝ) (J : ℝ≥0) (r : ℝ)
    (hℓ : 0 < ℓ) (hr₀ : 0 < r₀) (hT : 0 ≤ T) (hr : 0 < r) :
    ∃ δ₀ > 0,
      ∀ yi : ℝ → RectangleIncoming, LipschitzWith J yi →
        ContDiffOn ℝ 1 yi (Icc 0 T) →
      ∀ S d δ : ℝ, 0 < d → d < S → 0 < δ → δ ≤ δ₀ → S+δ ≤ T →
      ∀ (w : ℝ → RectangleState) (old : Fields) (D : Set (ℝ × ℝ)),
        Continuous w → ContDiffOn ℝ 1 w (Icc 0 d) →
        IsC1Solution e old D → MapsTo (fun u => (u,S)) (Icc 0 d) D →
        (∀ u ∈ Icc 0 d, rectangle_state old (u,S)=w u) →
        (∀ u ∈ Icc 0 d, ‖w u‖ ≤ B ∧ r₀ ≤ (w u).2.1 ∧
          ℓ ≤ (w u).1.1 ∧ ℓ ≤ -(w u).2.2.1 ∧
          ℓ ≤ 1-2*(w u).2.2.2.1/(w u).2.1) →
        (∀ u ∈ Icc 0 d, (w u).1=yi S+∫ s in 0..u, rectangle_in_source e (w s)) →
        ∃ F : ℝ × ℝ → RectangleState,
          Continuous F ∧ ContDiffOn ℝ 1 F (Icc 0 d ×ˢ Icc S (S+δ)) ∧
          IsC1Solution e (rectangle_fields F) (Icc 0 d ×ˢ Icc S (S+δ)) ∧
          (∀ u ∈ Icc 0 d, ∀ v ∈ Icc S (S+δ),
            (F (u,v)).1=yi v+∫ s in 0..u, rectangle_in_source e (F (s,v))) ∧
          (∀ u ∈ Icc 0 d, ∀ v ∈ Icc S (S+δ),
            (F (u,v)).2=(w u).2+∫ t in S..v, rectangle_out_source e (F (u,t))) ∧
          (∀ u ∈ Icc 0 d, F (u,S)=w u) ∧
          (∀ u ∈ Icc 0 d, ∀ v ∈ Icc S (S+δ), ‖F (u,v)-w u‖ ≤ r) := by
  obtain ⟨τ, hτ, htube⟩ := continuation_state_tube ℓ r₀ hℓ hr₀
  let ρ := min (r₀/2) (min (ℓ/2) (ℓ*r₀/2))
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  obtain ⟨H, _L₀, hH, _hL₀, hsize, _hLi, _hLo⟩ :=
    continuation_source_bounds e ρ (B+1) hρ
  obtain ⟨L, fi, fo, _hL, hfi, hfo, heqi, heqo⟩ :=
    continuation_sources_global_extensions e ρ (B+1) hρ
  obtain ⟨δ₀, hδ₀, hstrip⟩ := continuous_rectangle_strip (I := RectangleIncoming) (O :=
      RectangleOutgoing)
    L J H T (min τ r)
    hH.le hT (lt_min hτ hr)
  refine ⟨δ₀, hδ₀, ?_⟩
  intro yi hyi hyic S d δ hd hdS hδ hδsmall hcap w old D hw hwc hold hside hmatch
    hbounds hin
  have hS : 0 < S := hd.trans hdS
  have hdT : d ∈ Icc 0 T := ⟨hd.le, hdS.le.trans (by linarith)⟩
  have holdBox u (hu : u ∈ Icc 0 d) : w u ∈ continuationStateBox ρ (B+1) := by
    obtain ⟨hn, hr, hl, hnu, hgap⟩ := hbounds u hu
    exact (htube B (w u) (w u) hn hr hl hnu hgap (by simpa using hτ.le)).1
  have hin' : ∀ u ∈ Icc 0 d, (w u).1=yi S+∫ s in 0..u, fi (w s) := by
    intro u hu
    rw [hin u hu]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hu.1] at hs
    exact heqi (holdBox s ⟨hs.1, hs.2.trans hu.2⟩)
  have hout : ∀ u ∈ Icc 0 d, ‖fo (w u)‖ ≤ H := by
    intro u hu
    rw [← heqo (holdBox u hu)]
    exact (hsize (w u) (holdBox u hu)).2
  obtain ⟨F, hF, hFi, hFo, hlower, hnear⟩ := hstrip fi fo hfi hfo S d δ hdT hδ hδsmall
    w yi hw hyi hin' hout
  have htubeF u (hu : u ∈ Icc 0 d) v (hv : v ∈ Icc S (S+δ)) :=
    htube B (w u) (F (u,v)) (hbounds u hu).1 (hbounds u hu).2.1
      (hbounds u hu).2.2.1 (hbounds u hu).2.2.2.1 (hbounds u hu).2.2.2.2
      ((hnear u hu v hv).trans (min_le_left _ _))
  have hregion : ∀ p ∈ Icc 0 d ×ˢ Icc S (S+δ), F p ∈ rectangle_state_region :=
    fun p hp => (htubeF p.1 hp.1 p.2 hp.2).2.1
  have hnu : ∀ p ∈ Icc 0 d ×ˢ Icc S (S+δ), (F p).2.2.1 < 0 :=
    fun p hp => (htubeF p.1 hp.1 p.2 hp.2).2.2.1
  have hFi' : ∀ u ∈ Icc 0 d, ∀ v ∈ Icc S (S+δ),
      (F (u,v)).1=yi v+∫ s in 0..u, rectangle_in_source e (F (s,v)) := by
    intro u hu v hv
    rw [hFi u hu v hv]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hu.1] at hs
    exact (heqi (htubeF s ⟨hs.1, hs.2.trans hu.2⟩ v hv).1).symm
  have hFo' : ∀ u ∈ Icc 0 d, ∀ v ∈ Icc S (S+δ),
      (F (u,v)).2=(w u).2+∫ t in S..v, rectangle_out_source e (F (u,t)) := by
    intro u hu v hv
    rw [hFo u hu v hv]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hv.1] at ht
    exact (heqo (htubeF u hu t ⟨ht.1, ht.2.trans hv.2⟩).1).symm
  have hsourcei : ∀ z ∈ rectangle_state_region,
      ContDiffAt ℝ 1 (rectangle_in_source e) z :=
    fun z hz => contDiffAt_rectangle_in_source e hz
  have hsourceo : ∀ z ∈ rectangle_state_region,
      ContDiffAt ℝ 1 (rectangle_out_source e) z :=
    fun z hz => contDiffAt_rectangle_out_source e hz
  have hjoint := contDiffOn_goursat_of_integral_eq hd (by linarith) F hF.continuousOn
    yi (fun u => (w u).2) (rectangle_in_source e) (rectangle_out_source e)
    (hyic.mono (Icc_subset_Icc hS.le hcap)) hwc.snd rectangle_state_region
    isOpen_rectangle_state_region hregion hsourcei hsourceo hFi' hFo'
  have hFoOld : ∀ u ∈ Icc 0 d, ∀ v ∈ Icc S (S+δ),
      (F (u,v)).2=(rectangle_state old (u,S)).2+
        ∫ t in S..v, rectangle_out_source e (F (u,t)) := by
    intro u hu v hv
    rw [hmatch u hu]
    exact hFo' u hu v hv
  have hsol := isC1Solution_rectangle_fields_of_goursat hd (by linarith) hdS hjoint
    hregion hnu hold hside hFi' hFoOld
  exact ⟨F, hF, hjoint, hsol, hFi', hFo', hlower,
    fun u hu v hv => (hnear u hu v hv).trans (min_le_right _ _)⟩

end EmcsfAcExtension.Local
