module

public import EmcsfAcExtension.Global.Observation.IncomingTravel
import Mathlib

/-! # A continuous inner level segment in the actual chart

The compact graph argument uses only existing source points. It does not
extend the source fields across the original axis in order to obtain a
rectangular implicit-function problem. Source: charged_SF_new_version.tex:L2741–2755;
approved internal project record (D2)–(D4).
-/

public section

open Set

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
The actual incoming hits form a continuous level segment. Each point
retains its full dependence triangle and stopped travel bound. The
optical bound is needed only at radius at least `ρ`, on the literal
source truncation. Constants and both reserved label intervals precede
the source fields; no incoming field supremum or comparison estimate
is used in the construction. -/
theorem actual_chart_level_segment_of_optical_bound
    {e ui s a b vleft vright c L ρ : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (hs : 0 < s)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 1 χ) (U V : ℝ ≃o ℝ)
    (hU : ContDiff ℝ 1 (U : ℝ → ℝ)) (hV : ContDiff ℝ 1 (V : ℝ → ℝ))
    (hUp : ∀ x, 0 < deriv (U : ℝ → ℝ) x)
    (hi : ui ≤ s * U a) (hu : s * U b < 0) (hv : s * V b < 0)
    (hvl : a ≤ vleft) (hvr : vright ≤ b) (hvv : vleft ≤ vright)
    (hc : 0 < c) (hρ : 0 < ρ) (hρL : ρ ≤ L)
    (hstartmem : ∀ t ∈ Icc a b, (s * U t, s * V t) ∈ origDomain ui)
    (hstart : ∀ t ∈ Icc a b,
      (nullPullback (rescaleFields (gaugeFields e S χ) s) U V).r t t = L)
    (hbudget : L / c ≤ b - vright)
    (hspeed : ∀ p ∈ sidewaysTruncation
      (nullPullback (rescaleFields (gaugeFields e S χ) s) U V)
      {p : ℝ × ℝ | (s * U p.1, s * V p.2) ∈ origDomain ui} a b ρ L,
      c ≤ -(nullPullback (rescaleFields (gaugeFields e S χ) s) U V).nu p.1 p.2) :
    let P := nullPullback (rescaleFields (gaugeFields e S χ) s) U V
    let D := {p : ℝ × ℝ | (s * U p.1, s * V p.2) ∈ origDomain ui}
    ∃ g : ℝ → ℝ, Continuous g ∧ ∀ v ∈ Icc vleft vright,
      g v ∈ Icc v b ∧ (g v, v) ∈ sidewaysTruncation P D a b ρ L ∧
      P.r (g v) v = ρ ∧ g v - v ≤ (L - ρ) / c ∧
      sidewaysTriangle v (g v) ⊆ sidewaysTruncation P D a b ρ L ∧
      ∀ z ∈ Icc v b, (z, v) ∈ D → P.r z v = ρ → z = g v := by
  classical
  let P := nullPullback (rescaleFields (gaugeFields e S χ) s) U V
  let D := {p : ℝ × ℝ | (s * U p.1, s * V p.2) ∈ origDomain ui}
  let R := sidewaysTruncation P D a b ρ L
  have hsub : Icc vleft vright ⊆ Icc a b := Icc_subset_Icc hvl hvr
  have hhit (v : ℝ) (hh : v ∈ Icc vleft vright) :
      ∃ u ∈ Icc v b, (u, v) ∈ R ∧ P.r u v = ρ ∧ u - v ≤ (L - ρ) / c ∧
        ∀ z ∈ Icc v b, (z, v) ∈ D → P.r z v = ρ → z = u :=
    actual_chart_incoming_radius_hit_of_optical_bound hS hs χ U V hU hUp hi hu hv
      (hsub hh).1 (hsub hh).2 hc hρ hρL (hstartmem v (hsub hh)) (hstart v (hsub hh))
      (hbudget.trans (by linarith only [hh.2])) hspeed
  have hR : IsCompact R := isCompact_actual_chart_truncation hS hs χ hχ U V hU hV
    U.monotone V.monotone hi hu hv.le
  have cr : ContinuousOn (Function.uncurry P.r) R :=
    (chart_fields_continuousOn hS χ hχ U V hU hV R (fun _ hp => hp.1.1)).1
  let K := (R ∩ (Function.uncurry P.r) ⁻¹' {ρ}) ∩ Prod.snd ⁻¹' Icc vleft vright
  have hK : IsCompact K :=
    (hR.of_isClosed_subset
      (cr.preimage_isClosed_of_isClosed hR.isClosed isClosed_singleton)
      inter_subset_left).inter_right (isClosed_Icc.preimage continuous_snd)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let projection : K → Icc vleft vright := fun p => ⟨p.val.2, p.property.2⟩
  have hpc : Continuous projection := by
    exact (continuous_snd.comp continuous_subtype_val).subtype_mk _
  have hbij : Function.Bijective projection := by
    constructor
    · intro x y heq
      have hyx : y.val.2 = x.val.2 := (congrArg Subtype.val heq).symm
      obtain ⟨u, _hu, _hmem, _hroot, _htravel, huniq⟩ := hhit x.val.2 x.property.2
      have hxu : x.val.1 = u := huniq x.val.1
        ⟨x.property.1.1.1.2.2.1, x.property.1.1.1.2.2.2⟩
        x.property.1.1.1.1 x.property.1.2
      have hyD : (y.val.1, y.val.2) ∈ D := y.property.1.1.1.1
      have hyr : P.r y.val.1 y.val.2 = ρ := y.property.1.2
      have hyu : y.val.1 = u := huniq y.val.1
        (by simpa only [hyx] using
          (show y.val.1 ∈ Icc y.val.2 b from
            ⟨y.property.1.1.1.2.2.1, y.property.1.1.1.2.2.2⟩))
        (by simpa only [hyx] using hyD)
        (by simpa only [hyx] using hyr)
      exact Subtype.ext (Prod.ext (hxu.trans hyu.symm) hyx.symm)
    · intro v
      obtain ⟨u, _hu, hmem, hroot, _⟩ := hhit v v.property
      exact ⟨⟨(u, v), ⟨⟨hmem, hroot⟩, v.property⟩⟩, rfl⟩
  let homeo : K ≃ₜ Icc vleft vright :=
    (Equiv.ofBijective projection hbij).toHomeomorphOfContinuousClosed hpc hpc.isClosedMap
  let g := IccExtend hvv (fun v => (homeo.symm v).val.1)
  have hgc : Continuous g :=
    (continuous_fst.comp (continuous_subtype_val.comp homeo.symm.continuous)).Icc_extend'
  refine ⟨g, hgc, ?_⟩
  intro v hh
  let point := homeo.symm ⟨v, hh⟩
  have hgv : g v = point.val.1 := IccExtend_of_mem hvv _ hh
  have hpv : point.val.2 = v := congrArg Subtype.val (homeo.apply_symm_apply ⟨v, hh⟩)
  have hmem : (g v, v) ∈ R := by
    rw [hgv, ← hpv]
    exact point.property.1.1
  have hroot : P.r (g v) v = ρ := by
    rw [hgv, ← hpv]
    exact point.property.1.2
  have hgb : g v ∈ Icc v b := ⟨hmem.1.2.2.1, hmem.1.2.2.2⟩
  obtain ⟨u, hu, _huR, hru, htravel, huniq⟩ := hhit v hh
  have heq : g v = u := huniq _ hgb hmem.1.1 hroot
  refine ⟨hgb, hmem, hroot, by simpa only [heq] using htravel, ?_, ?_⟩
  · exact actual_chart_subtriangles hS hs hρ χ U V U.monotone V.monotone hi hv.le
      hstart (g v, v) hmem
  · intro z hz hzm hzr
    exact (huniq z hz hzm hzr).trans heq.symm

end EmcsfAcExtension.Global.Observation
