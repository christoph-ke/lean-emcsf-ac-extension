module

public import EmcsfAcExtension.Global.Observation.LevelRegularity
public import EmcsfAcExtension.Global.Observation.InnerClock
public import EmcsfAcExtension.Global.Observation.ChartComposition
import Mathlib

/-! # Complete inner comparison geometry in the original development

The level curve, clock, inner chart and all positive-radius test points
are constructed from the source solution and its optical bounds. Every
dependence triangle stays in the same literal radius truncation.
Source: charged_SF_new_version.tex:L2741–2755; approved internal project record (D1)–(D4).
-/

public section

open Set

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
Construct the entire inner comparison window, including actual points
at every requested stopped radius, from optical bounds on the actual
outer chart. The original solution supplies the level graph, its C¹
regularity and its clock; no level curve or comparison record is assumed.
All label and travel margins and the constants `rStar,Lzero,c,B,K` are
fixed before the solution. The source optical export supplies `hopt`.
No incoming supremum, chart solution class or extra gauge is used. -/
theorem inner_window_of_actual_chart_optics
    {e ui s a b rStar Lzero L c B K : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (hs : 0 < s)
    (hrStar : 0 < rStar) (hLzero : rStar ≤ Lzero) (hL : Lzero ≤ L)
    (hc : 0 < c) (hB : 0 < B) (hK : 0 < K)
    (hclock : K ≤ 2 * c * B) (htravel : Lzero / c ≤ K)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 1 χ) (F G : ℝ ≃o ℝ)
    (hF : ContDiff ℝ 1 (F : ℝ → ℝ)) (hG : ContDiff ℝ 1 (G : ℝ → ℝ))
    (hFp : ∀ x, 0 < deriv (F : ℝ → ℝ) x)
    (hGp : ∀ x, 0 < deriv (G : ℝ → ℝ) x)
    (hi : ui < s * F a) (hu : s * F b < 0) (hv : s * G b < 0)
    (hleft : a ≤ -B) (hright : B ≤ b) (hbudget : L / c ≤ b - B)
    (hdiagmem : ∀ t ∈ Icc a b, (s * F t, s * G t) ∈ origDomain ui)
    (hdiag : ∀ t ∈ Icc a b,
      (nullPullback (rescaleFields (gaugeFields e S χ) s) F G).r t t = L)
    (hopt : ∀ p ∈ sidewaysTruncation
      (nullPullback (rescaleFields (gaugeFields e S χ) s) F G)
      {p : ℝ × ℝ | (s * F p.1, s * G p.2) ∈ origDomain ui} a b rStar L,
      -(nullPullback (rescaleFields (gaugeFields e S χ) s) F G).nu p.1 p.2 ∈ Icc c (1 / 2) ∧
        (nullPullback (rescaleFields (gaugeFields e S χ) s) F G).lam p.1 p.2 ∈ Icc c (1 / 2)) :
    let P := nullPullback (rescaleFields (gaugeFields e S χ) s) F G
    let D := {p : ℝ × ℝ | (s * F p.1, s * G p.2) ∈ origDomain ui}
    ∃ U V : ℝ ≃o ℝ,
      ContDiff ℝ 1 (U : ℝ → ℝ) ∧ ContDiff ℝ 1 (V : ℝ → ℝ) ∧
      ContDiff ℝ 1 (U.symm : ℝ → ℝ) ∧ ContDiff ℝ 1 (V.symm : ℝ → ℝ) ∧
      (∀ x, 0 < deriv (U : ℝ → ℝ) x) ∧ (∀ x, 0 < deriv (V : ℝ → ℝ) x) ∧
      (∀ t ∈ Icc (-K) K,
        (U t, V t) ∈ sidewaysTruncation P D a b Lzero L ∧ P.r (U t) (V t) = Lzero ∧
        deriv (U : ℝ → ℝ) t ∈ Icc 1 (1 / (2 * c)) ∧
        deriv (V : ℝ → ℝ) t ∈ Icc 1 (1 / (2 * c)) ∧
        (nullPullback P U V).nu t t = -1 / 2 ∧
        (nullPullback P U V).lam t t = 1 / 2 ∧
        (nullPullback P U V).A t t = P.A (U t) (V t) / (-2 * P.nu (U t) (V t))) ∧
      let Q := nullPullback P U V
      let E := {p : ℝ × ℝ | (U p.1, V p.2) ∈ D}
      (∀ ρ ∈ Icc rStar Lzero,
        ∀ p ∈ sidewaysTruncation Q E (-K) K ρ Lzero,
          (U p.1, V p.2) ∈ sidewaysTruncation P D a b rStar L ∧
          c ≤ -Q.nu p.1 p.2 ∧ c ≤ Q.lam p.1 p.2) ∧
      ∀ ρ ∈ Icc rStar Lzero, ∃ u ∈ Icc 0 K,
        (u, 0) ∈ sidewaysTruncation Q E (-K) K ρ Lzero ∧ Q.r u 0 = ρ ∧
        u ≤ (Lzero - ρ) / c ∧
        sidewaysTriangle 0 u ⊆ sidewaysTruncation Q E (-K) K ρ Lzero := by
  let P := nullPullback (rescaleFields (gaugeFields e S χ) s) F G
  let D := {p : ℝ × ℝ | (s * F p.1, s * G p.2) ∈ origDomain ui}
  have hLzeroPos : 0 < Lzero := hrStar.trans_le hLzero
  have hBB : -B ≤ B := by linarith only [hB]
  have hKK : -K ≤ K := by linarith only [hK]
  have hsub := sidewaysTruncation_mono_radius P D a b L hLzero
  obtain ⟨g, hgc, hlevel⟩ := actual_chart_level_segment_of_optical_bound hS hs χ hχ F G
    hF hG hFp hi.le hu hv hleft hright hBB hc hLzeroPos hL hdiagmem hdiag hbudget
    (fun p hp => (hopt p (hsub hp)).1.1)
  have hlevelmem (v) (hv' : v ∈ Icc (-B) B) :
      (g v, v) ∈ sidewaysTruncation P D a b Lzero L := (hlevel v hv').2.1
  have hlevelr (v) (hv' : v ∈ Icc (-B) B) : P.r (g v) v = Lzero := (hlevel v hv').2.2.1
  have hgreg := actual_chart_level_regular_of_continuous_segment hS hs hLzeroPos χ F G
    hF hG hFp hGp hi hv g hgc.continuousOn hlevelmem hlevelr
  have hfields := chart_fields_continuousOn hS χ hχ F G hF hG
    (sidewaysTruncation P D a b Lzero L) (fun _ hp => hp.1.1)
  have hpair : ContinuousOn (fun v => (g v, v)) (Icc (-B) B) :=
    hgc.continuousOn.prodMk continuousOn_id
  have cn := hfields.2.1.comp hpair hlevelmem
  have cl := hfields.2.2.1.comp hpair hlevelmem
  obtain ⟨clock, U, V, _cclock, _cclocki, _clock0, _dclock,
      hU, hV, hUi, hVi, hUp, hVp, hinner⟩ :=
    inner_maps_of_reserved_level_segment P hB hK hc hclock hgc.continuousOn cn cl
      (fun v hv' => hopt (g v, v) (hsub (hlevelmem v hv'))) hlevelr hgreg.2.1
  have hboundary (t) (ht : t ∈ Icc (-K) K) :
      (U t, V t) ∈ sidewaysTruncation P D a b Lzero L ∧ P.r (U t) (V t) = Lzero := by
    have hh := hinner t ht
    rw [hh.2.1, hh.2.2.1]
    exact ⟨hlevelmem _ hh.1, hlevelr _ hh.1⟩
  let Q := nullPullback P U V
  let E := {p : ℝ × ℝ | (U p.1, V p.2) ∈ D}
  let Fnew := U.trans F
  let Gnew := V.trans G
  have hcompose : Q = nullPullback (rescaleFields (gaugeFields e S χ) s) Fnew Gnew :=
    nullPullback_comp_of_c1_maps _ F G U V hF hG hU hV
  have hFnew : ContDiff ℝ 1 (Fnew : ℝ → ℝ) := hF.comp hU
  have hGnew : ContDiff ℝ 1 (Gnew : ℝ → ℝ) := hG.comp hV
  have hFnewp (x) : 0 < deriv (Fnew : ℝ → ℝ) x := by
    rw [show (Fnew : ℝ → ℝ) = (F : ℝ → ℝ) ∘ U from rfl,
      (((hF.differentiable (by norm_num) (U x)).hasDerivAt).comp x
        (hU.differentiable (by norm_num) x).hasDerivAt).deriv]
    exact mul_pos (hFp _) (hUp _)
  have hinnerDomain : E = {p : ℝ × ℝ | (s * Fnew p.1, s * Gnew p.2) ∈ origDomain ui} := rfl
  have hlow : ui ≤ s * Fnew (-K) := (hboundary (-K) (left_mem_Icc.mpr hKK)).1.1.1.1
  have hfinalU : s * Fnew K < 0 := (hboundary K (right_mem_Icc.mpr hKK)).1.1.1.2.1
  have hfinalV : s * Gnew K < 0 := by
    have hbound := (hboundary K (right_mem_Icc.mpr hKK)).1.1.2
    exact (mul_le_mul_of_nonneg_left (G.monotone (hbound.2.1.trans hbound.2.2)) hs.le).trans_lt hv
  have himage (ρ) (hρ : ρ ∈ Icc rStar Lzero) (p)
      (hp : p ∈ sidewaysTruncation Q E (-K) K ρ Lzero) :
      (U p.1, V p.2) ∈ sidewaysTruncation P D a b rStar L := by
    have hpu : p.1 ∈ Icc (-K) K := ⟨hp.1.2.1.trans hp.1.2.2.1, hp.1.2.2.2⟩
    have hpv : p.2 ∈ Icc (-K) K := ⟨hp.1.2.1, hp.1.2.2.1.trans hp.1.2.2.2⟩
    have hbU := (hboundary p.1 hpu).1
    have hbV := (hboundary p.2 hpv).1
    have hrad : P.r (U p.1) (V p.2) ∈ Icc rStar L :=
      ⟨hρ.1.trans hp.2.1, hp.2.2.trans hL⟩
    refine ⟨⟨hp.1.1, hbV.1.2.1, ?_, hbU.1.2.2.2⟩, hrad⟩
    exact hbV.1.2.2.1.trans (U.monotone hp.1.2.2.1)
  have hinnerOpt (ρ) (hρ : ρ ∈ Icc rStar Lzero) (p)
      (hp : p ∈ sidewaysTruncation Q E (-K) K ρ Lzero) :
      c ≤ -Q.nu p.1 p.2 ∧ c ≤ Q.lam p.1 p.2 := by
    have ho := hopt _ (himage ρ hρ p hp)
    have hpu : p.1 ∈ Icc (-K) K := ⟨hp.1.2.1.trans hp.1.2.2.1, hp.1.2.2.2⟩
    have hpv : p.2 ∈ Icc (-K) K := ⟨hp.1.2.1, hp.1.2.2.1.trans hp.1.2.2.2⟩
    have hdu := (hinner p.1 hpu).2.2.2.2.1.1
    have hdv := (hinner p.2 hpv).2.2.2.2.2.1.1
    constructor
    · change c ≤ -(deriv (U : ℝ → ℝ) p.1 * P.nu (U p.1) (V p.2))
      have hh := mul_le_mul_of_nonneg_right hdu (hc.trans_le ho.1.1).le
      linarith only [hh, ho.1.1]
    · change c ≤ deriv (V : ℝ → ℝ) p.2 * P.lam (U p.1) (V p.2)
      exact ho.2.1.trans (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hdv (hc.trans_le ho.2.1).le)
  refine ⟨U, V, hU, hV, hUi, hVi, hUp, hVp, ?_, ?_, ?_⟩
  · intro t ht
    have hn := hinner t ht
    exact ⟨(hboundary t ht).1, (hboundary t ht).2,
      hn.2.2.2.2.1, hn.2.2.2.2.2.1,
      hn.2.2.2.2.2.2.1, hn.2.2.2.2.2.2.2.1, hn.2.2.2.2.2.2.2.2⟩
  · intro ρ hρ p hp
    exact ⟨himage ρ hρ p hp, hinnerOpt ρ hρ p hp⟩
  · intro ρ hρ
    have hρpos := hrStar.trans_le hρ.1
    have hdiagNew (t) (ht : t ∈ Icc (-K) K) :
        (nullPullback (rescaleFields (gaugeFields e S χ) s) Fnew Gnew).r t t = Lzero := by
      rw [← hcompose]
      exact (hboundary t ht).2
    have hzmem : (s * Fnew 0, s * Gnew 0) ∈ origDomain ui :=
      (hboundary 0 ⟨by linarith only [hK], hK.le⟩).1.1.1
    obtain ⟨u, hu', hpoint, hru, htravel', _⟩ :=
      actual_chart_incoming_radius_hit_of_optical_bound hS hs χ Fnew Gnew hFnew hFnewp
        hlow hfinalU hfinalV (by linarith only [hK]) hK.le hc hρpos hρ.2
        hzmem (hdiagNew 0 ⟨by linarith only [hK], hK.le⟩)
        (by simpa only [sub_zero] using htravel)
        (by
          intro p hp
          have hp' : p ∈ sidewaysTruncation Q E (-K) K ρ Lzero := by
            simpa only [hcompose, hinnerDomain] using hp
          simpa only [hcompose] using (hinnerOpt ρ hρ p hp').1)
    have hpoint' : (u, 0) ∈ sidewaysTruncation Q E (-K) K ρ Lzero := by
      simpa only [hcompose, hinnerDomain] using hpoint
    refine ⟨u, hu', hpoint', ?_, ?_, ?_⟩
    · change Q.r u 0 = ρ
      rw [hcompose]
      exact hru
    · simpa only [sub_zero] using htravel'
    · have htri := actual_chart_subtriangles hS hs hρpos χ Fnew Gnew
        Fnew.monotone Gnew.monotone hlow hfinalV.le hdiagNew (u, 0) hpoint
      change sidewaysTriangle 0 u ⊆ sidewaysTruncation Q E (-K) K ρ Lzero
      rw [hcompose, hinnerDomain]
      exact htri

end EmcsfAcExtension.Global.Observation
