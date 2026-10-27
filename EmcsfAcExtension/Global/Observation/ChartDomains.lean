module

public import EmcsfAcExtension.Global.Observation.ChartRegularity
public import EmcsfAcExtension.Global.Observation.Domains
import EmcsfAcExtension.Global.Calculus.Endpoint

/-! # Compactness and completeness of the actual normalized comparison set

The domain is the literal inverse image of the original development.
Positive-radius sideways truncations are compact, and every required
characteristic dependence triangle stays in the same radius truncation.
Source: charged_SF_new_version.tex:L2741–2755; approved internal project record (D1)–(D3).
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
Positive-radius sideways truncations of the actual source chart are
compact. Properness of the final original incoming label is explicit;
no closure through the missing endpoint is used. There are no constants. -/
theorem isCompact_actual_chart_truncation {e ui s a b ρ L : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (hs : 0 < s)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 1 χ) (U V : ℝ → ℝ)
    (hU : ContDiff ℝ 1 U) (hV : ContDiff ℝ 1 V)
    (hUm : Monotone U) (hVm : Monotone V)
    (hi : ui ≤ s * U a) (hu : s * U b < 0) (hv : s * V b ≤ 0) :
    let P := nullPullback (rescaleFields (gaugeFields e S χ) s) U V
    let D := {p : ℝ × ℝ | (s * U p.1, s * V p.2) ∈ origDomain ui}
    IsCompact (sidewaysTruncation P D a b ρ L) := by
  let P := nullPullback (rescaleFields (gaugeFields e S χ) s) U V
  let D := {p : ℝ × ℝ | (s * U p.1, s * V p.2) ∈ origDomain ui}
  let K := sidewaysTriangle a b ∩ {p : ℝ × ℝ | s * U p.1 ≤ s * V p.2}
  have hK : IsCompact K := (isCompact_sidewaysTriangle a b).inter_right
    (isClosed_le (continuous_const.mul (hU.continuous.comp continuous_fst))
      (continuous_const.mul (hV.continuous.comp continuous_snd)))
  have hsource (p) (hp : p ∈ K) : (s * U p.1, s * V p.2) ∈ origDomain ui :=
    ⟨hi.trans (mul_le_mul_of_nonneg_left (hUm (hp.1.1.trans hp.1.2.1)) hs.le),
      (mul_le_mul_of_nonneg_left (hUm hp.1.2.2) hs.le).trans_lt hu, hp.2,
      (mul_le_mul_of_nonneg_left (hVm (hp.1.2.1.trans hp.1.2.2)) hs.le).trans hv⟩
  have cr := (chart_fields_continuousOn hS χ hχ U V hU hV K hsource).1
  have hc := cr.preimage_isClosed_of_isClosed hK.isClosed (isClosed_Icc (a := ρ) (b := L))
  have heq : sidewaysTruncation P D a b ρ L = K ∩ (Function.uncurry P.r) ⁻¹' Icc ρ L := by
    ext p
    constructor
    · intro hp
      exact ⟨⟨hp.1.2, hp.1.1.2.2.1⟩, hp.2⟩
    · intro hp
      exact ⟨⟨hsource p hp.1, hp.1.1⟩, hp.2⟩
  change IsCompact (sidewaysTruncation P D a b ρ L)
  rw [heq]
  exact hK.of_isClosed_subset hc inter_subset_left

/-- [internal]
Complete dependence triangles in the actual normalized chart preserve
both radial cutoffs. Original-domain completeness and radius monotonicity
are derived directly from the original integral equations. All outward
Maxwell segments and both scalar characteristic paths therefore use the
same literal truncation. No constants or comparison estimates occur. -/
theorem actual_chart_subtriangles {e ui s a b ρ L : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (hs : 0 < s) (hρ : 0 < ρ)
    (χ : ℝ → ℝ) (U V : ℝ → ℝ) (hUm : Monotone U) (hVm : Monotone V)
    (hi : ui ≤ s * U a) (hv : s * V b ≤ 0)
    (hdiag : ∀ t ∈ Icc a b,
      (nullPullback (rescaleFields (gaugeFields e S χ) s) U V).r t t = L) :
    let P := nullPullback (rescaleFields (gaugeFields e S χ) s) U V
    let D := {p : ℝ × ℝ | (s * U p.1, s * V p.2) ∈ origDomain ui}
    ∀ p ∈ sidewaysTruncation P D a b ρ L,
      sidewaysTriangle p.2 p.1 ⊆ sidewaysTruncation P D a b ρ L := by
  let P := nullPullback (rescaleFields (gaugeFields e S χ) s) U V
  let D := {p : ℝ × ℝ | (s * U p.1, s * V p.2) ∈ origDomain ui}
  have hF : Monotone (fun t => s * U t) := fun x y hxy =>
    mul_le_mul_of_nonneg_left (hUm hxy) hs.le
  have hG : Monotone (fun t => s * V t) := fun x y hxy =>
    mul_le_mul_of_nonneg_left (hVm hxy) hs.le
  dsimp only
  intro p hp q hq
  have hsub := subtriangle_mem_original_of_normalization (hF.monotoneOn _) (hG.monotoneOn _)
    hi hv hp.1.2 hp.1.1
  have hqorig := hsub q hq
  have hlabels := sidewaysTriangle_subtriangle hp.1.2 hq
  have htip : s * U p.1 < s * V p.2 := by
    have hh : s * U p.1 ≤ s * V p.2 := hp.1.1.2.2.1
    rcases lt_or_eq_of_le hh with hh | hh
    · exact hh
    · have hporig : (s * U p.1, s * V p.2) ∈ origDomain ui := hp.1.1
      have hz := (hS.axis (s * U p.1) (by simpa only [← hh] using hporig)).1
      have hrp := hρ.trans_le hp.2.1
      change 0 < S.r (s * U p.1) (s * V p.2) / s at hrp
      rw [← hh, hz, zero_div] at hrp
      exact False.elim (lt_irrefl _ hrp)
  have hqin : s * U q.1 ≤ s * U p.1 := hF hq.2.2
  have hqout : s * V p.2 ≤ s * V q.2 := hG hq.1
  have hproper : s * U q.1 < s * V p.2 := hqin.trans_lt htip
  have hinseg : inSeg (s * U q.1) (s * U p.1) (s * V p.2) ⊆ origDomain ui := by
    rintro ⟨x, y⟩ ⟨h1, h2, rfl⟩
    exact ⟨hqorig.1.trans h1, h2.trans_lt hp.1.1.2.1,
      h2.trans htip.le, hp.1.1.2.2.2⟩
  have houtseg : outSeg (s * U q.1) (s * V p.2) (s * V q.2) ⊆ origDomain ui := by
    rintro ⟨x, y⟩ ⟨rfl, h1, h2⟩
    exact ⟨hqorig.1, hqorig.2.1, hproper.le.trans h1, h2.trans hqorig.2.2.2⟩
  have ein := (hS.eq_in _ _ _ hqin htip hinseg).1
  have eout := (hS.eq_out _ _ _ hproper hqout houtseg).1
  have hinle : S.r (s * U p.1) (s * V p.2) ≤ S.r (s * U q.1) (s * V p.2) := by
    have hh := intervalIntegral.integral_nonneg (μ := volume)
      (f := fun x => -S.nu x (s * V p.2)) hqin
      (fun x hx => (neg_pos.mpr (hS.nu_neg (x, s * V p.2) (hinseg ⟨hx.1, hx.2, rfl⟩))).le)
    rw [intervalIntegral.integral_neg, ← ein.2] at hh
    linarith only [hh]
  have houtle : S.r (s * U q.1) (s * V p.2) ≤ S.r (s * U q.1) (s * V q.2) := by
    have hh := intervalIntegral.integral_nonneg (μ := volume)
      (f := fun x => S.lam (s * U q.1) x) hqout
      (fun x hx => (hS.lam_pos (s * U q.1, x) (houtseg ⟨rfl, hx.1, hx.2⟩)).le)
    rw [← eout.2] at hh
    exact sub_nonneg.mp hh
  have hrlo : ρ ≤ P.r q.1 q.2 := hp.2.1.trans
    (div_le_div_of_nonneg_right (hinle.trans houtle) hs.le)
  have hqt : q.1 ∈ Icc a b := ⟨hlabels.1.trans hlabels.2.1, hlabels.2.2⟩
  have hdiagorig : (s * U q.1, s * V q.1) ∈ origDomain ui := by
    have hq1 : q.1 ∈ Icc p.2 p.1 := ⟨hq.1.trans hq.2.1, hq.2.2⟩
    exact hsub (q.1, q.1) ⟨hq1.1, le_rfl, hq1.2⟩
  have hupper : s * V q.2 ≤ s * V q.1 := hG hq.2.1
  have hfullout : outSeg (s * U q.1) (s * V q.2) (s * V q.1) ⊆ origDomain ui := by
    rintro ⟨x, y⟩ ⟨rfl, h1, h2⟩
    exact ⟨hqorig.1, hqorig.2.1, hqorig.2.2.1.trans h1, h2.trans hdiagorig.2.2.2⟩
  have he := (hS.eq_out _ _ _ (hproper.trans_le hqout) hupper hfullout).1
  have hhi : P.r q.1 q.2 ≤ L := by
    rw [← hdiag q.1 hqt]
    apply div_le_div_of_nonneg_right _ hs.le
    have hh := intervalIntegral.integral_nonneg (μ := volume)
      (f := fun x => S.lam (s * U q.1) x) hupper
      (fun x hx => (hS.lam_pos (s * U q.1, x) (hfullout ⟨rfl, hx.1, hx.2⟩)).le)
    rw [← he.2] at hh
    exact sub_nonneg.mp hh
  exact ⟨⟨hqorig, hlabels⟩, hrlo, hhi⟩

end EmcsfAcExtension.Global.Observation
