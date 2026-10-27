module

public import EmcsfAcExtension.Global.Observation.ActualWindow
public import EmcsfAcExtension.Global.Observation.NormalizedMaps
public import EmcsfAcExtension.Global.Observation.ChartBox
import EmcsfAcExtension.Global.Observation.Gauge
import Mathlib

/-! # The comparison window from the original observation data

The comparison labels occupy a strictly smaller clock interval inside
the source cylinder. The gauge, both charts, the inner clock and all
stopped-radius test points are constructed internally.
Source: charged_SF_new_version.tex:L2741–2755; approved internal project record (D1)–(D4).
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global.Observation

/-- [node prop:charged-observation#comparison-window]
Construct the complete characteristic comparison window from an original
observation setting and failure of its boundary inequality. The optical
bounds, stopped travel, level curve, inner clock and both inner null
maps are derived internally. Every selected positive radius has an
actual test point and its full dependence triangle. The constants
`c,K,T,ηc,C` depend only on `δ,rStar,Lzero`; the failure coefficient is
selected after `ε`, before all physical data. The two radii are fixed
reference-family parameters, never chosen from the physical solution.
There is no comparison record, optical estimate or new gauge premise. -/
theorem comparison_window {δ rStar Lzero : ℝ}
    (hδ : 0 < δ) (hrStar : 0 < rStar) (hLzero : rStar ≤ Lzero) :
    ∃ c K T ηc C : ℝ, 0 < c ∧ 0 < K ∧ 0 < T ∧ 0 < ηc ∧ 0 < C ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / C → ∃ Cobs : ℝ, 0 < Cobs ∧
    ∀ (ui e b s τ₀ : ℝ) (S : Fields) (_h : OriginalData ui e S)
      (γ : ClockCylinder S (origDomain ui) b (τ₀ - T * b / 2) (τ₀ + T * b / 2)),
    0 < b → 0 < s → s ≤ b → Lzero ≤ b / s →
    S.m (γ.U τ₀) (γ.V τ₀) + b *
      ‖S.theta (γ.U τ₀) (γ.V τ₀) / S.lam (γ.U τ₀) (γ.V τ₀)‖ ≤ s →
    (∀ p ∈ triangle (γ.U (τ₀ - T * b / 2)) (γ.V (τ₀ + T * b / 2)),
      δ ≤ 1 - S.mu p.1 p.2) →
    |e| * b * (1 + ‖S.a (γ.U τ₀) (γ.V τ₀)‖) ≤ ηc →
    (¬ ENNReal.ofReal (b * (‖S.theta (γ.U τ₀) (γ.V τ₀) /
      S.lam (γ.U τ₀) (γ.V τ₀)‖ ^ 2 + S.mu (γ.U τ₀) (γ.V τ₀) ^ 2)) ≤
      ENNReal.ofReal Cobs * (ENNReal.ofReal (cylinderDissipation S γ.U γ.V
        (τ₀ - T * b / 2) (τ₀ + T * b / 2)) + ENNReal.ofReal b *
        (curveCovVar e S S.a γ.U γ.V (τ₀ - T * b / 2) (τ₀ + T * b / 2)) ^ 2)) →
    ∃ χ : ℝ → ℝ, ContDiff ℝ 1 χ ∧ χ (γ.U (τ₀ - T * b / 2)) = 0 ∧
      (∀ τ ∈ Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2),
        HasDerivAt χ (S.A (γ.U τ) (γ.V τ)) (γ.U τ)) ∧
    ∃ F G U V : ℝ ≃o ℝ,
      ContDiff ℝ 1 (F : ℝ → ℝ) ∧ ContDiff ℝ 1 (G : ℝ → ℝ) ∧
      ContDiff ℝ 1 (F.symm : ℝ → ℝ) ∧ ContDiff ℝ 1 (G.symm : ℝ → ℝ) ∧
      (∀ x, 0 < deriv (F : ℝ → ℝ) x) ∧ (∀ x, 0 < deriv (G : ℝ → ℝ) x) ∧
      ContDiff ℝ 1 (U : ℝ → ℝ) ∧ ContDiff ℝ 1 (V : ℝ → ℝ) ∧
      ContDiff ℝ 1 (U.symm : ℝ → ℝ) ∧ ContDiff ℝ 1 (V.symm : ℝ → ℝ) ∧
      (∀ x, 0 < deriv (U : ℝ → ℝ) x) ∧ (∀ x, 0 < deriv (V : ℝ → ℝ) x) ∧
      let P := nullPullback (rescaleFields (gaugeFields e S χ) s) F G
      let D := {p : ℝ × ℝ | (s * F p.1, s * G p.2) ∈ origDomain ui}
      let Q := nullPullback P U V
      let E := {p : ℝ × ℝ | (U p.1, V p.2) ∈ D}
      (∀ t ∈ Icc (-T * (b / s)) (T * (b / s)),
        s * F t = γ.U (τ₀ + s * t / 2) ∧ s * G t = γ.V (τ₀ + s * t / 2)) ∧
      (∀ t ∈ Icc (-K) K,
        (U t, V t) ∈ sidewaysTruncation P D (-T * (b / s) / 2) (T * (b / s) / 2) Lzero (b / s) ∧
        P.r (U t) (V t) = Lzero ∧
        deriv (U : ℝ → ℝ) t ∈ Icc 1 (1 / (2 * c)) ∧
        deriv (V : ℝ → ℝ) t ∈ Icc 1 (1 / (2 * c)) ∧
        Q.nu t t = -1 / 2 ∧ Q.lam t t = 1 / 2 ∧
        Q.A t t = P.A (U t) (V t) / (-2 * P.nu (U t) (V t))) ∧
      (∀ ρ ∈ Icc rStar Lzero,
        ∀ p ∈ sidewaysTruncation Q E (-K) K ρ Lzero,
          (U p.1, V p.2) ∈ sidewaysTruncation P D
            (-T * (b / s) / 2) (T * (b / s) / 2) rStar (b / s) ∧
          c ≤ -Q.nu p.1 p.2 ∧ c ≤ Q.lam p.1 p.2) ∧
      ∀ ρ ∈ Icc rStar Lzero, ∃ u ∈ Icc 0 K,
        (u, 0) ∈ sidewaysTruncation Q E (-K) K ρ Lzero ∧ Q.r u 0 = ρ ∧
        u ≤ (Lzero - ρ) / c ∧
        sidewaysTriangle 0 u ⊆ sidewaysTruncation Q E (-K) K ρ Lzero := by
  let c : ℝ := 1 / 2 * Real.exp (-(4 / (δ * rStar)))
  have hc : 0 < c := mul_pos (by norm_num) (Real.exp_pos _)
  have hLzeroPos : 0 < Lzero := hrStar.trans_le hLzero
  let K := Lzero / c + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  obtain ⟨B, hB, T₀, hT₀, hclock, hmargins⟩ := comparison_window_margins hc hLzeroPos hK
  let T := 2 * T₀
  have hT : 0 < T := mul_pos (by norm_num) hT₀
  obtain ⟨ηc, hηc, hbox⟩ := chart_box_of_failed_observation hδ
  obtain ⟨C, hC, hbox⟩ := hbox T hT.le
  refine ⟨c, K, T, ηc, C, hc, hK, hT, hηc, hC, ?_⟩
  intro ε hε hεC
  obtain ⟨Cobs, hCobs, hbox⟩ := hbox ε hε hεC
  refine ⟨Cobs, hCobs, ?_⟩
  intro ui e b s τ₀ S h γ hb hs hsb hL hscale hgap hcharged hfailure
  have hsource : τ₀ - T * b / 2 ≤ τ₀ + T * b / 2 := by
    nlinarith only [mul_pos hT hb]
  obtain ⟨χ, hχ, hχ0, hχd, _⟩ :=
    boundary_clock_equations_of_solution (τ₀ := τ₀) h.solution γ hsource hs hb
  obtain ⟨U₀, V₀, hU₀, hV₀, _hiU₀, _hiV₀, hpU₀, hpV₀, heq, hdU₀, hdV₀⟩ :=
    boundary_c1_maps_of_clock_cylinder h.solution hsource γ
  obtain ⟨F, G, hFval, hGval, hF, hG, hFi, hGi, hFp, hGp⟩ :=
    normalized_clock_orderIsos (τ₀ := τ₀) hs U₀ V₀ hU₀ hV₀ hpU₀ hpV₀
  let L := b / s
  let a := -T₀ * L
  let z := T₀ * L
  let f := fun t : ℝ => τ₀ + s * t / 2
  let P := nullPullback (rescaleFields (gaugeFields e S χ) s) F G
  let D := {p : ℝ × ℝ | (s * F p.1, s * G p.2) ∈ origDomain ui}
  have physF (t) : s * F t = U₀ (f t) := by rw [hFval]; dsimp only [f]; field_simp
  have physG (t) : s * G t = V₀ (f t) := by rw [hGval]; dsimp only [f]; field_simp
  have ha : a = -T * L / 2 := by dsimp only [a, T]; ring
  have hz : z = T * L / 2 := by dsimp only [z, T]; ring
  have hinnerClock : τ₀ - T * b / 2 < τ₀ - T₀ * b / 2 ∧
      τ₀ + T₀ * b / 2 < τ₀ + T * b / 2 := by
    dsimp only [T]
    constructor <;> nlinarith only [mul_pos hT₀ hb]
  have hinnerOrder : τ₀ - T₀ * b / 2 ≤ τ₀ + T₀ * b / 2 := by
    nlinarith only [mul_pos hT₀ hb]
  have hinnerSubset := Icc_subset_Icc hinnerClock.1.le hinnerClock.2.le
  have hnorm (t) (ht : t ∈ Icc a z) : f t ∈ Icc (τ₀ - T₀ * b / 2) (τ₀ + T₀ * b / 2) :=
    normalized_clock_mem hs ht
  have htrace (t) (ht : t ∈ Icc a z) :
      s * F t = γ.U (f t) ∧ s * G t = γ.V (f t) := by
    rw [physF, physG]
    exact heq _ (hinnerSubset (hnorm t ht))
  have hfullTrace (t) (ht : t ∈ Icc (-T * L) (T * L)) :
      s * F t = γ.U (f t) ∧ s * G t = γ.V (f t) := by
    rw [physF, physG]
    exact heq _ (normalized_clock_mem hs ht)
  have hdiagmem (t) (ht : t ∈ Icc a z) : (s * F t, s * G t) ∈ origDomain ui := by
    rw [(htrace t ht).1, (htrace t ht).2]
    exact γ.mem _ (hinnerSubset (hnorm t ht))
  have hdiag (t) (ht : t ∈ Icc a z) : P.r t t = L := by
    change S.r (s * F t) (s * G t) / s = b / s
    rw [(htrace t ht).1, (htrace t ht).2, γ.radius _ (hinnerSubset (hnorm t ht))]
  have haz : a ≤ z := by dsimp only [a, z, L]; nlinarith only [mul_nonneg hT₀.le (div_pos hb hs).le]
  have margins := inner_clock_labels h.solution γ hinnerClock.1 hinnerOrder hinnerClock.2
  have hi : ui < s * F a := by
    rw [(htrace a (left_mem_Icc.mpr haz)).1]
    exact (margins _ (hnorm a (left_mem_Icc.mpr haz))).1
  have hu : s * F z < 0 := (hdiagmem z (right_mem_Icc.mpr haz)).2.1
  have hv : s * G z < 0 := by
    rw [(htrace z (right_mem_Icc.mpr haz)).2]
    exact (margins _ (hnorm z (right_mem_Icc.mpr haz))).2
  have hH : ‖(gaugeFields e S χ).a (γ.U τ₀) (γ.V τ₀)‖ = ‖S.a (γ.U τ₀) (γ.V τ₀)‖ := by
    rw [gauge_normalized_out, norm_mul, norm_gauge_phase, one_mul]
  have hcharged' : |e| * b * (1 + ‖(gaugeFields e S χ).a (γ.U τ₀) (γ.V τ₀)‖) ≤ ηc := by
    rwa [hH]
  have hsourcebox := hbox ui e b s τ₀ S h γ χ hb hs hsb hχ hχd hχ0
    hscale hgap hcharged' hfailure U₀ V₀ heq hdU₀ hdV₀
  have hP : P = nullPullback (rescaleFields (gaugeFields e S χ) s)
      (fun t => U₀ (f t) / s) (fun t => V₀ (f t) / s) := by
    dsimp only [P]
    rw [show (F : ℝ → ℝ) = (fun t => U₀ (f t) / s) from funext hFval,
      show (G : ℝ → ℝ) = (fun t => V₀ (f t) / s) from funext hGval]
  have hD : D = {p : ℝ × ℝ | (U₀ (f p.1), V₀ (f p.2)) ∈ origDomain ui} := by
    ext p
    change (s * F p.1, s * G p.2) ∈ origDomain ui ↔ _
    rw [physF, physG]
    rfl
  have hopt (p) (hp : p ∈ sidewaysTruncation P D a z rStar L) :
      -P.nu p.1 p.2 ∈ Icc c (1 / 2) ∧ P.lam p.1 p.2 ∈ Icc c (1 / 2) := by
    have hTL : 0 ≤ T₀ * L := mul_nonneg hT₀.le (div_pos hb hs).le
    have hbig : p ∈ sidewaysTruncation P D (-T * L) (T * L) rStar L := by
      refine ⟨⟨hp.1.1, ?_, hp.1.2.2.1, ?_⟩, hp.2⟩
      · exact (show -T * L ≤ a by dsimp only [a, T]; nlinarith only [hTL]).trans hp.1.2.1
      · exact hp.1.2.2.2.trans (show z ≤ T * L by dsimp only [z, T]; nlinarith only [hTL])
    rw [hP, hD] at hbig
    have hh := hsourcebox rStar hrStar p hbig
    change (c ≤ -P.nu p.1 p.2 ∧ -P.nu p.1 p.2 ≤ 1 / 2) ∧
      (c ≤ P.lam p.1 p.2 ∧ P.lam p.1 p.2 ≤ 1 / 2)
    rw [hP]
    exact ⟨hh.1, hh.2.1⟩
  have hbBudget := (hmargins L hL B (right_mem_Icc.mpr (by linarith only [hB]))).2
  have hlBudget := (hmargins L hL (-B) (left_mem_Icc.mpr (by linarith only [hB]))).1
  obtain ⟨U, V, hU, hV, hUi, hVi, hUp, hVp, hboundary, himage, hpoints⟩ :=
    inner_window_of_actual_chart_optics h.solution hs hrStar hLzero hL hc hB hK
      hclock (by dsimp only [K]; linarith) χ hχ F G hF hG hFp hGp hi hu hv
      (by dsimp only [a] at *; linarith only [hlBudget, div_nonneg (div_pos hb hs).le hc.le])
      (by dsimp only [z] at *; linarith only [hbBudget, div_nonneg (div_pos hb hs).le hc.le])
      (by dsimp only [z] at *; linarith only [hbBudget]) hdiagmem hdiag hopt
  refine ⟨χ, hχ, hχ0, hχd, F, G, U, V, hF, hG, hFi, hGi, hFp, hGp,
    hU, hV, hUi, hVi, hUp, hVp, ?_⟩
  rw [← ha, ← hz]
  exact ⟨hfullTrace, hboundary, himage, hpoints⟩

end EmcsfAcExtension.Global.Observation
