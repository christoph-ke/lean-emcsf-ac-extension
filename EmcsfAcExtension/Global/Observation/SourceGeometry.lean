module

public import EmcsfAcExtension.Global.Observation.Calibration
import Mathlib

/-! # Geometry fields of the source outer normalization record

All equations are ordinary on the closed comparison set because the
physical clock labels lie strictly inside the source cylinder window.
Source: charged_SF_new_version.tex:L1980–2034, L2741–2755; internal project record internal project
record.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
Construct the compactness, full dependence triangles, continuous fields,
component equations and normalized boundary geometry of the actual outer
record. All inputs are the original solution and defining calibrated
chart/gauge data, with a strictly smaller comparison window. No geometric
record, optical bound or comparison estimate is assumed. No constants
are selected. -/
theorem source_chart_geometry_of_calibration
    {e ui b s τ₀ T ρ : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (hb : 0 < b) (hs : 0 < s)
    (hT : 0 < T) (hρ : 0 < ρ) (hρL : ρ ≤ b / s)
    (γ : ClockCylinder S (origDomain ui) b (τ₀ - T * b / 2) (τ₀ + T * b / 2))
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 1 χ) (F G : ℝ ≃o ℝ)
    (hF : ContDiff ℝ 1 (F : ℝ → ℝ)) (hG : ContDiff ℝ 1 (G : ℝ → ℝ))
    (hFp : ∀ x, 0 < deriv (F : ℝ → ℝ) x) (hGp : ∀ x, 0 < deriv (G : ℝ → ℝ) x)
    (hcal : ∀ x : ℝ, τ₀ + s * x / 2 ∈ Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2) →
      s * F x = γ.U (τ₀ + s * x / 2) ∧ s * G x = γ.V (τ₀ + s * x / 2))
    (hχd : ∀ τ ∈ Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2),
      HasDerivAt χ (S.A (γ.U τ) (γ.V τ)) (γ.U τ)) :
    let P := nullPullback (rescaleFields (gaugeFields e S χ) s) F G
    let D := {p : ℝ × ℝ | (s * F p.1, s * G p.2) ∈ origDomain ui}
    let a := -T * (b / s) / 2
    let z := T * (b / s) / 2
    let R := sidewaysTruncation P D a z ρ (b / s)
    IsCompact R ∧
      (∀ p ∈ R, sidewaysTriangle p.2 p.1 ⊆ R) ∧
      (ContinuousOn (Function.uncurry P.r) R ∧ ContinuousOn (Function.uncurry P.nu) R ∧
        ContinuousOn (Function.uncurry P.lam) R ∧ ContinuousOn (Function.uncurry P.A) R ∧
        ContinuousOn (Function.uncurry P.phi) R ∧ ContinuousOn (Function.uncurry P.theta) R ∧
        ContinuousOn (Function.uncurry P.m) R ∧ ContinuousOn (Function.uncurry P.Q) R ∧
        ContinuousOn (Function.uncurry P.xi) R) ∧
      (∀ p ∈ R,
        (HasDerivAt (P.r p.1) (P.lam p.1 p.2) p.2 ∧
          HasDerivAt (P.nu p.1) (P.rUV p.1 p.2) p.2 ∧
          HasDerivAt (P.m p.1) (P.mV p.1 p.2) p.2 ∧
          HasDerivAt (P.Q p.1) (P.QV (s * e) p.1 p.2) p.2 ∧
          HasDerivAt (P.A p.1) (P.AV p.1 p.2) p.2 ∧
          HasDerivAt (P.phi p.1) (P.phiV p.1 p.2) p.2 ∧
          HasDerivAt (P.xi p.1) (P.xiV (s * e) p.1 p.2) p.2) ∧
        (HasDerivAt (fun u => P.r u p.2) (P.nu p.1 p.2) p.1 ∧
          HasDerivAt (fun u => P.lam u p.2) (P.rUV p.1 p.2) p.1 ∧
          HasDerivAt (fun u => P.m u p.2) (P.mU p.1 p.2) p.1 ∧
          HasDerivAt (fun u => P.Q u p.2) (P.QU (s * e) p.1 p.2) p.1 ∧
          HasDerivAt (fun u => P.phi u p.2) (P.phiU (s * e) p.1 p.2) p.1 ∧
          HasDerivAt (fun u => P.theta u p.2) (P.thetaU (s * e) p.1 p.2) p.1)) ∧
      ∀ t ∈ Icc a z, (t, t) ∈ R ∧ P.r t t = b / s ∧
        P.nu t t = -1 / 2 ∧ P.lam t t = 1 / 2 ∧ P.A t t = 0 := by
  let P := nullPullback (rescaleFields (gaugeFields e S χ) s) F G
  let D := {p : ℝ × ℝ | (s * F p.1, s * G p.2) ∈ origDomain ui}
  let a := -T * (b / s) / 2
  let z := T * (b / s) / 2
  let f := fun t : ℝ => τ₀ + s * t / 2
  let R := sidewaysTruncation P D a z ρ (b / s)
  have hTb : 0 < T * b := mul_pos hT hb
  have haz : a ≤ z := by
    dsimp only [a, z]
    have hh : 0 ≤ T * (b / s) := mul_nonneg hT.le (div_pos hb hs).le
    linarith only [hh]
  have hsource : τ₀ - T * b / 2 ≤ τ₀ + T * b / 2 := by linarith only [hTb]
  have strictLabel (t) (ht : t ∈ Icc a z) :
      f t ∈ Ioo (τ₀ - T * b / 2) (τ₀ + T * b / 2) := by
    have ht' : t ∈ Icc (-(T / 2) * (b / s)) ((T / 2) * (b / s)) := by
      have hl : -(T / 2) * (b / s) = a := by dsimp only [a]; ring
      have hr : (T / 2) * (b / s) = z := by dsimp only [z]; ring
      rwa [hl, hr]
    have hh := normalized_clock_mem (τ₀ := τ₀) hs ht'
    dsimp only [f]
    constructor <;> nlinarith only [hh.1, hh.2, hTb]
  have phys (t) (ht : t ∈ Icc a z) :
      s * F t = γ.U (f t) ∧ s * G t = γ.V (f t) :=
    hcal t (Ioo_subset_Icc_self (strictLabel t ht))
  have labels (t) (ht : t ∈ Icc a z) : ui < s * F t ∧ s * G t < 0 := by
    have hh := strictLabel t ht
    have hm := γ.mem (f t) (Ioo_subset_Icc_self hh)
    rw [(phys t ht).1, (phys t ht).2]
    refine ⟨?_, ?_⟩
    · exact (γ.mem _ (left_mem_Icc.mpr hsource)).1.trans_lt
        (γ.strictMonoOn_U hS (left_mem_Icc.mpr hsource) (Ioo_subset_Icc_self hh) hh.1)
    · exact (γ.strictMonoOn_V hS (Ioo_subset_Icc_self hh)
        (right_mem_Icc.mpr hsource) hh.2).trans_le
          (γ.mem _ (right_mem_Icc.mpr hsource)).2.2.2
  have hdiagmem (t) (ht : t ∈ Icc a z) : (s * F t, s * G t) ∈ origDomain ui := by
    rw [(phys t ht).1, (phys t ht).2]
    exact γ.mem _ (Ioo_subset_Icc_self (strictLabel t ht))
  have hdiag (t) (ht : t ∈ Icc a z) : P.r t t = b / s := by
    change S.r (s * F t) (s * G t) / s = _
    rw [(phys t ht).1, (phys t ht).2, γ.radius _ (Ioo_subset_Icc_self (strictLabel t ht))]
  have hi := (labels a (left_mem_Icc.mpr haz)).1
  have hu := (hdiagmem z (right_mem_Icc.mpr haz)).2.1
  have hv := (labels z (right_mem_Icc.mpr haz)).2
  refine ⟨isCompact_actual_chart_truncation hS hs χ hχ F G hF hG F.monotone G.monotone hi.le hu
      hv.le,
    actual_chart_subtriangles hS hs hρ χ F G F.monotone G.monotone hi.le hv.le hdiag,
    chart_fields_continuousOn hS χ hχ F G hF hG R (fun _ hp => hp.1.1), ?_, ?_⟩
  · intro p hp
    have hpU : p.1 ∈ Icc a z := ⟨hp.1.2.1.trans hp.1.2.2.1, hp.1.2.2.2⟩
    have hpV : p.2 ∈ Icc a z := ⟨hp.1.2.1, hp.1.2.2.1.trans hp.1.2.2.2⟩
    have hproper : s * F p.1 < s * G p.2 := by
      rcases lt_or_eq_of_le hp.1.1.2.2.1 with hh | hh
      · exact hh
      · change s * F p.1 = s * G p.2 at hh
        have hm : (s * F p.1, s * G p.2) ∈ origDomain ui := hp.1.1
        have hz := (hS.axis (s * F p.1) (by simpa only [← hh] using hm)).1
        have hr : 0 < S.r (s * F p.1) (s * G p.2) / s := hρ.trans_le hp.2.1
        rw [← hh, hz, zero_div] at hr
        exact False.elim (lt_irrefl _ hr)
    exact observation_chart_equations hS hs χ hχ F G hF hG hFp hGp
      (labels p.1 hpU).1 hproper (labels p.2 hpV).2
  · intro t ht
    have hsourcet := strictLabel t ht
    have cm := calibrated_chart_components hS γ hs χ F G hcal hsourcet hsourcet
    have hn := (hS.nu_neg _ (γ.mem _ (Ioo_subset_Icc_self hsourcet))).ne
    have hl := (hS.lam_pos _ (γ.mem _ (Ioo_subset_Icc_self hsourcet))).ne'
    refine ⟨⟨⟨hdiagmem t ht, ht.1, le_rfl, ht.2⟩, by rw [hdiag t ht]; exact hρL,
      by rw [hdiag t ht]⟩, hdiag t ht, ?_, ?_, ?_⟩
    · have halg (x : ℝ) (hx : x ≠ 0) : (2 * (-x))⁻¹ * x = -1 / 2 := by
        field_simp
      rw [cm.2.2.2.2.1]
      exact halg _ hn
    · have halg (x : ℝ) (hx : x ≠ 0) : (2 * x)⁻¹ * x = 1 / 2 := by
        field_simp
      rw [cm.2.2.2.2.2.1]
      exact halg _ hl
    · change deriv (F : ℝ → ℝ) t *
        (S.A (s * F t) (s * G t) - deriv χ (s * F t)) = 0
      rw [(phys t ht).1, (phys t ht).2,
        (hχd _ (Ioo_subset_Icc_self hsourcet)).deriv, sub_self, mul_zero]

end EmcsfAcExtension.Global.Observation
