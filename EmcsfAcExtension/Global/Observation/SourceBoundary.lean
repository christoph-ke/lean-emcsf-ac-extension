module

public import EmcsfAcExtension.Global.Observation.Calibration
public import EmcsfAcExtension.Global.Observation.BoundaryControl
public import EmcsfAcExtension.Global.Observation.BoundaryFailedSource
import Mathlib

/-! # Boundary fields of the actual outer comparison record

The physical failure estimate gives both normalized small boundary norms.
Their scalar, mass and charge consequences are transported to the actual
calibrated chart, retaining the incoming error only in L².
Source: charged_SF_new_version.tex:L2060–2106, L2549–2583; approved internal project record.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
Supply every actual outer boundary input, including the measured incoming
boundary error, from failed physical observation. The maps are supplied
only through their defining calibration, and the chosen parallel gauge
only through its defining derivative and initial phase. The coefficient
`Ct` depends only on `T`; the failure coefficient is chosen after `T,ε`,
before all physical solution data and normalized parameters. -/
theorem source_outer_boundary_of_failed_observation {T : ℝ} (hT : 0 < T) :
    ∃ Ct : ℝ, 0 < Ct ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / Ct → ∃ Cobs : ℝ, 0 < Cobs ∧
    ∀ (ui e b s τ₀ : ℝ) (S : Fields) (_h : OriginalData ui e S)
      (γ : ClockCylinder S (origDomain ui) b (τ₀ - T * b / 2) (τ₀ + T * b / 2))
      (χ F G : ℝ → ℝ),
    let B := gaugeFields e S χ
    let L := b / s
    let H := B.a (γ.U τ₀) (γ.V τ₀)
    let M := S.m (γ.U τ₀) (γ.V τ₀) / s
    let Pzero := -(L : ℂ) * (B.theta (γ.U τ₀) (γ.V τ₀) / B.lam (γ.U τ₀) (γ.V τ₀))
    let q := S.Q (γ.U τ₀) (γ.V τ₀) / s
    let eta := |s * e| * L * (1 + ‖H‖)
    let P := nullPullback (rescaleFields B s) F G
    let a := -T * L / 2
    let z := T * L / 2
    0 < b → 0 < s → s ≤ b →
    ContDiff ℝ 1 χ →
    (∀ τ ∈ Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2),
      HasDerivAt χ (S.A (γ.U τ) (γ.V τ)) (γ.U τ)) →
    χ (γ.U (τ₀ - T * b / 2)) = 0 →
    (∀ x : ℝ, τ₀ + s * x / 2 ∈ Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2) →
      s * F x = γ.U (τ₀ + s * x / 2) ∧ s * G x = γ.V (τ₀ + s * x / 2)) →
    S.m (γ.U τ₀) (γ.V τ₀) + b *
      ‖S.theta (γ.U τ₀) (γ.V τ₀) / S.lam (γ.U τ₀) (γ.V τ₀)‖ ≤ s →
    (¬ ENNReal.ofReal (b * (‖S.theta (γ.U τ₀) (γ.V τ₀) /
      S.lam (γ.U τ₀) (γ.V τ₀)‖ ^ 2 + S.mu (γ.U τ₀) (γ.V τ₀) ^ 2)) ≤
      ENNReal.ofReal Cobs * (ENNReal.ofReal (cylinderDissipation S γ.U γ.V
        (τ₀ - T * b / 2) (τ₀ + T * b / 2)) + ENNReal.ofReal b *
        (curveCovVar e S S.a γ.U γ.V (τ₀ - T * b / 2) (τ₀ + T * b / 2)) ^ 2)) →
    (∀ t ∈ Icc a z, P.r t t = L ∧ P.nu t t = -1 / 2 ∧ P.lam t t = 1 / 2 ∧
      P.A t t = 0 ∧ ‖P.phi t t - H - Pzero / (L : ℂ)‖ ≤ Ct * ε / L ∧
      ‖P.a t t - H‖ ≤ ε / L ∧ |P.m t t - M| ≤ Ct * ε / L ∧
      |P.Q t t - q| ≤ Ct * eta) ∧
      ContinuousOn (fun t => P.phi t t - H + P.xi t t / P.nu t t) (Icc a z) ∧
      (∫ t in a..z, ‖P.phi t t - H + P.xi t t / P.nu t t‖ ^ 2) ≤ ε ^ 2 / L := by
  obtain ⟨Ct, hCt, hcontrol⟩ := boundary_control_of_small_boundary hT.le
  refine ⟨Ct, hCt, ?_⟩
  intro ε hε hεC
  obtain ⟨Cobs, hCobs, hsmall⟩ := small_boundary_of_solution_failed_observation hT.le hε
  refine ⟨Cobs, hCobs, ?_⟩
  intro ui e b s τ₀ S h γ χ F G
  dsimp only
  intro hb hs hsb hχ hχd hχ0 hcal hscale hfailure
  let B := gaugeFields e S χ
  let L := b / s
  let f := fun t : ℝ => τ₀ + s * t / 2
  let H := B.a (γ.U τ₀) (γ.V τ₀)
  let M := S.m (γ.U τ₀) (γ.V τ₀) / s
  let Pzero := -(L : ℂ) * (B.theta (γ.U τ₀) (γ.V τ₀) / B.lam (γ.U τ₀) (γ.V τ₀))
  let q := S.Q (γ.U τ₀) (γ.V τ₀) / s
  let eta := |s * e| * L * (1 + ‖H‖)
  let P := nullPullback (rescaleFields B s) F G
  let a := -T * L / 2
  let z := T * L / 2
  let incoming := fun t => B.phi (γ.U (f t)) (γ.V (f t)) - H +
    B.xi (γ.U (f t)) (γ.V (f t)) / B.nu (γ.U (f t)) (γ.V (f t))
  have hTL : 0 ≤ T * L := mul_nonneg hT.le (div_pos hb hs).le
  have haz : a ≤ z := by dsimp only [a, z]; linarith only [hTL]
  have hfull : -T * L ≤ T * L := by linarith only [hTL]
  have hsub : Icc a z ⊆ Icc (-T * L) (T * L) :=
    Icc_subset_Icc (by dsimp only [a]; linarith only [hTL])
      (by dsimp only [z]; linarith only [hTL])
  have strictLabel (t) (ht : t ∈ Icc a z) :
      f t ∈ Ioo (τ₀ - T * b / 2) (τ₀ + T * b / 2) := by
    have ht' : t ∈ Icc (-(T / 2) * L) ((T / 2) * L) := by
      have hl : -(T / 2) * L = a := by dsimp only [a]; ring
      have hr : (T / 2) * L = z := by dsimp only [z]; ring
      rwa [hl, hr]
    have hh := normalized_clock_mem (τ₀ := τ₀) hs ht'
    dsimp only [f]
    constructor <;> nlinarith only [hh.1, hh.2, mul_pos hT hb]
  have hbnd := hsmall ui e b s τ₀ S h γ χ hb hs hχ hχd hχ0 hscale hfailure
  have hc := hcontrol ui e b s τ₀ ε S h γ χ hb hs hsb hε.le hεC hχ hχd
    hscale hbnd.1 hbnd.2
  simp only [mul_zero, zero_div, add_zero] at hc
  have profiles := boundary_profiles_of_solution (T := T) (τ₀ := τ₀)
    h.solution γ χ hχ hs hb (Subset.rfl) hχd
  have cIncoming : ContinuousOn incoming (Icc (-T * L) (T * L)) :=
    (profiles.1.sub continuousOn_const).add profiles.2.2.1
  have iIncoming := (cIncoming.norm.pow 2).intervalIntegrable_of_Icc (μ := volume) hfull
  have hmatch (t) (ht : t ∈ Icc a z) :
      P.phi t t - H + P.xi t t / P.nu t t = incoming t := by
    have cm := calibrated_chart_components h.solution γ hs χ F G hcal
      (strictLabel t ht) (strictLabel t ht)
    change P.phi t t - H + P.xi t t / P.nu t t = _
    rw [cm.2.2.2.2.2.2.1, cm.2.2.2.2.2.2.2.2.1]
  refine ⟨?_, (cIncoming.mono hsub).congr (fun t ht => hmatch t ht), ?_⟩
  · intro t ht
    have ht' := strictLabel t ht
    have cm := calibrated_chart_components h.solution γ hs χ F G hcal ht' ht'
    have hval := hc t (hsub ht)
    have hnu := (h.solution.nu_neg _ (γ.mem _ (Ioo_subset_Icc_self ht'))).ne
    have hlam := (h.solution.lam_pos _ (γ.mem _ (Ioo_subset_Icc_self ht'))).ne'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [cm.1, γ.radius _ (Ioo_subset_Icc_self ht')]
    · have halg (x : ℝ) (hx : x ≠ 0) : (2 * (-x))⁻¹ * x = -1 / 2 := by field_simp
      rw [cm.2.2.2.2.1]
      exact halg _ hnu
    · have halg (x : ℝ) (hx : x ≠ 0) : (2 * x)⁻¹ * x = 1 / 2 := by field_simp
      rw [cm.2.2.2.2.2.1]
      exact halg _ hlam
    · change deriv F t * (S.A (s * F t) (s * G t) - deriv χ (s * F t)) = 0
      rw [(hcal t (Ioo_subset_Icc_self ht')).1, (hcal t (Ioo_subset_Icc_self ht')).2,
        (hχd _ (Ioo_subset_Icc_self ht')).deriv, sub_self, mul_zero]
    · rw [cm.2.2.2.2.2.2.1]
      exact hval.1.1.1
    · rw [cm.2.2.2.2.2.2.2.2.2]
      exact hbnd.1 t (hsub ht)
    · rw [cm.2.1]
      exact hval.1.1.2.1
    · rw [cm.2.2.1]
      exact hval.1.2
  · have heq : (∫ t in a..z, ‖P.phi t t - H + P.xi t t / P.nu t t‖ ^ 2) =
        ∫ t in a..z, ‖incoming t‖ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le haz] at ht
      dsimp only
      rw [hmatch t ht]
    rw [heq]
    have hm := intervalIntegral.integral_mono_interval
      (show -T * L ≤ a by dsimp only [a]; linarith only [hTL]) haz
      (show z ≤ T * L by dsimp only [z]; linarith only [hTL])
      (Filter.Eventually.of_forall (fun t => sq_nonneg ‖incoming t‖)) iIncoming
    exact hm.trans hbnd.2

end EmcsfAcExtension.Global.Observation
