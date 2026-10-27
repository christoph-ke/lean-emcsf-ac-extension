module

public import EmcsfAcExtension.Global.Observation.SourceGeometry
public import EmcsfAcExtension.Global.Observation.SourceBoundary
public import EmcsfAcExtension.Global.Observation.CentralParameters
public import EmcsfAcExtension.Global.Observation.IncomingTransfer
import EmcsfAcExtension.Global.Observation.Gauge
import Mathlib

/-! # The outer comparison record from the original observation setting

All analytic, geometric and boundary fields are constructed from the
original solution. The selected checked static reference remains visible
to preserve its matching with the same stopped inner continuation.
Source: charged_SF_new_version.tex:L1957–2544; approved internal project record.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global.Observation

private theorem failed_bound_of_coefficient_le {A E : ℝ≥0∞} {c C : ℝ}
    (hc : c ≤ C) (hf : ¬A ≤ ENNReal.ofReal C * E) : ¬A ≤ ENNReal.ofReal c * E := by
  intro hh
  exact hf (hh.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hc) (zero_le : 0 ≤ E)))

/-- [internal]
Construct the source outer record for any fixed checked radial reference.
The consumer supplies only its static ODE fields and initial data, and
must derive these from the selected reference family. Every physical,
analytic, chart and boundary input of the comparison record is discharged.
Constants are chosen after `δ,Kstatic,T,ε` in that order, before physical
fields and the chosen member. This form preserves the same outer member
that is matched to its own stopped inner continuation. -/
theorem source_outer_data_of_reference {δ : ℝ} (hδ : 0 < δ)
    (Kstatic : ℝ) (_hKs : 0 < Kstatic) :
    ∃ ηc : ℝ, 0 < ηc ∧
    ∀ T : ℝ, 0 < T → ∃ Ct Ccap : ℝ, 0 < Ct ∧ 0 < Ccap ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / Ccap → ∃ Cobs : ℝ, 0 < Cobs ∧
    ∀ (ui e b s τ₀ Lzero : ℝ) (S : Fields) (_h : OriginalData ui e S)
      (γ : ClockCylinder S (origDomain ui) b (τ₀ - T * b / 2) (τ₀ + T * b / 2))
      (χ : ℝ → ℝ) (F G : ℝ ≃o ℝ),
    let B := gaugeFields e S χ
    let L := b / s
    let H := B.a (γ.U τ₀) (γ.V τ₀)
    let M := S.m (γ.U τ₀) (γ.V τ₀) / s
    let Pzero := -(L : ℂ) * (B.theta (γ.U τ₀) (γ.V τ₀) / B.lam (γ.U τ₀) (γ.V τ₀))
    let q := S.Q (γ.U τ₀) (γ.V τ₀) / s
    let eta := |s * e| * L * (1 + ‖H‖)
    let P := nullPullback (rescaleFields B s) F G
    let D := {p : ℝ × ℝ | (s * F p.1, s * G p.2) ∈ origDomain ui}
    let a := -T * L / 2
    let z := T * L / 2
    0 < b → 0 < s → s ≤ b → 128 ≤ Lzero → Lzero ≤ L →
    s = S.m (γ.U τ₀) (γ.V τ₀) + b *
      ‖S.theta (γ.U τ₀) (γ.V τ₀) / S.lam (γ.U τ₀) (γ.V τ₀)‖ +
        |S.Q (γ.U τ₀) (γ.V τ₀)| →
    ContDiff ℝ 1 χ →
    (∀ τ ∈ Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2),
      HasDerivAt χ (S.A (γ.U τ) (γ.V τ)) (γ.U τ)) →
    χ (γ.U (τ₀ - T * b / 2)) = 0 →
    ContDiff ℝ 1 (F : ℝ → ℝ) → ContDiff ℝ 1 (G : ℝ → ℝ) →
    (∀ x, 0 < deriv (F : ℝ → ℝ) x) → (∀ x, 0 < deriv (G : ℝ → ℝ) x) →
    (∀ x : ℝ, τ₀ + s * x / 2 ∈ Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2) →
      s * F x = γ.U (τ₀ + s * x / 2) ∧ s * G x = γ.V (τ₀ + s * x / 2)) →
    (∀ p ∈ triangle (γ.U (τ₀ - T * b / 2)) (γ.V (τ₀ + T * b / 2)),
      δ ≤ 1 - S.mu p.1 p.2) →
    |e| * b * (1 + ‖S.a (γ.U τ₀) (γ.V τ₀)‖) ≤ ηc →
    (¬ ENNReal.ofReal (b * (‖S.theta (γ.U τ₀) (γ.V τ₀) /
      S.lam (γ.U τ₀) (γ.V τ₀)‖ ^ 2 + S.mu (γ.U τ₀) (γ.V τ₀) ^ 2)) ≤
      ENNReal.ofReal Cobs * (ENNReal.ofReal (cylinderDissipation S γ.U γ.V
        (τ₀ - T * b / 2) (τ₀ + T * b / 2)) + ENNReal.ofReal b *
        (curveCovVar e S S.a γ.U γ.V (τ₀ - T * b / 2) (τ₀ + T * b / 2)) ^ 2)) →
    ∀ (phiStar yStar : ℝ → ℂ) (mStar : ℝ → ℝ),
    (AbsolutelyContinuousOnInterval mStar Lzero L ∧
      ContinuousOn phiStar (Icc Lzero L) ∧ ContinuousOn yStar (Icc Lzero L) ∧
      mStar L = M ∧ phiStar L = Pzero / (L : ℂ) ∧ phiStar L + yStar L = 0 ∧
      (∀ r ∈ Icc Lzero L,
        let k := (2 * mStar r / r - q ^ 2 / r ^ 2) / (1 - 2 * mStar r / r)
        HasDerivAt (fun x : ℝ => (x : ℂ) * phiStar x) (phiStar r + yStar r) r ∧
        HasDerivAt (fun x => phiStar x + yStar x) ((-k / r : ℝ) * yStar r) r ∧
        HasDerivAt mStar ((1 - 2 * mStar r / r) * ‖yStar r‖ ^ 2 / 2 + q ^ 2 / (2 * r ^ 2)) r) ∧
      ∀ r ∈ Icc Lzero L,
        |mStar r| ≤ 2 ∧ ‖yStar r‖ ≤ Kstatic / r ∧ |1 - 2 * mStar r / r| ≤ 2 ∧
        ‖(r : ℂ) * phiStar r‖ ≤ Kstatic ∧ ‖phiStar r + yStar r‖ ≤ Kstatic / r ^ 2 ∧
        1 / 2 ≤ 1 - 2 * mStar r / r) →
      OuterNormalizationData Kstatic Ct Ct P D H Pzero phiStar yStar mStar
        a z Lzero L ε eta q (s * e) ∧
      ContinuousOn (fun t => P.phi t t - H + P.xi t t / P.nu t t) (Icc a z) ∧
      (∫ t in a..z, ‖P.phi t t - H + P.xi t t / P.nu t t‖ ^ 2) ≤ ε ^ 2 / L := by
  obtain ⟨ηopt, hηopt, hbox⟩ := calibrated_chart_box_of_failed_observation hδ
  let ηc := min ηopt 1
  have hηc : 0 < ηc := lt_min hηopt zero_lt_one
  refine ⟨ηc, hηc, ?_⟩
  intro T hT
  obtain ⟨Ct, hCt, hboundary⟩ := source_outer_boundary_of_failed_observation hT
  obtain ⟨Cb, hCb, hbox⟩ := hbox T hT
  let Ccap := max 1 (max Ct Cb)
  have hCcap : 0 < Ccap := zero_lt_one.trans_le (le_max_left _ _)
  have hCtCap : Ct ≤ Ccap := (le_max_left _ _).trans (le_max_right _ _)
  have hCbCap : Cb ≤ Ccap := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨Ct, Ccap, hCt, hCcap, ?_⟩
  intro ε hε hεCap
  have hεCt : ε ≤ 1 / Ct := hεCap.trans (one_div_le_one_div_of_le hCt hCtCap)
  have hεCb : ε ≤ 1 / Cb := hεCap.trans (one_div_le_one_div_of_le hCb hCbCap)
  have hεOne : ε ≤ 1 := hεCap.trans
    ((one_div_le_one_div_of_le zero_lt_one (le_max_left 1 (max Ct Cb))).trans_eq (by norm_num))
  obtain ⟨Cbd, hCbd, hboundary⟩ := hboundary ε hε hεCt
  obtain ⟨Cbo, hCbo, hbox⟩ := hbox ε hε hεCb
  refine ⟨max Cbd Cbo, lt_of_lt_of_le hCbd (le_max_left _ _), ?_⟩
  intro ui e b s τ₀ Lzero S h γ χ F G
  dsimp only
  intro hb hs hsb h128 hLzero hscale hχ hχd hχ0 hF hG hFp hGp hcal hgap hcharged hfailure
    phiStar yStar mStar hstatic
  rcases hstatic with ⟨hmAC, cphi, cy, hmL, hphiL, hsumL, hstaticEq, hstaticBox⟩
  let B := gaugeFields e S χ
  let L := b / s
  let H := B.a (γ.U τ₀) (γ.V τ₀)
  let M := S.m (γ.U τ₀) (γ.V τ₀) / s
  let Pzero := -(L : ℂ) * (B.theta (γ.U τ₀) (γ.V τ₀) / B.lam (γ.U τ₀) (γ.V τ₀))
  let q := S.Q (γ.U τ₀) (γ.V τ₀) / s
  let eta := |s * e| * L * (1 + ‖H‖)
  let P := nullPullback (rescaleFields B s) F G
  let D := {p : ℝ × ℝ | (s * F p.1, s * G p.2) ∈ origDomain ui}
  let a := -T * L / 2
  let z := T * L / 2
  let R := sidewaysTruncation P D a z Lzero L
  have hLzeroPos : 0 < Lzero := lt_of_lt_of_le (by norm_num) h128
  have hLzero16 : 16 ≤ Lzero := (by norm_num : (16 : ℝ) ≤ 128).trans h128
  have htime : τ₀ ∈ Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2) := by
    constructor <;> nlinarith only [mul_pos hT hb]
  have hcentral := central_parameters_of_physical_scale h γ hb hs htime χ hscale
  have hfailBd := failed_bound_of_coefficient_le (le_max_left Cbd Cbo) hfailure
  have hfailBo := failed_bound_of_coefficient_le (le_max_right Cbd Cbo) hfailure
  have hbnd := hboundary ui e b s τ₀ S h γ χ F G hb hs hsb hχ hχd hχ0 hcal
    hcentral.2.2.2 hfailBd
  have hH : ‖H‖ = ‖S.a (γ.U τ₀) (γ.V τ₀)‖ := by
    rw [show H = B.a (γ.U τ₀) (γ.V τ₀) from rfl, gauge_normalized_out,
      norm_mul, norm_gauge_phase, one_mul]
  have hetaEq : eta = |e| * b * (1 + ‖S.a (γ.U τ₀) (γ.V τ₀)‖) := by
    rw [show eta = |s * e| * (b / s) * (1 + ‖H‖) from rfl, co_eta _ _ _ _ hs, hH]
  have heta : 0 ≤ eta := by dsimp only [eta]; positivity
  have hetaOne : eta ≤ 1 := by rw [hetaEq]; exact hcharged.trans (min_le_right _ _)
  have hetaOpt : |e| * b * (1 + ‖H‖) ≤ ηopt := by
    rw [hH]
    exact hcharged.trans (min_le_left _ _)
  have hboxActual := hbox ui e b s τ₀ S h γ χ hb hs hsb hχ hχd hχ0
    hcentral.2.2.2 hgap hetaOpt hfailBo F G hcal
  have geometry := source_chart_geometry_of_calibration h.solution hb hs hT hLzeroPos hLzero
    γ χ hχ F G hF hG hFp hGp hcal hχd
  rcases geometry.2.2.1 with ⟨cr, cn, cl, cA, cp, ct, cm, cQ, cx⟩
  have hz : 0 ≤ T * L := mul_nonneg hT.le (div_pos hb hs).le
  have hzero : (0 : ℝ) ∈ Icc a z := by dsimp only [a, z]; constructor <;> linarith only [hz]
  refine ⟨?_, hbnd.2.1, hbnd.2.2⟩
  refine {
    ordered := hLzero
    errors := ⟨⟨hε.le, hεOne⟩, heta, hetaOne⟩
    reference_charge := hcentral.2.2.1
    scale := rfl
    compact := geometry.1
    fields := ⟨cr, cn, cl, cA, cp, ct, cm, cQ⟩
    incoming_continuous := cx
    static_mass_ac := hmAC
    static_continuous := ⟨cphi, cy⟩
    static_boundary := ⟨hphiL, hsumL⟩
    static_equations := hstaticEq
    static_bounds := hstaticBox
    base := ⟨(0, 0), (geometry.2.2.2.2 0 hzero).1, (geometry.2.2.2.2 0 hzero).2.1⟩
    triangles := geometry.2.1
    box := fun p hp => (hboxActual Lzero hLzeroPos p hp).2.2.2.2 hLzero16
    equations := ?_
    incoming_equations := ?_
    boundary := ?_
    incoming_boundary := ?_
  }
  · intro p hp
    rcases geometry.2.2.2.1 p hp with
      ⟨⟨hrOut, _hnOut, hmOut, hQOut, hAOut, hphiOut, _hxiOut⟩,
        ⟨hrIn, hlIn, _hmIn, _hQIn, hphiIn, hthetaIn⟩⟩
    exact ⟨hrIn, hrOut, hmOut, hphiOut, hQOut, hAOut, hlIn, hphiIn, hthetaIn⟩
  · intro p hp
    have heq := (geometry.2.2.2.1 p hp).1
    exact ⟨heq.2.1, heq.2.2.2.2.2.2⟩
  · intro t ht
    have hclock : t ∈ Icc a z := ⟨ht.1.2.1, ht.1.2.2.2⟩
    rcases hbnd.1 t hclock with ⟨hr, _hn, hl, hA, hphi, ha, hm, hQ⟩
    refine ⟨hr, hl, hphi, ha, ?_, hA, hQ⟩
    change |P.m t t - mStar (P.r t t)| ≤ _
    rw [hr, hmL]
    exact hm
  · intro t ht
    exact (hbnd.1 t ⟨ht.1.2.1, ht.1.2.2.2⟩).2.1

end EmcsfAcExtension.Global.Observation
