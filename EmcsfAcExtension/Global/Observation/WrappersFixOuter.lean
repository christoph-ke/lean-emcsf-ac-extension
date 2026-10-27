module

public import EmcsfAcExtension.Global.Observation.WrappersFixMass
import EmcsfAcExtension.Global.Observation.SourceOuterReference
import EmcsfAcExtension.Global.Observation.Static.OuterReference
import EmcsfAcExtension.Global.Observation.WrappersControls
import EmcsfAcExtension.Global.Observation.Gauge
import Mathlib

/-! # Outer observation polynomials with the source constant order

internal project record–F3. Source: charged_SF_new_version.tex:L2476–2531; approved internal project
record.
The scalar boundary coefficient follows the window and precedes the gap.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global.Observation

private theorem failure_of_larger_coefficient {A E : ℝ≥0∞} {c C : ℝ}
    (hc : c ≤ C) (hf : ¬ A ≤ ENNReal.ofReal C * E) : ¬ A ≤ ENNReal.ofReal c * E := by
  intro hh
  exact hf (hh.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hc) (zero_le : 0 ≤ E)))

/-- [node prop:charged-observation#outer-boundary-difference-data]
[node eq:co-outer-sup]
[node eq:co-outer-mass]
The actual boundary identities and two stopped regional polynomials.
Reference and neutral coefficients are universal. `Ct,CbM` depend only on
`T`, before `δ`; charge and electric coefficients may depend on `δ,T`.
Tolerances follow `Lzero`; all coefficients and tolerances precede physical
fields, scale, coupling, background and errors. Only the source scalar stop
is tested in the conclusion; its numerical mass envelope is arbitrary. -/
theorem outer_comparison_with_separate_boundary :
    ∃ Kstatic Lref Cn CnM : ℝ,
      0 < Kstatic ∧ 0 < Lref ∧ 0 < Cn ∧ 0 < CnM ∧
    ∀ T : ℝ, 0 < T → ∃ Ct CbM : ℝ, 0 < Ct ∧ 0 < CbM ∧
    ∀ δ : ℝ, 0 < δ → ∃ Bboundary Cq Ce CeM : ℝ,
      0 < Bboundary ∧ 0 < Cq ∧ 0 < Ce ∧ 0 < CeM ∧
    ∀ Lzero : ℝ, Lref ≤ Lzero → ∃ εc ηc : ℝ, 0 < εc ∧ 0 < ηc ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ εc → ∃ Cobs : ℝ, 0 < Cobs ∧
    ∀ (ui e b s τ₀ : ℝ) (S : Fields) (_h : OriginalData ui e S)
      (γ : ClockCylinder S (origDomain ui) b (τ₀ - T * b / 2) (τ₀ + T * b / 2))
      (χ : ℝ → ℝ) (F G : ℝ ≃o ℝ),
    let B := gaugeFields e S χ
    let L := b / s
    let H := B.a (γ.U τ₀) (γ.V τ₀)
    let Pzero := -(L : ℂ) * (B.theta (γ.U τ₀) (γ.V τ₀) / B.lam (γ.U τ₀) (γ.V τ₀))
    let q := S.Q (γ.U τ₀) (γ.V τ₀) / s
    let eta := |s * e| * L * (1 + ‖H‖)
    let P := nullPullback (rescaleFields B s) F G
    let D := {p : ℝ × ℝ | (s * F p.1, s * G p.2) ∈ origDomain ui}
    let a := -T * L / 2
    let z := T * L / 2
    0 < b → 0 < s → s ≤ b → Lzero ≤ L →
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
    ∃ (phiStar yStar : ℝ → ℂ) (mStar : ℝ → ℝ),
      OuterNormalizationData Kstatic Ct Bboundary P D H Pzero phiStar yStar mStar
        a z Lzero L ε eta q (s * e) ∧
      outerExact P D H phiStar yStar mStar a z Lzero L ε q (s * e) Ct ∧
      ∀ Nphi Nm : ℝ, 0 ≤ Nphi → Nphi ≤ 1 → 0 ≤ Nm →
        comparisonNorm (sidewaysTruncation P D a z Lzero L) (scalarComparison P H phiStar) ≤
          ENNReal.ofReal Nphi →
        comparisonNorm (sidewaysTruncation P D a z Lzero L) (massComparison P mStar) ≤
          ENNReal.ofReal Nm →
        comparisonNorm (sidewaysTruncation P D a z Lzero L) (scalarComparison P H phiStar) ≤
          ENNReal.ofReal ((Ct + 4) * ε + 64 * (Cn * (Nphi + Nm)) / Lzero + 96 * (Ce * eta)) ∧
        comparisonNorm (sidewaysTruncation P D a z Lzero L) (massComparison P mStar) ≤
          ENNReal.ofReal ((CbM * ε + CeM * eta) / Lzero +
            (CnM / Lzero) * (Nphi + Nphi ^ 2) + (CnM / Lzero ^ 2) * Nm +
              (CnM / Lzero ^ 3) * Nm ^ 2) := by
  obtain ⟨Lstatic, Kstatic, hLs, hKs, href⟩ := outer_radial_reference
  obtain ⟨Cn, hCn, hscalar⟩ := outer_scalar_of_normalization Kstatic hKs.le
  obtain ⟨CnM, hCnM, hmass⟩ :=
    outer_mass_with_separate_boundary_of_normalization Kstatic Cn hKs.le hCn.le
  obtain ⟨Cp, hCp, hcontrols⟩ := outer_controls_of_normalization Kstatic hKs.le
  let Lref := max 128 Lstatic
  refine ⟨Kstatic, Lref, Cn, CnM, hKs,
    (by norm_num : (0 : ℝ) < 128).trans_le (le_max_left _ _), hCn, hCnM, ?_⟩
  intro T hT
  obtain ⟨Ct, hCt, hboundary⟩ := source_outer_boundary_of_failed_observation hT
  obtain ⟨CbM, hCbM, hmass⟩ := hmass Ct hCt.le
  refine ⟨Ct, CbM, hCt, hCbM, ?_⟩
  intro δ hδ
  obtain ⟨ηsource, hηsource, hsource⟩ := source_outer_data_of_reference hδ Kstatic hKs
  obtain ⟨Bboundary, Ccap, hBboundary, hCcap, hsource⟩ := hsource T hT
  obtain ⟨Ce, CqS, hCe, hCqS, hscalar⟩ := hscalar Bboundary hBboundary.le
  obtain ⟨CqP, hCqP, hcontrols⟩ := hcontrols Bboundary hBboundary.le
  let Cq := max CqS CqP
  have hCq : 0 < Cq := hCqS.trans_le (le_max_left _ _)
  obtain ⟨CeM, hCeM, hmass⟩ := hmass Ce Cq hCe.le hCq.le
  refine ⟨Bboundary, Cq, Ce, CeM, hBboundary, hCq, hCe, hCeM, ?_⟩
  intro Lzero hLzero
  let εc := min (1 / Ccap) (1 / Ct)
  let ηc := min ηsource (1 / Cq)
  refine ⟨εc, ηc, lt_min (by positivity) (by positivity), lt_min hηsource (by positivity), ?_⟩
  intro ε hε hεc
  obtain ⟨Co, hCo, hsource⟩ := hsource ε hε (hεc.trans (min_le_left _ _))
  obtain ⟨Cb, hCb, hboundary⟩ := hboundary ε hε (hεc.trans (min_le_right _ _))
  refine ⟨max Co Cb, hCo.trans_le (le_max_left _ _), ?_⟩
  intro ui e b s τ₀ S h γ χ F G
  dsimp only
  intro hb hs hsb hL hscale hχ hχd hχ0 hF hG hFp hGp hcal hgap hcharged hfailure
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
  have h128 : 128 ≤ Lzero := (le_max_left _ _).trans hLzero
  have hLstatic : Lstatic ≤ Lzero := (le_max_right _ _).trans hLzero
  have hL1 : 1 ≤ Lzero := (by norm_num : (1 : ℝ) ≤ 128).trans h128
  have hLp : 0 < Lzero := zero_lt_one.trans_le hL1
  have htime : τ₀ ∈ Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2) := by
    constructor <;> nlinarith only [mul_pos hT hb]
  have central := central_parameters_of_physical_scale h γ hb hs htime χ hscale
  obtain ⟨phiStar, yStar, mStar, hstatic⟩ :=
    href Lzero L M q Pzero hLstatic hL central.1 central.2.1
  obtain ⟨ho, _traceCont, _traceBound⟩ := hsource ui e b s τ₀ Lzero S h γ χ F G
    hb hs hsb h128 hL hscale hχ hχd hχ0 hF hG hFp hGp hcal hgap
    (hcharged.trans (min_le_left _ _))
    (failure_of_larger_coefficient (le_max_left _ _) hfailure) phiStar yStar mStar hstatic
  have hbnd := hboundary ui e b s τ₀ S h γ χ F G hb hs hsb hχ hχd hχ0 hcal
    central.2.2.2 (failure_of_larger_coefficient (le_max_right _ _) hfailure)
  have ho' : OuterNormalizationData Kstatic Ct Bboundary P D H Pzero phiStar yStar mStar
      a z Lzero L ε eta q (s * e) := { ho with
    boundary := by
      intro t ht
      have hbOld := ho.boundary t ht
      have hbNew := hbnd.1 t ⟨ht.1.2.1, ht.1.2.2.2⟩
      refine ⟨hbOld.1, hbOld.2.1, hbNew.2.2.2.2.1, hbOld.2.2.2.1, ?_,
        hbOld.2.2.2.2.2.1, hbOld.2.2.2.2.2.2⟩
      change |P.m t t - mStar (P.r t t)| ≤ _
      rw [hbOld.1, hstatic.2.2.2.1]
      exact hbNew.2.2.2.2.2.2.1 }
  have hH : ‖H‖ = ‖S.a (γ.U τ₀) (γ.V τ₀)‖ := by
    rw [show H = B.a (γ.U τ₀) (γ.V τ₀) from rfl, gauge_normalized_out,
      norm_mul, norm_gauge_phase, one_mul]
  have hetaEq : eta = |e| * b * (1 + ‖S.a (γ.U τ₀) (γ.V τ₀)‖) := by
    rw [show eta = |s * e| * (b / s) * (1 + ‖H‖) from rfl, co_eta _ _ _ _ hs, hH]
  have hcharge : Cq * eta ≤ 1 := by
    have hh : eta ≤ 1 / Cq := by rw [hetaEq]; exact hcharged.trans (min_le_right _ _)
    simpa only [mul_comm] using (le_div_iff₀ hCq).mp hh
  refine ⟨phiStar, yStar, mStar, ho', outer_exact_of_normalization hLp ho', ?_⟩
  intro Nphi Nm hNp hstop hNm hw hm
  have hscalar' := hscalar Ct P D H Pzero phiStar yStar mStar a z Lzero L ε eta q (s * e)
    Nphi Nm ho' hL1 hCt.le
    ((mul_le_mul_of_nonneg_right (le_max_left _ _) ho'.errors.2.1).trans hcharge)
    hNp hstop hNm hw hm
  have hcontrols' := hcontrols P D H Pzero phiStar yStar mStar a z Lzero L ε eta q (s * e) Ct
    ho' hL1 ((mul_le_mul_of_nonneg_right (le_max_right _ _) ho'.errors.2.1).trans hcharge)
    (hw.trans (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hstop))
  refine ⟨hscalar'.2.2.1, hmass P D H Pzero phiStar yStar mStar a z Lzero L ε eta q (s * e)
    Nphi Nm Bboundary ho' hL1 hNp hNm ?_ hscalar'.2.2.2⟩
  intro p hp
  exact ⟨(hcontrols' p hp).2.1,
    (hscalar'.1 p hp).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ho'.errors.2.1)⟩

end EmcsfAcExtension.Global.Observation
