module

public import EmcsfAcExtension.Global.Observation.WrappersFixInnerFacts
public import EmcsfAcExtension.Global.Observation.WrappersInnerFacts
import EmcsfAcExtension.Global.Observation.WrappersControls
import EmcsfAcExtension.Global.Observation.OuterClosure
import EmcsfAcExtension.Global.Observation.SourceOuterReference
import EmcsfAcExtension.Global.Observation.Static.ReferenceFamily
import EmcsfAcExtension.Global.Observation.InnerRecord
import EmcsfAcExtension.Global.Observation.Gauge
import Mathlib

/-! # Source-setting wrappers for the complete inner comparison chain

The actual retained-gauge chart and matched reference are constructed from
the original observation setting. Source: charged_SF_new_version.tex:L2587–2735;
approved internal project record and the six internal project record inner repairs.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global.Observation

private theorem failure_mono {A E : ℝ≥0∞} {c C : ℝ} (hc : c ≤ C)
    (hf : ¬ A ≤ ENNReal.ofReal C * E) : ¬ A ≤ ENNReal.ofReal c * E := by
  intro h
  exact hf (h.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hc) (zero_le : 0 ≤ E)))

/-- [node prop:charged-observation#inner-potential-control]
[node prop:charged-observation#inner-source-bounds]
[node prop:charged-observation#inner-comparison-closure]
The actual inner comparison through the member's own strict barrier.
All coefficients, common positive margin, annuli and tolerances depend only
on `δ`, before `ε` and every physical solution, scale, coupling and background.
Every smaller positive `ε` has its observation coefficient. The returned
ordinary potential retains the incoming Jacobian and the exact outer scale;
the individual geometric/electric/potential bounds are uniform. Both matched
source references, the strict violation and the actual test point with its
whole dependence triangle are retained, together with all prior estimates. -/
theorem inner_comparison_through_strict_barrier (δ : ℝ) (hδ : δ ∈ Ioo 0 1) :
    ∃ T ηstar Lzero εc rStar c K Cref delta Ct
      Qmax Cscalar Bcharge Amax Ctheta Cmass Cxi
      A Bsrc Echarge Cm Cz Cv Cclose sigma γmargin Cp Cpotential Cg Ce : ℝ,
    0 < T ∧ 0 < ηstar ∧ 1 ≤ Lzero ∧ 0 < εc ∧
      0 < rStar ∧ rStar ≤ Lzero ∧ 0 < c ∧ 0 < K ∧ 0 < Cref ∧ 0 < delta ∧
      0 < Ct ∧ 0 < Qmax ∧ 0 < Cscalar ∧ 0 < Bcharge ∧ 0 < Amax ∧
      0 < Ctheta ∧ 0 < Cmass ∧ 0 < Cxi ∧
      0 < A ∧ 0 < Bsrc ∧ 0 < Echarge ∧ 0 < Cm ∧ 0 < Cz ∧ 0 < Cv ∧ 0 < Cclose ∧
      0 < sigma ∧ 0 < γmargin ∧ 0 < Cp ∧
      0 < Cpotential ∧ 0 < Cg ∧ 0 < Ce ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ εc → ∃ Cobs > 0,
    ∀ (ui e b s τ₀ : ℝ) (S : Fields) (_h : OriginalData ui e S)
      (γ : ClockCylinder S (origDomain ui) b (τ₀ - T * b / 2) (τ₀ + T * b / 2)),
    0 < b → 0 < s → Lzero ≤ b / s →
    s = S.m (γ.U τ₀) (γ.V τ₀) + b *
      ‖S.theta (γ.U τ₀) (γ.V τ₀) / S.lam (γ.U τ₀) (γ.V τ₀)‖ +
        |S.Q (γ.U τ₀) (γ.V τ₀)| →
    (∀ p ∈ triangle (γ.U (τ₀ - T * b / 2)) (γ.V (τ₀ + T * b / 2)),
      δ ≤ 1 - S.mu p.1 p.2) →
    |e| * b * (1 + ‖S.a (γ.U τ₀) (γ.V τ₀)‖) ≤ ηstar →
    (¬ ENNReal.ofReal (b * (‖S.theta (γ.U τ₀) (γ.V τ₀) /
      S.lam (γ.U τ₀) (γ.V τ₀)‖ ^ 2 + S.mu (γ.U τ₀) (γ.V τ₀) ^ 2)) ≤
      ENNReal.ofReal Cobs * (ENNReal.ofReal (cylinderDissipation S γ.U γ.V
        (τ₀ - T * b / 2) (τ₀ + T * b / 2)) + ENNReal.ofReal b *
        (curveCovVar e S S.a γ.U γ.V (τ₀ - T * b / 2) (τ₀ + T * b / 2)) ^ 2)) →
    ∃ (χ : ℝ → ℝ) (F G U V : ℝ ≃o ℝ) (rho : ℝ)
      (phiOut yOut : ℝ → ℂ) (mOut : ℝ → ℝ) (yIn : ℝ → ℂ) (mIn : ℝ → ℝ),
    let B := gaugeFields e S χ
    let L := b / s
    let H := B.a (γ.U τ₀) (γ.V τ₀)
    let M := S.m (γ.U τ₀) (γ.V τ₀) / s
    let Pzero := -(L : ℂ) * (B.theta (γ.U τ₀) (γ.V τ₀) / B.lam (γ.U τ₀) (γ.V τ₀))
    let q := S.Q (γ.U τ₀) (γ.V τ₀) / s
    let eta := |s * e| * L * (1 + ‖H‖)
    let P := nullPullback (rescaleFields B s) F G
    let D := {p : ℝ × ℝ | (s * F p.1, s * G p.2) ∈ origDomain ui}
    let Q := nullPullback P U V
    let E := {p : ℝ × ℝ | (U p.1,V p.2) ∈ D}
    rho ∈ Icc rStar Lzero ∧ yIn Lzero = yOut Lzero ∧ mIn Lzero = mOut Lzero ∧
      OuterNormalizationData 41 Ct Ct P D H Pzero phiOut yOut mOut
        (-T * L / 2) (T * L / 2) Lzero L ε eta q (s * e) ∧
      InnerComparisonData rho Lzero delta c Cref (1 + 2 * Cref ^ 2) Qmax Cscalar Bcharge Amax
        Q E H yIn mIn (-K) K q (s * e) eta
        (Ctheta * (ε + eta)) (Cmass * (ε + eta)) (Cxi * (ε + eta)) ∧
      innerConclusions rStar Lzero delta c Cref (1 + 2 * Cref ^ 2) Qmax Cscalar Bcharge Amax
        A Bsrc Echarge Cm Cz Cv Cclose sigma Ctheta Cmass Cxi
        rho Q E H yIn mIn (-K) K q (s * e) ε eta ∧
      mOut L = M ∧
      (ContinuousOn yIn (Icc rho Lzero) ∧ ContinuousOn mIn (Icc rho Lzero) ∧
        (∀ r ∈ Icc rho Lzero, ‖yIn r‖ ≤ Cref ∧
          1 / (Cref + 1) ≤ 1 - 2 * mIn r / r ∧ |1 - 2 * mIn r / r| ≤ 1 + 2 * Cref ^ 2) ∧
        ∀ r ∈ Ioo rho Lzero,
          let k := (2 * mIn r / r - q ^ 2 / r ^ 2) / (1 - 2 * mIn r / r)
          HasDerivAt yIn (((-(1 + k) / r : ℝ) : ℂ) * yIn r) r ∧
          HasDerivAt mIn ((1 - 2 * mIn r / r) * ‖yIn r‖ ^ 2 / 2 + q ^ 2 / (2 * r ^ 2)) r) ∧
      (mIn rho ≤ -γmargin ∨ 1 - 2 * mIn rho / rho ≤ δ - γmargin) ∧
      (∃ u ∈ Icc 0 K, (u, 0) ∈ sidewaysTruncation Q E (-K) K rho Lzero ∧
        Q.r u 0 = rho ∧ u ≤ (Lzero - rho) / c ∧
        sidewaysTriangle 0 u ⊆ sidewaysTruncation Q E (-K) K rho Lzero) ∧
      (∀ t ∈ Icc (-K) K,
        (U t, V t) ∈ sidewaysTruncation P D (-T * L / 2) (T * L / 2) Lzero L ∧
        P.r (U t) (V t) = Lzero ∧ deriv (U : ℝ → ℝ) t ∈ Icc 1 (1 / (2 * c)) ∧
        |P.A (U t) (V t)| ≤ Cp / Lzero) ∧
      (∀ p ∈ sidewaysTruncation Q E (-K) K rho Lzero,
        |Q.A p.1 p.2| ≤ Cpotential ∧
        |(s * e) * Q.A p.1 p.2| * (1 + ‖H‖) ≤ Cpotential * eta / L ∧
        Q.A p.1 p.2 = deriv (U : ℝ → ℝ) p.1 * P.A (U p.1) (V p.2) ∧
        deriv (U : ℝ → ℝ) p.1 ∈ Icc 1 (1 / (2 * c))) ∧
      |s * e| * L * (1 + ‖H‖) = eta ∧
      (∀ p ∈ sidewaysTruncation Q E (-K) K rho Lzero,
        (U p.1, V p.2) ∈ sidewaysTruncation P D (-T * L / 2) (T * L / 2) rStar L ∧
        δ ≤ 1 - Q.mu p.1 p.2) ∧
      ∀ p ∈ sidewaysTruncation Q E (-K) K rho Lzero,
        let r := Q.r p.1 p.2
        let k := (Q.mu p.1 p.2 - Q.Q p.1 p.2 ^ 2 / r ^ 2) / (1 - Q.mu p.1 p.2)
        let ks := (2 * mIn r / r - q ^ 2 / r ^ 2) / (1 - 2 * mIn r / r)
        let electric := I * (s * e) * Q.Q p.1 p.2 * Q.phi p.1 p.2 / ((1 - Q.mu p.1 p.2) * r : ℝ)
        let potential := I * (s * e) * Q.A p.1 p.2 * yIn r
        |k - ks| ≤ Cg * (|massComparison Q mIn p.1 p.2| + eta) ∧
        ‖electric‖ + ‖potential‖ ≤ Ce * eta ∧
        ‖electric‖ ≤ Ce * eta ∧ ‖potential‖ ≤ Ce * eta := by
  obtain ⟨Lmin, hLmin, hrecord⟩ := inner_record_of_geometry_and_core 41 (by norm_num)
  obtain ⟨Lclose, CmOuter, hLclose, hCmOuter, hcloseOuter⟩ :=
    outer_comparison_of_normalization 41 (by norm_num)
  obtain ⟨Cp, hCp, hpotentialOuter⟩ := outer_controls_of_normalization 41 (by norm_num)
  obtain ⟨Lzero, rStar, γmargin, Cref, hLzero, hLminZero, h128, hrStar, hrStarL,
    hmargin, hCref, hreferences⟩ := uniform_radial_references δ (max Lmin Lclose) hδ
  have hL1 : 1 ≤ Lzero := (by norm_num : (1 : ℝ) ≤ 128).trans h128
  obtain ⟨Ccore, ηcore, hCcore, hηcore, hcore⟩ := calibrated_core_of_failed_observation hδ.1
  obtain ⟨ηouter, hηouter, houter⟩ := source_outer_data_of_reference hδ.1 41 (by norm_num)
  obtain ⟨ηbox, hηbox, hbox⟩ := calibrated_chart_box_of_failed_observation hδ.1
  obtain ⟨c, K, T, ηwindow, Cwindow, hc, hK, hT, hηwindow, hCwindow, hwindow⟩ :=
    comparison_window hδ.1 hrStar hrStarL
  obtain ⟨Ct, Couter, hCt, hCouter, houter⟩ := houter T hT
  obtain ⟨CcoreCap, hCcoreCap, hcore⟩ := hcore T hT
  obtain ⟨Cbox, hCbox, hbox⟩ := hbox T hT
  obtain ⟨CB, CE, Cq, Ctheta, Cmass, Cxi, Bcharge, Amax, Cscalar, Qmax,
    hCB, hCE, hCq, hCtheta, hCmass, hCxi, hBcharge, hAmax, hCscalar, hQmax, hrecord⟩ :=
    hrecord Ct hCt δ rStar Lzero c K Ccore hδ.1 hrStar hrStarL
      ((le_max_left _ _).trans hLminZero) hc hK.le hCcore.le
  obtain ⟨CBp, CEp, Cqp, hCBp, hCEp, hCqp, hcloseOuter⟩ := hcloseOuter Ct Ct hCt.le hCt.le
  obtain ⟨CqPotential, hCqPotential, hpotentialOuter⟩ := hpotentialOuter Ct hCt.le
  let CqAll := max Cq (max Cqp CqPotential)
  have hCqAll : 0 < CqAll := hCq.trans_le (le_max_left _ _)
  let delta := min δ (1 / (Cref + 1))
  have hdelta : 0 < delta := lt_min hδ.1 (by positivity)
  let cap := 1 / (16 * (CB + CE + CBp + CEp + 1))
  have hcap : 0 < cap := by dsimp [cap]; positivity
  let εcap := min (1 / Cwindow) (min (1 / Couter)
    (min (1 / CcoreCap) (min (1 / Cbox) cap)))
  have hεcap : 0 < εcap := by dsimp [εcap]; positivity
  let ηcap := min ηwindow (min ηouter (min ηcore (min ηbox (min (1 / CqAll) cap))))
  have hηcap : 0 < ηcap := by dsimp [ηcap]; positivity
  obtain ⟨A, Bsrc, Echarge, Cm, Cz, Cv, Cclose, sigma,
    hA, hBsrc, hEcharge, hCm, hCz, hCv, hCclose, hsigma, hestimates⟩ :=
    inner_conclusions_of_normalization rStar Lzero delta c Cref (1 + 2 * Cref ^ 2)
      Qmax Cscalar Bcharge Amax Ctheta Cmass Cxi
      hrStar hrStarL hdelta hc hCref.le (by positivity) hQmax.le hCscalar.le
      hBcharge.le hAmax.le hCtheta.le hCmass.le hCxi.le
  obtain ⟨Cpotential, hCpotential, hpotential⟩ := inner_ordinary_potential_of_normalization
    rStar delta Qmax (Cp / (2 * c * Lzero)) hrStar hdelta hQmax.le (by positivity)
  obtain ⟨Cg, Ce, hCg, hCe, hsources⟩ := inner_individual_sources_of_normalization
    rStar delta Cref Qmax Cscalar Bcharge Amax hrStar hdelta hCref.le
      hQmax.le hCscalar.le hBcharge.le hAmax.le
  let εc := min εcap (sigma / 4)
  let ηstar := min ηcap (sigma / 4)
  have hεc : 0 < εc := lt_min hεcap (by positivity)
  have hηstar : 0 < ηstar := lt_min hηcap (by positivity)
  have hηstarCap : ηstar ≤ ηcap := min_le_left _ _
  refine ⟨T, ηstar, Lzero, εc, rStar, c, K, Cref, delta, Ct,
    Qmax, Cscalar, Bcharge, Amax, Ctheta, Cmass, Cxi,
    A, Bsrc, Echarge, Cm, Cz, Cv, Cclose, sigma, γmargin, Cp, Cpotential, Cg, Ce,
    hT, hηstar, hL1, hεc, hrStar, hrStarL, hc, hK, hCref, hdelta,
    hCt, hQmax, hCscalar, hBcharge, hAmax, hCtheta, hCmass, hCxi,
    hA, hBsrc, hEcharge, hCm, hCz, hCv, hCclose, hsigma, hmargin, hCp, hCpotential, hCg, hCe, ?_⟩
  intro ε hε hεSmall
  have hεCap : ε ≤ εcap := hεSmall.trans (min_le_left _ _)
  have hεCaps : ε ≤ 1 / Cwindow ∧ ε ≤ 1 / Couter ∧ ε ≤ 1 / CcoreCap ∧
      ε ≤ 1 / Cbox ∧ ε ≤ cap := by
    simpa only [εcap, le_min_iff] using hεCap
  obtain ⟨Cw, hCw, hwindow⟩ := hwindow ε hε hεCaps.1
  obtain ⟨Co, hCo, houter⟩ := houter ε hε hεCaps.2.1
  obtain ⟨Cc, hCc, hcore⟩ := hcore ε hε hεCaps.2.2.1
  obtain ⟨Cb, hCb, hbox⟩ := hbox ε hε hεCaps.2.2.2.1
  let Cobs := max Cw (max Co (max Cc Cb))
  refine ⟨Cobs, hCw.trans_le (le_max_left _ _), ?_⟩
  intro ui e b s τ₀ S h γ hb hs hL hscale hgap hcharged hfailure
  have hηCaps : (|e| * b * (1 + ‖S.a (γ.U τ₀) (γ.V τ₀)‖) ≤ ηwindow) ∧
      (|e| * b * (1 + ‖S.a (γ.U τ₀) (γ.V τ₀)‖) ≤ ηouter) ∧
      (|e| * b * (1 + ‖S.a (γ.U τ₀) (γ.V τ₀)‖) ≤ ηcore) ∧
      (|e| * b * (1 + ‖S.a (γ.U τ₀) (γ.V τ₀)‖) ≤ ηbox) ∧
      (|e| * b * (1 + ‖S.a (γ.U τ₀) (γ.V τ₀)‖) ≤ 1 / CqAll) ∧
      (|e| * b * (1 + ‖S.a (γ.U τ₀) (γ.V τ₀)‖) ≤ cap) := by
    simpa only [ηcap, le_min_iff] using hcharged.trans hηstarCap
  have hsb : s ≤ b := by simpa only [one_mul] using (le_div_iff₀ hs).mp (hL1.trans hL)
  have hcentralScale : S.m (γ.U τ₀) (γ.V τ₀) + b *
      ‖S.theta (γ.U τ₀) (γ.V τ₀) / S.lam (γ.U τ₀) (γ.V τ₀)‖ ≤ s := by
    rw [hscale]; exact le_add_of_nonneg_right (abs_nonneg _)
  obtain ⟨χ, hχ, hχ0, hχd, F, G, U, V, hF, hG, hFi, hGi, hFp, hGp,
    hU, hV, hUi, hVi, hUp, hVp, hcalWindow, hboundary, himage, htest⟩ :=
    hwindow ui e b s τ₀ S h γ hb hs hsb hL hcentralScale hgap hηCaps.1
      (failure_mono (le_max_left _ _) hfailure)
  let L := b / s
  let B := gaugeFields e S χ
  let H := B.a (γ.U τ₀) (γ.V τ₀)
  let M := S.m (γ.U τ₀) (γ.V τ₀) / s
  let Pzero := -(L : ℂ) * (B.theta (γ.U τ₀) (γ.V τ₀) / B.lam (γ.U τ₀) (γ.V τ₀))
  let q := S.Q (γ.U τ₀) (γ.V τ₀) / s
  let eta := |s * e| * L * (1 + ‖H‖)
  let P := nullPullback (rescaleFields B s) F G
  let D := {p : ℝ × ℝ | (s * F p.1, s * G p.2) ∈ origDomain ui}
  let Q := nullPullback P U V
  let E := {p : ℝ × ℝ | (U p.1,V p.2) ∈ D}
  let a := -T * L / 2
  let z := T * L / 2
  have hcal (x) (hx : τ₀ + s * x / 2 ∈ Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2)) := by
    have hid : s * (T * L) = T * b := by dsimp [L]; field_simp
    have hx' : x ∈ Icc (-T * L) (T * L) := by
      constructor <;> nlinarith only [hx.1, hx.2, hid, hs]
    exact hcalWindow x hx'
  have hτ : τ₀ ∈ Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2) := by
    constructor <;> nlinarith only [mul_pos hT hb]
  have hcentral := central_parameters_of_physical_scale h γ hb hs hτ χ hscale
  have hH : ‖H‖ = ‖S.a (γ.U τ₀) (γ.V τ₀)‖ := by
    rw [show H = B.a (γ.U τ₀) (γ.V τ₀) from rfl, gauge_normalized_out,
      norm_mul, norm_gauge_phase, one_mul]
  have hetaEq : eta = |e| * b * (1 + ‖S.a (γ.U τ₀) (γ.V τ₀)‖) := by
    rw [show eta = |s * e| * (b / s) * (1 + ‖H‖) from rfl, co_eta _ _ _ _ hs, hH]
  have hetaCore : |e| * b * (1 + ‖H‖) ≤ ηcore := by rw [hH]; exact hηCaps.2.2.1
  have hetaBox : |e| * b * (1 + ‖H‖) ≤ ηbox := by rw [hH]; exact hηCaps.2.2.2.1
  obtain ⟨rho, hrho, phiOut, yOut, mOut, yIn, mIn, hstaticOut, hstaticIn, hyMatch, hmMatch, hbar⟩ :=
    hreferences L M q Pzero hL hcentral.1 hcentral.2.1
  obtain ⟨ho, cIncoming, hIncoming⟩ := houter ui e b s τ₀ Lzero S h γ χ F G hb hs hsb h128 hL
    hscale hχ hχd hχ0 hF hG hFp hGp hcal hgap hηCaps.2.1
    (failure_mono ((le_max_left _ _).trans (le_max_right _ _)) hfailure)
    phiOut yOut mOut hstaticOut
  have core := hcore ui e b s τ₀ S h γ χ F G hb hs hsb hχ hχd hχ0 hcal hcentralScale hgap hetaCore
    (failure_mono ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))) hfailure)
    rStar hrStar
  have optical := hbox ui e b s τ₀ S h γ χ hb hs hsb hχ hχd hχ0 hcentralScale hgap hetaBox
    (failure_mono ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))) hfailure)
    F G hcal rStar hrStar
  obtain ⟨_compactOld, htriOld, fieldsOld, eqOld, diagOld⟩ :=
    source_chart_geometry_of_calibration h.solution hb hs hT hrStar (hrStarL.trans hL)
      γ χ hχ F G hF hG hFp hGp hcal hχd
  rcases fieldsOld with ⟨cr, cn, cl, cA, cphi, ctheta, cm, cQ, cxi⟩
  have hbInner (t) (ht : t ∈ Icc (-K) K) := hboundary t ht
  obtain ⟨hcompact, htri, fieldsInner, boxInner, eqInner⟩ :=
    source_inner_geometry_of_window (δ := delta) h.solution hs
      (hrStar.trans_le hrho.1) hK.le χ hχ F G U V
      hF hG hU hV hUp hVp
      (fun t ht => ⟨(hbInner t ht).1, (hbInner t ht).2.1,
        (hbInner t ht).2.2.2.2.1, (hbInner t ht).2.2.2.2.2.1⟩)
      (himage rho hrho)
      (fun p hp => by
        rcases core p hp with ⟨_hr, hm, hg, _hphi, _hQ, _hrel, _hn, _hl, hmix⟩
        exact ⟨hm, (min_le_left δ (1 / (Cref + 1))).trans hg, hmix, eqOld p hp⟩)
  have hεeta : 4 * (CB * ε + CE * eta) ≤ 1 / 2 := by
    have hetaCap : eta ≤ cap := by rw [hetaEq]; exact hηCaps.2.2.2.2.2
    have hh := add_le_add (mul_le_mul_of_nonneg_left hεCaps.2.2.2.2 hCB.le)
      (mul_le_mul_of_nonneg_left hetaCap hCE.le)
    have hsum : 4 * (CB * cap + CE * cap) ≤ 1 / 2 := by
      dsimp [cap]
      field_simp
      nlinarith only [hCB, hCE, hCBp, hCEp]
    exact (mul_le_mul_of_nonneg_left hh (by norm_num)).trans hsum
  have hchargeAll : CqAll * eta ≤ 1 := by
    have hh : eta ≤ 1 / CqAll := by rw [hetaEq]; exact hηCaps.2.2.2.2.1
    simpa only [mul_comm] using (le_div_iff₀ hCqAll).mp hh
  have hcharge : Cq * eta ≤ 1 :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) ho.errors.2.1).trans hchargeAll
  have inner := hrecord P D H Pzero phiOut yOut yIn mOut mIn a z L ε eta q (s * e)
    rho delta Cref (1 + 2 * Cref ^ 2) U V ho hεeta hcharge hrho.1 hrho.2 hU hUi hUp hVp
    (fun t ht => ⟨(hbInner t ht).1, (hbInner t ht).2.1, (hbInner t ht).2.2.1.2,
      (hbInner t ht).2.2.2.2.1, (hbInner t ht).2.2.2.2.2.1⟩)
    (fun p hp => (himage rho hrho p hp).1) htriOld ⟨cr, cl, cA, cn, cQ, cm⟩
    (fun p hp => ⟨(eqOld p hp).1.1, (eqOld p hp).1.2.2.2.2.1⟩)
    (fun t ht => (diagOld t ⟨ht.1.2.1, ht.1.2.2.2⟩).2.2.2.2)
    (fun p hp => by
      rcases core p hp with ⟨_hr, hm, hg, hphi, hQ, hrel, hn, hl, _hmix⟩
      exact ⟨hm, hg, hl.le, by rw [abs_of_neg hn]; exact (optical p hp).1.2,
        hrel, hphi, hQ⟩)
    hcompact htri fieldsInner boxInner eqInner hstaticIn.1 hstaticIn.2.1
    (fun r hr => ⟨(hstaticIn.2.2.1 r hr).1,
      (min_le_right _ _).trans (hstaticIn.2.2.1 r hr).2.1, (hstaticIn.2.2.1 r hr).2.2⟩)
    hstaticIn.2.2.2 hyMatch hmMatch
    ((cIncoming.norm.pow 2).intervalIntegrable_of_Icc (by
      dsimp [a, z, L]
      nlinarith only [mul_nonneg hT.le (div_pos hb hs).le])) hIncoming
  have hsmallInner : ε + eta ≤ sigma := by
    have hepsSigma : ε ≤ sigma / 4 := hεSmall.trans (min_le_right _ _)
    have hetaSigma : eta ≤ sigma / 4 := by
      rw [hetaEq]
      exact hcharged.trans (min_le_right _ _)
    linarith only [hepsSigma, hetaSigma, hsigma]
  have hsmallPotential : 4 * (CBp * ε + CEp * eta) ≤ 1 / 2 := by
    have hetaCap : eta ≤ cap := by rw [hetaEq]; exact hηCaps.2.2.2.2.2
    have hh := add_le_add (mul_le_mul_of_nonneg_left hεCaps.2.2.2.2 hCBp.le)
      (mul_le_mul_of_nonneg_left hetaCap hCEp.le)
    have hsum : 4 * (CBp * cap + CEp * cap) ≤ 1 / 2 := by
      dsimp [cap]
      field_simp
      nlinarith only [hCB, hCE, hCBp, hCEp]
    exact (mul_le_mul_of_nonneg_left hh (by norm_num)).trans hsum
  have hclosed := hcloseOuter P D H Pzero phiOut yOut mOut a z Lzero L ε eta q (s * e)
    ((le_max_right _ _).trans hLminZero) ho.ordered ho.errors.1.1 ho.errors.1.2
    ho.errors.2.1 ho.errors.2.2 hsmallPotential
    ((mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _))
      ho.errors.2.1).trans hchargeAll)
    ho.reference_charge ho.scale ho.compact ho.fields ho.static_mass_ac
    ho.static_continuous.1 ho.static_continuous.2 ho.static_boundary.1 ho.static_boundary.2
    ho.static_equations ho.static_bounds ho.base ho.triangles ho.box ho.equations ho.boundary
  have hstopPotential : comparisonNorm (sidewaysTruncation P D a z Lzero L)
      (scalarComparison P H phiOut) ≤ 1 := hclosed.1.trans (by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal
      (hsmallPotential.trans (by norm_num : (1 / 2 : ℝ) ≤ 1)))
  have hpotOuter := hpotentialOuter P D H Pzero phiOut yOut mOut a z Lzero L ε eta q (s * e) Ct
    ho hL1
    ((mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _))
      ho.errors.2.1).trans hchargeAll)
    hstopPotential
  have hboundaryPotential (t) (ht : t ∈ Icc (-K) K) : |Q.A t t| ≤ Cp / (2 * c * Lzero) := by
    have hb := hboundary t ht
    have hA := (hpotOuter _ hb.1).2.2.1
    rw [hb.2.1] at hA
    change |deriv (U : ℝ → ℝ) t * P.A (U t) (V t)| ≤ _
    rw [abs_mul, abs_of_pos (hUp t)]
    exact (mul_le_mul hb.2.2.1.2 hA (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hpotentialEq (p) (hp : p ∈ sidewaysTruncation Q E (-K) K rho Lzero) :
      HasDerivAt (Q.A p.1) (Q.AV p.1 p.2) p.2 := by
    have hh := nullPullback_equations P U V (s * e) p.1 p.2
      (deriv (U : ℝ → ℝ) p.1) (deriv (V : ℝ → ℝ) p.2)
      (hU.differentiable (by norm_num) p.1).hasDerivAt
      (hV.differentiable (by norm_num) p.2).hasDerivAt (hUp _) (hVp _)
      (eqOld _ (himage rho hrho p hp).1).1 (eqOld _ (himage rho hrho p hp).1).2
    exact hh.1.2.2.2.2.1
  have hpot := hpotential rho Lzero c Cref (1 + 2 * Cref ^ 2) Cscalar Bcharge Amax
    Q E H yIn mIn (-K) K q (s * e) eta (Ctheta * (ε + eta))
      (Cmass * (ε + eta)) (Cxi * (ε + eta)) L hrho.1 hc (div_pos hb hs)
      inner hboundaryPotential hpotentialEq ho.scale
  refine ⟨χ, F, G, U, V, rho, phiOut, yOut, mOut, yIn, mIn,
    hrho, hyMatch, hmMatch, ho, inner,
    hestimates rho Q E H yIn mIn (-K) K q (s * e) ε eta
      hrho.1 hrho.2 hε.le inner hsmallInner,
    hstaticOut.2.2.2.1, hstaticIn, hbar, htest rho hrho, ?_, ?_, ho.scale, ?_, ?_⟩
  · intro t ht
    have hb := hboundary t ht
    have hA := (hpotOuter _ hb.1).2.2.1
    rw [hb.2.1] at hA
    exact ⟨hb.1, hb.2.1, hb.2.2.1, hA⟩
  · intro p hp
    exact ⟨(hpot p hp).1, (hpot p hp).2, rfl,
      (hboundary p.1 ⟨hp.1.2.1.trans hp.1.2.2.1, hp.1.2.2.2⟩).2.2.1⟩
  · intro p hp
    have him := (himage rho hrho p hp).1
    exact ⟨him, (core _ him).2.2.1⟩
  · simpa only [Complex.ofReal_mul] using
      hsources rho Lzero c (1 + 2 * Cref ^ 2) Q E H yIn mIn (-K) K q (s * e) eta
        (Ctheta * (ε + eta)) (Cmass * (ε + eta)) (Cxi * (ε + eta)) hrho.1 inner

end EmcsfAcExtension.Global.Observation
