module

public import EmcsfAcExtension.Global.Observation.WrappersControls
import EmcsfAcExtension.Global.Observation.SourceOuterReference
import EmcsfAcExtension.Global.Observation.Static.OuterReference
import EmcsfAcExtension.Global.Observation.WrappersElectric
import EmcsfAcExtension.Global.Observation.OuterClosure
import EmcsfAcExtension.Global.Observation.Gauge
import Mathlib

/-! # Source-setting wrappers for the complete outer comparison chain

The original solution supplies the actual gauged, scaled and calibrated chart.
All normalization, reference, boundary and estimate premises are discharged.
Source: charged_SF_new_version.tex:L2348–2544; approved internal project record; internal project
record repairs.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global.Observation

/-- [node prop:charged-observation#outer-bootstrap-box]
[node eq:co-maxwell-ibp]
[node eq:co-charge-improved]
[node eq:co-potential]
[node eq:co-shifted-wave]
[node eq:co-wv-exact]
[node eq:co-source-envelope]
[node prop:charged-observation#electric-source-integrals]
[node eq:co-outer-y]
[node eq:co-mass-difference]
[node prop:charged-observation#backward-mass-integrating-factor]
[node eq:co-electric-mass-error]
[node eq:co-outer-close]
[node prop:charged-observation#outer-domain-continuation]
The outer chain on the actual normalized comparison setting. Universal
reference, neutral, radial and continuation constants are fixed first.
Boundary and electric coefficients depend additionally on `δ,T`. Positive
tolerances are selected after `Lzero`, before every physical solution,
scale, coupling, scalar background and radius. Both norms are closed on the
whole region with scalar norm at most `1/2`; the stopped conclusion also
exports both polynomials, the separate component inequalities, the literal
derivatives, Maxwell identity, weighted integral, electric mass integral
and both characteristic electric integrations. No normalization record,
reference bound or comparison estimate is a premise. -/
theorem outer_comparison_chain :
    ∃ Kstatic Lref Cp Cn Cnc CnM Cem Cm : ℝ,
      0 < Kstatic ∧ 0 < Lref ∧ 0 < Cp ∧ 0 < Cn ∧ 0 < Cnc ∧ 0 < CnM ∧ 0 < Cem ∧ 0 < Cm ∧
    ∀ δ : ℝ, 0 < δ → ∀ T : ℝ, 0 < T →
    ∃ Ct Cq Ce Cec CbM CeM CB CE : ℝ,
      0 < Ct ∧ 0 < Cq ∧ 0 < Ce ∧ 0 < Cec ∧ 0 < CbM ∧ 0 < CeM ∧ 0 < CB ∧ 0 < CE ∧
    ∀ Lzero : ℝ, Lref ≤ Lzero → ∃ εc ηc : ℝ, 0 < εc ∧ 0 < ηc ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ εc → ∃ Cobs : ℝ, 0 < Cobs ∧
    ∀ (ui e b s τ₀ : ℝ) (S : Fields) (_h : OriginalData ui e S)
      (γ : ClockCylinder S (origDomain ui) b (τ₀ - T * b / 2) (τ₀ + T * b / 2))
      (χ : ℝ → ℝ) (F G : ℝ ≃o ℝ),
    let B := gaugeFields e S χ
    let L := b / s
    let H := B.a (γ.U τ₀) (γ.V τ₀)
    let _M := S.m (γ.U τ₀) (γ.V τ₀) / s
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
      OuterNormalizationData Kstatic Ct Ct P D H Pzero phiStar yStar mStar
        a z Lzero L ε eta q (s * e) ∧
      outerExact P D H phiStar yStar mStar a z Lzero L ε q (s * e) Ct ∧
      outerRadial P D H a z Lzero L (s * e) ∧
      outerStopped Kstatic Cp Cq Cn Ce Cnc Cec CnM CbM CeM Cem
        P D H phiStar yStar mStar a z Lzero L ε eta q (s * e) Ct ∧
      (∀ p ∈ sidewaysTruncation P D a z Lzero L,
        ((∫ r in (P.r p.1 p.2)..L, eta / r ^ 3) ≤ eta / (2 * P.r p.1 p.2 ^ 2) ∧
         (∫ r in (P.r p.1 p.2)..L, eta / r ^ 3 + eta / L * Real.log (L / r)) ≤
           eta / (2 * P.r p.1 p.2 ^ 2) + eta) ∧
        ((∫ u in p.2..p.1, eta / P.r u p.2 ^ 4 + eta / (L * P.r u p.2)) ≤
           8 * eta / P.r p.1 p.2 ^ 3 + 8 * eta / L * Real.log (L / P.r p.1 p.2)) ∧
        (∫⁻ v in Icc p.2 p.1, ∫⁻ u in Icc v p.1,
          ENNReal.ofReal (eta / P.r u v ^ 4 + eta / (L * P.r u v))) ≤ ENNReal.ofReal (96 * eta)) ∧
      (4 * (CB * ε + CE * eta) ≤ 1 / 2 ∧
       comparisonNorm (sidewaysTruncation P D a z Lzero L) (scalarComparison P H phiStar) ≤
         ENNReal.ofReal (4 * (CB * ε + CE * eta)) ∧
       comparisonNorm (sidewaysTruncation P D a z Lzero L) (massComparison P mStar) ≤
         ENNReal.ofReal (Cm * (CB * ε + CE * eta) / Lzero)) ∧
      comparisonNorm (sidewaysTruncation P D a z Lzero L) (scalarComparison P H phiStar) ≤
        ENNReal.ofReal (1 / 2) ∧
      comparisonNorm (sidewaysTruncation P D a z Lzero L) (scalarComparison P H phiStar) ≤
        ENNReal.ofReal (4 * (CB + CE) * (ε + eta)) ∧
      comparisonNorm (sidewaysTruncation P D a z Lzero L) (massComparison P mStar) ≤
        ENNReal.ofReal (Cm * (CB + CE) * (ε + eta) / Lzero) := by
  obtain ⟨Lstatic, Kstatic, hLs, hKs, href⟩ := outer_radial_reference
  obtain ⟨Cp, Cn, Cnc, CnM, Cem, hCp, hCn, hCnc, hCnM, hCem, hstopped⟩ :=
    outer_stopped_of_normalization Kstatic hKs.le
  obtain ⟨Lclose, Cm, hLc, hCm, hclose⟩ := outer_comparison_of_normalization Kstatic hKs.le
  let Lref := max 128 (max Lstatic Lclose)
  have hLref : 0 < Lref := (by norm_num : (0 : ℝ) < 128).trans_le (le_max_left _ _)
  refine ⟨Kstatic, Lref, Cp, Cn, Cnc, CnM, Cem, Cm, hKs, hLref,
    hCp, hCn, hCnc, hCnM, hCem, hCm, ?_⟩
  intro δ hδ T hT
  obtain ⟨ηsource, hηsource, hsource⟩ := source_outer_data_of_reference hδ Kstatic hKs
  obtain ⟨Ct, Ccap, hCt, hCcap, hsource⟩ := hsource T hT
  obtain ⟨CqS, Ce, Cec, CbM, CeM, hCqS, hCe, hCec, hCbM, hCeM, hstopped⟩ :=
    hstopped Ct Ct hCt.le hCt.le
  obtain ⟨CB, CE, CqC, hCB, hCE, hCqC, hclose⟩ := hclose Ct Ct hCt.le hCt.le
  let Cq := max CqS CqC
  have hCq : 0 < Cq := hCqS.trans_le (le_max_left _ _)
  refine ⟨Ct, CqS, Ce, Cec, CbM, CeM, CB, CE,
    hCt, hCqS, hCe, hCec, hCbM, hCeM, hCB, hCE, ?_⟩
  intro Lzero hLzero
  let cap := 1 / (16 * (CB + CE + 1))
  have hcap : 0 < cap := by dsimp [cap]; positivity
  let εc := min (1 / Ccap) cap
  let ηc := min ηsource (min cap (1 / Cq))
  have hεc : 0 < εc := lt_min (by positivity) hcap
  have hηc : 0 < ηc := lt_min hηsource (lt_min hcap (by positivity))
  refine ⟨εc, ηc, hεc, hηc, ?_⟩
  intro ε hε hεc'
  obtain ⟨Cobs, hCobs, hsource⟩ := hsource ε hε (hεc'.trans (min_le_left _ _))
  refine ⟨Cobs, hCobs, ?_⟩
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
  have hLstatic : Lstatic ≤ Lzero := (le_max_left _ _).trans ((le_max_right _ _).trans hLzero)
  have hLclose : Lclose ≤ Lzero := (le_max_right _ _).trans ((le_max_right _ _).trans hLzero)
  have hL1 : 1 ≤ Lzero := (by norm_num : (1 : ℝ) ≤ 128).trans h128
  have hLp : 0 < Lzero := zero_lt_one.trans_le hL1
  have htime : τ₀ ∈ Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2) := by
    constructor <;> nlinarith only [mul_pos hT hb]
  have central := central_parameters_of_physical_scale h γ hb hs htime χ hscale
  obtain ⟨phiStar, yStar, mStar, hstatic⟩ := href Lzero L M q Pzero hLstatic hL central.1
      central.2.1
  obtain ⟨ho, _traceCont, _traceBound⟩ := hsource ui e b s τ₀ Lzero S h γ χ F G
    hb hs hsb h128 hL hscale hχ hχd hχ0 hF hG hFp hGp hcal hgap
    (hcharged.trans (min_le_left _ _)) hfailure phiStar yStar mStar hstatic
  have hH : ‖H‖ = ‖S.a (γ.U τ₀) (γ.V τ₀)‖ := by
    rw [show H = B.a (γ.U τ₀) (γ.V τ₀) from rfl,
      gauge_normalized_out, norm_mul, norm_gauge_phase, one_mul]
  have hetaEq : eta = |e| * b * (1 + ‖S.a (γ.U τ₀) (γ.V τ₀)‖) := by
    rw [show eta = |s * e| * (b / s) * (1 + ‖H‖) from rfl, co_eta _ _ _ _ hs, hH]
  have hetaCap : eta ≤ cap :=
      by rw [hetaEq]; exact hcharged.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcharge : Cq * eta ≤ 1 := by
    have hh : eta ≤ 1 / Cq :=
        by rw [hetaEq]; exact hcharged.trans ((min_le_right _ _).trans (min_le_right _ _))
    simpa only [mul_comm] using (le_div_iff₀ hCq).mp hh
  have hsmall : 4 * (CB * ε + CE * eta) ≤ 1 / 2 := by
    have hh := add_le_add (mul_le_mul_of_nonneg_left (hεc'.trans (min_le_right _ _)) hCB.le)
      (mul_le_mul_of_nonneg_left hetaCap hCE.le)
    have hs : 4 * (CB * cap + CE * cap) ≤ 1 / 2 := by
      dsimp only [cap]
      field_simp
      nlinarith only [hCB, hCE]
    exact (mul_le_mul_of_nonneg_left hh (by norm_num)).trans hs
  have hclosed := hclose P D H Pzero phiStar yStar mStar a z Lzero L ε eta q (s * e)
    hLclose ho.ordered ho.errors.1.1 ho.errors.1.2 ho.errors.2.1 ho.errors.2.2 hsmall
    ((mul_le_mul_of_nonneg_right (le_max_right _ _) ho.errors.2.1).trans hcharge)
    ho.reference_charge ho.scale ho.compact ho.fields ho.static_mass_ac
    ho.static_continuous.1 ho.static_continuous.2 ho.static_boundary.1 ho.static_boundary.2
    ho.static_equations ho.static_bounds ho.base ho.triangles ho.box ho.equations ho.boundary
  refine ⟨phiStar, yStar, mStar, ho, outer_exact_of_normalization hLp ho,
    outer_radial_of_normalization hLp ho,
    hstopped P D H Pzero phiStar yStar mStar a z Lzero L ε eta q (s * e) ho hL1
      ((mul_le_mul_of_nonneg_right (le_max_left _ _) ho.errors.2.1).trans hcharge),
    ?_, ⟨hsmall, hclosed⟩, hclosed.1.trans (ENNReal.ofReal_le_ofReal hsmall), ?_, ?_⟩
  · intro p hp
    exact ⟨electric_second_integrals (hLp.trans_le hp.2.1) hp.2.2 ho.errors.2.1,
      electric_triangle_of_normalization hL1 ho p hp⟩
  · apply hclosed.1.trans (ENNReal.ofReal_le_ofReal ?_)
    have hh : CB * ε + CE * eta ≤ (CB + CE) * (ε + eta) := by
      nlinarith only [mul_nonneg hCB.le ho.errors.2.1, mul_nonneg hCE.le hε.le]
    nlinarith only [hh]
  · apply hclosed.2.trans (ENNReal.ofReal_le_ofReal ?_)
    apply div_le_div_of_nonneg_right _ hLp.le
    have hh : CB * ε + CE * eta ≤ (CB + CE) * (ε + eta) := by
      nlinarith only [mul_nonneg hCB.le ho.errors.2.1, mul_nonneg hCE.le hε.le]
    nlinarith only [mul_le_mul_of_nonneg_left hh hCm.le]

end EmcsfAcExtension.Global.Observation
