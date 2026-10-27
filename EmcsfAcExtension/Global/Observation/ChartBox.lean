module

public import EmcsfAcExtension.Global.Observation.OpticsExports
public import EmcsfAcExtension.Global.Observation.ClockChart

/-! # Optical and mass boxes on the actual comparison chart

The physical estimates are transported by the actual constructed clock
Jacobians on the entire literal sideways radius truncation.
Source: charged_SF_new_version.tex:L2145–2152, L2518–2544; internal project record (D1)–(D3).
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
The normalized optical/mass/gap box on every actual sideways truncation
from the source-setting optical theorem. Both clock Jacobians and all
core inputs are discharged. The threshold depends only on `δ`; the
boundary constant is chosen after `δ,T`, and failure coefficient after `δ,T,ε`,
before all physical data, gauges, charts and cutoffs. On `ρ ≥ 16` the
box is exactly the one consumed by the landed outer comparison record. -/
theorem chart_box_of_failed_observation {δ : ℝ} (hδ : 0 < δ) :
    ∃ ηc : ℝ, 0 < ηc ∧
    ∀ T : ℝ, 0 ≤ T → ∃ C : ℝ, 0 < C ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / C → ∃ Cobs : ℝ, 0 < Cobs ∧
    ∀ (ui e b s τ₀ : ℝ) (S : Fields) (_h : OriginalData ui e S)
      (γ : ClockCylinder S (origDomain ui) b (τ₀ - T * b / 2) (τ₀ + T * b / 2))
      (χ : ℝ → ℝ),
    let G := gaugeFields e S χ
    let H := G.a (γ.U τ₀) (γ.V τ₀)
    0 < b → 0 < s → s ≤ b →
    ContDiff ℝ 1 χ →
    (∀ τ ∈ Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2),
      HasDerivAt χ (S.A (γ.U τ) (γ.V τ)) (γ.U τ)) →
    χ (γ.U (τ₀ - T * b / 2)) = 0 →
    S.m (γ.U τ₀) (γ.V τ₀) + b *
      ‖S.theta (γ.U τ₀) (γ.V τ₀) / S.lam (γ.U τ₀) (γ.V τ₀)‖ ≤ s →
    (∀ p ∈ triangle (γ.U (τ₀ - T * b / 2)) (γ.V (τ₀ + T * b / 2)),
      δ ≤ 1 - S.mu p.1 p.2) →
    |e| * b * (1 + ‖H‖) ≤ ηc →
    (¬ ENNReal.ofReal (b * (‖S.theta (γ.U τ₀) (γ.V τ₀) /
      S.lam (γ.U τ₀) (γ.V τ₀)‖ ^ 2 + S.mu (γ.U τ₀) (γ.V τ₀) ^ 2)) ≤
      ENNReal.ofReal Cobs * (ENNReal.ofReal (cylinderDissipation S γ.U γ.V
        (τ₀ - T * b / 2) (τ₀ + T * b / 2)) + ENNReal.ofReal b *
        (curveCovVar e S S.a γ.U γ.V (τ₀ - T * b / 2) (τ₀ + T * b / 2)) ^ 2)) →
    ∀ (U V : ℝ ≃o ℝ),
    (∀ τ ∈ Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2), U τ = γ.U τ ∧ V τ = γ.V τ) →
    (∀ τ ∈ Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2),
      HasDerivAt (U : ℝ → ℝ) ((-S.nu (U τ) (V τ))⁻¹) τ) →
    (∀ τ ∈ Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2),
      HasDerivAt (V : ℝ → ℝ) ((S.lam (U τ) (V τ))⁻¹) τ) →
    let f := fun t => τ₀ + s * t / 2
    let P := nullPullback (rescaleFields (gaugeFields e S χ) s)
      (fun t => U (f t) / s) (fun t => V (f t) / s)
    let D := {p : ℝ × ℝ | (U (f p.1), V (f p.2)) ∈ origDomain ui}
    ∀ ρ : ℝ, 0 < ρ → ∀ p ∈ sidewaysTruncation P D (-T * (b / s)) (T * (b / s)) ρ (b / s),
      ((1 / 2 : ℝ) * Real.exp (-(4 / (δ * ρ))) ≤ -P.nu p.1 p.2 ∧
        -P.nu p.1 p.2 ≤ 1 / 2) ∧
      ((1 / 2 : ℝ) * Real.exp (-(4 / (δ * ρ))) ≤ P.lam p.1 p.2 ∧
        P.lam p.1 p.2 ≤ 1 / 2) ∧
      P.m p.1 p.2 ∈ Icc 0 2 ∧ δ ≤ 1 - P.mu p.1 p.2 ∧
      (16 ≤ ρ → P.nu p.1 p.2 ∈ Icc (-(1 / 2)) (-(1 / 8)) ∧
        P.lam p.1 p.2 ∈ Icc (1 / 8) (1 / 2) ∧ P.m p.1 p.2 ∈ Icc 0 2 ∧
        1 / 2 ≤ 1 - P.mu p.1 p.2) := by
  obtain ⟨ηc, hηc, hoptics⟩ := optics_of_failed_observation hδ
  refine ⟨ηc, hηc, ?_⟩
  intro T hT
  obtain ⟨C, hC, hoptics⟩ := hoptics T hT
  refine ⟨C, hC, ?_⟩
  intro ε hε hεC
  obtain ⟨Cobs, hCobs, hoptics⟩ := hoptics ε hε hεC
  refine ⟨Cobs, hCobs, ?_⟩
  intro ui e b s τ₀ S h γ χ
  dsimp only
  intro hb hs hsb hχ hχd hχ0 hscale hgap hcharged hfailure U V heq hUd hVd
  let f := fun t : ℝ => τ₀ + s * t / 2
  let P := nullPullback (rescaleFields (gaugeFields e S χ) s)
    (fun t => U (f t) / s) (fun t => V (f t) / s)
  intro ρ hρ p hp
  have hpu : p.1 ∈ Icc (-T * (b / s)) (T * (b / s)) :=
    ⟨hp.1.2.1.trans hp.1.2.2.1, hp.1.2.2.2⟩
  have hpv : p.2 ∈ Icc (-T * (b / s)) (T * (b / s)) :=
    ⟨hp.1.2.1, hp.1.2.2.1.trans hp.1.2.2.2⟩
  have hu := normalized_clock_mem (τ₀ := τ₀) hs hpu
  have hv := normalized_clock_mem (τ₀ := τ₀) hs hpv
  have hUu : U (f p.1) = γ.U (f p.1) := (heq _ hu).1
  have hVv : V (f p.2) = γ.V (f p.2) := (heq _ hv).2
  have hc := clock_chart_components h.solution γ hs χ U V hu hv heq hUd hVd
  have hclock : f p.2 ≤ f p.1 := by
    dsimp only [f]
    linarith only [mul_le_mul_of_nonneg_left hp.1.2.2.1 hs.le]
  have hple : γ.U (f p.1) ≤ γ.V (f p.2) := by
    have hh : U (f p.1) ≤ V (f p.2) := hp.1.1.2.2.1
    simpa only [hUu, hVv] using hh
  have hproper : γ.U (f p.1) < γ.V (f p.2) := by
    rcases lt_or_eq_of_le hple with hh | hh
    · exact hh
    · have hmem : (γ.U (f p.1), γ.V (f p.2)) ∈ origDomain ui := by
        have hh' : (U (f p.1), V (f p.2)) ∈ origDomain ui := hp.1.1
        simpa only [hUu, hVv] using hh'
      have hz := (h.solution.axis _ (by simpa only [← hh] using hmem)).1
      have hpR : 0 < P.r p.1 p.2 := hρ.trans_le hp.2.1
      rw [hc.1, ← hh, hz, zero_div] at hpR
      exact False.elim (lt_irrefl _ hpR)
  have hcut : s * ρ ≤ S.r (γ.U (f p.1)) (γ.V (f p.2)) := by
    have hh := hp.2.1
    rw [hc.1] at hh
    simpa only [mul_comm] using! (le_div_iff₀ hs).mp hh
  have ho := hoptics ui e b s τ₀ S h γ χ hb hs hsb hχ hχd hχ0 hscale hgap hcharged hfailure
    (f p.2) hv (f p.1) hu hclock hproper ρ hρ hcut
  have hn : -P.nu p.1 p.2 = (2 * (-S.nu (γ.U (f p.1)) (γ.V (f p.1))))⁻¹ *
      (-S.nu (γ.U (f p.1)) (γ.V (f p.2))) := by
    rw [hc.2.2.2.2.1]
    ring
  have hl := hc.2.2.2.2.2.1
  have hm : P.m p.1 p.2 ∈ Icc 0 2 := by rw [hc.2.1]; exact ho.1.1
  have hg : δ ≤ 1 - P.mu p.1 p.2 := by rw [hc.2.2.2.1]; exact ho.1.2.1
  refine ⟨?_, ?_, hm, hg, ?_⟩
  · rw [hn]
    exact ho.2.2.2.1.1
  · rw [hl]
    exact ho.2.2.2.1.2
  · intro hρ16
    have hρ8 : 8 ≤ ρ := (by norm_num : (8 : ℝ) ≤ 16).trans hρ16
    have hslope : 8 / ρ ≤ 1 / 2 := (div_le_iff₀ hρ).mpr (by linarith only [hρ16])
    have hexp := Real.add_one_le_exp (-(8 / ρ))
    have hlower : (1 / 8 : ℝ) ≤ 1 / 2 * Real.exp (-(8 / ρ)) := by
      linarith only [hexp, hslope]
    have houter := ho.2.2.2.2 hρ8
    have hnu : 1 / 8 ≤ -P.nu p.1 p.2 := by rw [hn]; exact hlower.trans houter.1.1
    have hlam : 1 / 8 ≤ P.lam p.1 p.2 := by rw [hl]; exact hlower.trans houter.2.1
    have hnuupper : -P.nu p.1 p.2 ≤ 1 / 2 := by rw [hn]; exact houter.1.2
    have hlamupper : P.lam p.1 p.2 ≤ 1 / 2 := by rw [hl]; exact houter.2.2
    have hr : 0 < P.r p.1 p.2 := hρ.trans_le hp.2.1
    have hmassratio : 2 * P.m p.1 p.2 / P.r p.1 p.2 ≤ 1 / 2 :=
      (div_le_iff₀ hr).mpr (by linarith only [hm.2, hp.2.1, hρ16])
    exact ⟨⟨by linarith only [hnuupper], by linarith only [hnu]⟩,
      ⟨hlam, hlamupper⟩, hm, by simpa only [Fields.mu] using (by linarith only [hmassratio] :
        1 / 2 ≤ 1 - 2 * P.m p.1 p.2 / P.r p.1 p.2)⟩

end EmcsfAcExtension.Global.Observation
