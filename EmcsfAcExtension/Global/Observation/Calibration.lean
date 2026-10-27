module

public import EmcsfAcExtension.Global.Observation.WindowSource
import EmcsfAcExtension.Global.Observation.Gauge
import Mathlib

/-! # Derivatives and values of calibrated observation maps

The calibration holds on the larger source clock window. Its interior
therefore determines ordinary chart derivatives throughout the smaller
comparison window, including that window's closed endpoints.
Source: charged_SF_new_version.tex:L1980–2034; internal project record internal project record.
-/

public section

open Set Filter Topology Complex

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
The defining physical clock calibration determines the actual derivatives
of both normalized coordinate maps at every strict source-clock label.
Only the original clock rates and a positive scale are used. There are
no optical or comparison premises and no estimate constants. -/
theorem calibrated_clock_map_derivatives
    {e ui b a z s τ₀ t : ℝ} {S : Fields}
    (_hS : IsSolution e S (origDomain ui))
    (γ : ClockCylinder S (origDomain ui) b a z) (hs : 0 < s)
    (F G : ℝ → ℝ)
    (hcal : ∀ x : ℝ, τ₀ + s * x / 2 ∈ Icc a z →
      s * F x = γ.U (τ₀ + s * x / 2) ∧ s * G x = γ.V (τ₀ + s * x / 2))
    (ht : τ₀ + s * t / 2 ∈ Ioo a z) :
    HasDerivAt F ((2 * (-S.nu (γ.U (τ₀ + s * t / 2))
      (γ.V (τ₀ + s * t / 2))))⁻¹) t ∧
    HasDerivAt G ((2 * S.lam (γ.U (τ₀ + s * t / 2))
      (γ.V (τ₀ + s * t / 2)))⁻¹) t := by
  let f := fun x : ℝ => τ₀ + s * x / 2
  have df : HasDerivAt f (s / 2) t := by
    simpa only [f, id_eq, mul_one, zero_mul, zero_add] using!
      (((hasDerivAt_id t).const_mul s).div_const 2).const_add τ₀
  have hnb : ∀ᶠ x in 𝓝 t, f x ∈ Ioo a z :=
    df.continuousAt.preimage_mem_nhds (Ioo_mem_nhds ht.1 ht.2)
  have hFeq : F =ᶠ[𝓝 t] fun x => γ.U (f x) / s := by
    filter_upwards [hnb] with x hx
    have he := (hcal x (Ioo_subset_Icc_self hx)).1
    exact (eq_div_iff hs.ne').mpr (by simpa only [mul_comm] using he)
  have hGeq : G =ᶠ[𝓝 t] fun x => γ.V (f x) / s := by
    filter_upwards [hnb] with x hx
    have he := (hcal x (Ioo_subset_Icc_self hx)).2
    exact (eq_div_iff hs.ne').mpr (by simpa only [mul_comm] using he)
  have dF := ((γ.hasDerivAt_U ht).comp t df).div_const s
  have dG := ((γ.hasDerivAt_V ht).comp t df).div_const s
  refine ⟨?_, ?_⟩
  · convert dF.congr_of_eventuallyEq hFeq using 1
    field_simp
  · convert dG.congr_of_eventuallyEq hGeq using 1
    field_simp

/-- [internal]
Every geometric value, expansion normalizer and scalar ratio of a
calibrated actual chart is its literal original value. The derivatives
are derived from calibration on the larger source window. No independent
clock derivatives or transformed solution assertion are supplied.
There are no estimate constants. -/
theorem calibrated_chart_components
    {e ui b a z s τ₀ u v : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui))
    (γ : ClockCylinder S (origDomain ui) b a z) (hs : 0 < s)
    (χ F G : ℝ → ℝ)
    (hcal : ∀ x : ℝ, τ₀ + s * x / 2 ∈ Icc a z →
      s * F x = γ.U (τ₀ + s * x / 2) ∧ s * G x = γ.V (τ₀ + s * x / 2))
    (hu : τ₀ + s * u / 2 ∈ Ioo a z) (hv : τ₀ + s * v / 2 ∈ Ioo a z) :
    let f := fun t => τ₀ + s * t / 2
    let B := gaugeFields e S χ
    let P := nullPullback (rescaleFields B s) F G
    let x := γ.U (f u)
    let y := γ.V (f v)
    P.r u v = S.r x y / s ∧ P.m u v = S.m x y / s ∧
      P.Q u v = S.Q x y / s ∧ P.mu u v = S.mu x y ∧
      P.nu u v = (2 * (-S.nu x (γ.V (f u))))⁻¹ * S.nu x y ∧
      P.lam u v = (2 * S.lam (γ.U (f v)) y)⁻¹ * S.lam x y ∧
      P.phi u v = B.phi x y ∧
      P.theta u v / P.lam u v = B.theta x y / B.lam x y ∧
      P.xi u v / P.nu u v = B.xi x y / B.nu x y ∧
      P.a u v = B.a x y := by
  let f := fun t : ℝ => τ₀ + s * t / 2
  have hvalU : s * F u = γ.U (f u) := (hcal u (Ioo_subset_Icc_self hu)).1
  have hvalV : s * G v = γ.V (f v) := (hcal v (Ioo_subset_Icc_self hv)).2
  have dF := (calibrated_clock_map_derivatives hS γ hs F G hcal hu).1
  have dG := (calibrated_clock_map_derivatives hS γ hs F G hcal hv).2
  have hn : S.nu (γ.U (f u)) (γ.V (f u)) ≠ 0 :=
    (hS.nu_neg _ (γ.mem _ (Ioo_subset_Icc_self hu))).ne
  have hl : S.lam (γ.U (f v)) (γ.V (f v)) ≠ 0 :=
    (hS.lam_pos _ (γ.mem _ (Ioo_subset_Icc_self hv))).ne'
  have hrat := nullPullback_ratios (rescaleFields (gaugeFields e S χ) s) F G dF dG
    (inv_ne_zero (mul_ne_zero (by norm_num) (neg_ne_zero.mpr hn)))
    (inv_ne_zero (mul_ne_zero (by norm_num) hl))
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change S.r (s * F u) (s * G v) / s = _
    rw [hvalU, hvalV]
  · change S.m (s * F u) (s * G v) / s = _
    rw [hvalU, hvalV]
  · change S.Q (s * F u) (s * G v) / s = _
    rw [hvalU, hvalV]
  · rw [nullPullback_mu, rescaleFields_mu _ s _ _ hs, gaugeFields_mu, hvalU, hvalV]
  · change deriv F u * S.nu (s * F u) (s * G v) = _
    rw [dF.deriv, hvalU, hvalV]
  · change deriv G v * S.lam (s * F u) (s * G v) = _
    rw [dG.deriv, hvalU, hvalV]
  · change (gaugeFields e S χ).phi (s * F u) (s * G v) = _
    rw [hvalU, hvalV]
  · simpa only [rescaleFields, hvalU, hvalV] using hrat.1
  · simpa only [rescaleFields, hvalU, hvalV] using hrat.2
  · unfold Fields.a
    rw [hrat.1]
    simp only [nullPullback, rescaleFields, hvalU, hvalV]
    rfl


/-- [internal]
The source optical box on a calibrated actual chart. The only map inputs
are their defining physical clock calibration; all derivative and optical
normalizers are derived internally on the strictly smaller comparison
window. The charged threshold depends only on `δ`, boundary coefficient
on `δ,T`, and failure coefficient on `δ,T,ε`, before all physical data. -/
theorem calibrated_chart_box_of_failed_observation {δ : ℝ} (hδ : 0 < δ) :
    ∃ ηc : ℝ, 0 < ηc ∧
    ∀ T : ℝ, 0 < T → ∃ C : ℝ, 0 < C ∧
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
    ∀ (F G : ℝ → ℝ),
    (∀ x : ℝ, τ₀ + s * x / 2 ∈ Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2) →
      s * F x = γ.U (τ₀ + s * x / 2) ∧ s * G x = γ.V (τ₀ + s * x / 2)) →
    let P := nullPullback (rescaleFields (gaugeFields e S χ) s) F G
    let D := {p : ℝ × ℝ | (s * F p.1, s * G p.2) ∈ origDomain ui}
    ∀ ρ : ℝ, 0 < ρ → ∀ p ∈ sidewaysTruncation P D (-T * (b / s) / 2) (T * (b / s) / 2) ρ (b / s),
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
  obtain ⟨C, hC, hoptics⟩ := hoptics T hT.le
  refine ⟨C, hC, ?_⟩
  intro ε hε hεC
  obtain ⟨Cobs, hCobs, hoptics⟩ := hoptics ε hε hεC
  refine ⟨Cobs, hCobs, ?_⟩
  intro ui e b s τ₀ S h γ χ
  dsimp only
  intro hb hs hsb hχ hχd hχ0 hscale hgap hcharged hfailure F G hcal
  let f := fun t : ℝ => τ₀ + s * t / 2
  let P := nullPullback (rescaleFields (gaugeFields e S χ) s) F G
  intro ρ hρ p hp
  have hpu : p.1 ∈ Icc (-T * (b / s) / 2) (T * (b / s) / 2) :=
    ⟨hp.1.2.1.trans hp.1.2.2.1, hp.1.2.2.2⟩
  have hpv : p.2 ∈ Icc (-T * (b / s) / 2) (T * (b / s) / 2) :=
    ⟨hp.1.2.1, hp.1.2.2.1.trans hp.1.2.2.2⟩
  have strictLabel (x) (hx : x ∈ Icc (-T * (b / s) / 2) (T * (b / s) / 2)) :
      f x ∈ Ioo (τ₀ - T * b / 2) (τ₀ + T * b / 2) := by
    have hx' : x ∈ Icc (-(T / 2) * (b / s)) ((T / 2) * (b / s)) := by
      have hl : -(T / 2) * (b / s) = -T * (b / s) / 2 := by ring
      have hr : (T / 2) * (b / s) = T * (b / s) / 2 := by ring
      rw [hl, hr]
      exact hx
    have hh := normalized_clock_mem (τ₀ := τ₀) hs hx'
    dsimp only [f]
    constructor <;> nlinarith only [hh.1, hh.2, mul_pos hT hb]
  have hu := strictLabel p.1 hpu
  have hv := strictLabel p.2 hpv
  have hUu : s * F p.1 = γ.U (f p.1) := (hcal _ (Ioo_subset_Icc_self hu)).1
  have hVv : s * G p.2 = γ.V (f p.2) := (hcal _ (Ioo_subset_Icc_self hv)).2
  have hc := calibrated_chart_components h.solution γ hs χ F G hcal hu hv
  have hclock : f p.2 ≤ f p.1 := by
    dsimp only [f]
    linarith only [mul_le_mul_of_nonneg_left hp.1.2.2.1 hs.le]
  have hple : γ.U (f p.1) ≤ γ.V (f p.2) := by
    have hh : s * F p.1 ≤ s * G p.2 := hp.1.1.2.2.1
    simpa only [hUu, hVv] using hh
  have hproper : γ.U (f p.1) < γ.V (f p.2) := by
    rcases lt_or_eq_of_le hple with hh | hh
    · exact hh
    · have hmem : (γ.U (f p.1), γ.V (f p.2)) ∈ origDomain ui := by
        have hh' : (s * F p.1, s * G p.2) ∈ origDomain ui := hp.1.1
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
    (f p.2) (Ioo_subset_Icc_self hv) (f p.1) (Ioo_subset_Icc_self hu) hclock hproper ρ hρ hcut
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
