module

public import EmcsfAcExtension.Global.Observation.Calibration
public import EmcsfAcExtension.Global.Observation.CoreExports
import EmcsfAcExtension.Global.Observation.Gauge
import Mathlib

/-! # Core bounds on the actual calibrated comparison domain

Each inward point uses the full outgoing section of its own source
cylinder label. Scalar, charge and signed curvature bounds are obtained
before either comparison stop is removed.
Source: charged_SF_new_version.tex:L2108–2152; approved internal project record (C1)–(C3).
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
The original core estimates on the literal calibrated chart, including
the scalar envelope, normalized absolute charge, relative charge and
nonpositive mixed radius derivative. `Ccore,ηc` depend only on `δ` and
precede `T`; boundary and failure coefficients are then selected before
all physical fields, scales, backgrounds, maps and test points.
No incoming scalar supremum or comparison estimate is supplied. -/
theorem calibrated_core_of_failed_observation {δ : ℝ} (hδ : 0 < δ) :
    ∃ Ccore ηc : ℝ, 0 < Ccore ∧ 0 < ηc ∧
    ∀ T : ℝ, 0 < T → ∃ Ccap : ℝ, 0 < Ccap ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / Ccap → ∃ Cobs : ℝ, 0 < Cobs ∧
    ∀ (ui e b s τ₀ : ℝ) (S : Fields) (_h : OriginalData ui e S)
      (γ : ClockCylinder S (origDomain ui) b (τ₀ - T * b / 2) (τ₀ + T * b / 2))
      (χ F G : ℝ → ℝ),
    let B := gaugeFields e S χ
    let L := b / s
    let H := B.a (γ.U τ₀) (γ.V τ₀)
    0 < b → 0 < s → s ≤ b → ContDiff ℝ 1 χ →
    (∀ τ ∈ Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2),
      HasDerivAt χ (S.A (γ.U τ) (γ.V τ)) (γ.U τ)) →
    χ (γ.U (τ₀ - T * b / 2)) = 0 →
    (∀ x : ℝ, τ₀ + s * x / 2 ∈ Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2) →
      s * F x = γ.U (τ₀ + s * x / 2) ∧ s * G x = γ.V (τ₀ + s * x / 2)) →
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
    let P := nullPullback (rescaleFields B s) F G
    let D := {p : ℝ × ℝ | (s * F p.1, s * G p.2) ∈ origDomain ui}
    ∀ ρ : ℝ, 0 < ρ → ∀ p ∈ sidewaysTruncation P D (-T * L / 2) (T * L / 2) ρ L,
      0 < P.r p.1 p.2 ∧ P.m p.1 p.2 ∈ Icc 0 2 ∧ δ ≤ 1 - P.mu p.1 p.2 ∧
      ‖P.phi p.1 p.2‖ ≤ ‖H‖ + (2 + 2 / Real.sqrt δ) / Real.sqrt (P.r p.1 p.2) ∧
      P.Q p.1 p.2 ^ 2 ≤ Ccore * (s * e) ^ 2 * P.m p.1 p.2 *
        (‖H‖ ^ 2 * P.r p.1 p.2 ^ 3 + P.r p.1 p.2 ^ 2) ∧
      P.Q p.1 p.2 ^ 2 / P.r p.1 p.2 ^ 2 ≤ P.mu p.1 p.2 ∧
      P.nu p.1 p.2 < 0 ∧ 0 < P.lam p.1 p.2 ∧ P.rUV p.1 p.2 ≤ 0 := by
  obtain ⟨Ccore, hCcore, ηc, hηc, hcore⟩ := core_bounds_of_failed_observation hδ
  refine ⟨Ccore, ηc, hCcore, hηc, ?_⟩
  intro T hT
  obtain ⟨Ccap, hCcap, hcore⟩ := hcore T hT.le
  refine ⟨Ccap, hCcap, ?_⟩
  intro ε hε hεCap
  obtain ⟨Cobs, hCobs, hcore⟩ := hcore ε hε hεCap
  refine ⟨Cobs, hCobs, ?_⟩
  intro ui e b s τ₀ S h γ χ F G
  dsimp only
  intro hb hs hsb hχ hχd hχ0 hcal hscale hgap hcharged hfailure
  let B := gaugeFields e S χ
  let L := b / s
  let H := B.a (γ.U τ₀) (γ.V τ₀)
  let f := fun t : ℝ => τ₀ + s * t / 2
  let P := nullPullback (rescaleFields B s) F G
  let D := {p : ℝ × ℝ | (s * F p.1, s * G p.2) ∈ origDomain ui}
  intro ρ hρ p hp
  have hTL : 0 ≤ T * L := mul_nonneg hT.le (div_pos hb hs).le
  have hu : p.1 ∈ Icc (-T * L / 2) (T * L / 2) :=
    ⟨hp.1.2.1.trans hp.1.2.2.1, hp.1.2.2.2⟩
  have hv : p.2 ∈ Icc (-T * L / 2) (T * L / 2) :=
    ⟨hp.1.2.1, hp.1.2.2.1.trans hp.1.2.2.2⟩
  have hsub : Icc (-T * L / 2) (T * L / 2) ⊆ Icc (-T * L) (T * L) :=
    Icc_subset_Icc (by linarith only [hTL]) (by linarith only [hTL])
  have strictLabel (t) (ht : t ∈ Icc (-T * L / 2) (T * L / 2)) :
      f t ∈ Ioo (τ₀ - T * b / 2) (τ₀ + T * b / 2) := by
    have ht' : t ∈ Icc (-(T / 2) * L) ((T / 2) * L) := by
      have hl : -(T / 2) * L = -T * L / 2 := by ring
      have hr : (T / 2) * L = T * L / 2 := by ring
      rwa [hl, hr]
    have hh := normalized_clock_mem (τ₀ := τ₀) hs ht'
    dsimp only [f]
    constructor <;> nlinarith only [hh.1, hh.2, mul_pos hT hb]
  have hsu := strictLabel p.1 hu
  have hsv := strictLabel p.2 hv
  have physU : s * F p.1 = γ.U (f p.1) := (hcal _ (Ioo_subset_Icc_self hsu)).1
  have physV : s * G p.2 = γ.V (f p.2) := (hcal _ (Ioo_subset_Icc_self hsv)).2
  have cm := calibrated_chart_components h.solution γ hs χ F G hcal hsu hsv
  have hpoint : (γ.U (f p.1), γ.V (f p.2)) ∈ origDomain ui := by
    have hh : (s * F p.1, s * G p.2) ∈ origDomain ui := hp.1.1
    rwa [physU, physV] at hh
  have hr : 0 < P.r p.1 p.2 := hρ.trans_le hp.2.1
  have hproper : γ.U (f p.1) < γ.V (f p.2) := by
    rcases lt_or_eq_of_le hpoint.2.2.1 with hh | hh
    · exact hh
    · change γ.U (f p.1) = γ.V (f p.2) at hh
      have hz := (h.solution.axis (γ.U (f p.1))
        (by simpa only [← hh] using hpoint)).1
      rw [cm.1, ← hh, hz, zero_div] at hr
      exact False.elim (lt_irrefl _ hr)
  have hclock : f p.2 ≤ f p.1 := by
    dsimp only [f]
    linarith only [mul_le_mul_of_nonneg_left hp.1.2.2.1 hs.le]
  have hupper : γ.V (f p.2) ≤ γ.V (f p.1) :=
    (γ.strictMonoOn_V h.solution).monotoneOn (Ioo_subset_Icc_self hsv) (Ioo_subset_Icc_self hsu)
        hclock
  have hc := hcore ui e b s τ₀ S h γ χ hb hs hsb hχ hχd hχ0 hscale hgap hcharged hfailure
    p.1 (hsub hu)
  have core := hc.2.2 (γ.V (f p.2)) ⟨hproper, hupper⟩
  have hm := hc.1 (γ.V (f p.2)) ⟨hproper.le, hupper⟩
  have hfull := cylinder_full_section_subset_triangle h.solution γ (Ioo_subset_Icc_self hsu)
  have hg := hgap (γ.U (f p.1), γ.V (f p.2)) (hfull ⟨rfl, hproper.le, hupper⟩)
  have hmass : P.m p.1 p.2 ∈ Icc 0 2 := by rw [cm.2.1]; exact hm
  have hgapP : δ ≤ 1 - P.mu p.1 p.2 := by rw [cm.2.2.2.1]; exact hg
  have hphi : ‖P.phi p.1 p.2‖ ≤ ‖H‖ +
      (2 + 2 / Real.sqrt δ) / Real.sqrt (P.r p.1 p.2) := by
    rw [cm.2.2.2.2.2.2.1, (gauge_invariants e S χ _ _).2.2.2.1, cm.1]
    exact core.1.2
  have hQ : P.Q p.1 p.2 ^ 2 ≤ Ccore * (s * e) ^ 2 * P.m p.1 p.2 *
      (‖H‖ ^ 2 * P.r p.1 p.2 ^ 3 + P.r p.1 p.2 ^ 2) := by
    rw [cm.2.2.1, cm.2.1, cm.1]
    exact core.2.1.2
  have hrelOriginal : S.Q (γ.U (f p.1)) (γ.V (f p.2)) ^ 2 /
      S.r (γ.U (f p.1)) (γ.V (f p.2)) ^ 2 ≤ S.mu (γ.U (f p.1)) (γ.V (f p.2)) := by
    have hh := (le_div_iff₀ (hδ.trans_le hg)).mp core.2.2.2.1
    simp only [zero_mul] at hh
    linarith only [hh]
  have hratio : P.Q p.1 p.2 ^ 2 / P.r p.1 p.2 ^ 2 =
      S.Q (γ.U (f p.1)) (γ.V (f p.2)) ^ 2 / S.r (γ.U (f p.1)) (γ.V (f p.2)) ^ 2 := by
    have halg (q r : ℝ) : (q / s) ^ 2 / (r / s) ^ 2 = q ^ 2 / r ^ 2 := by field_simp
    rw [cm.2.2.1, cm.1]
    exact halg _ _
  have hrelative : P.Q p.1 p.2 ^ 2 / P.r p.1 p.2 ^ 2 ≤ P.mu p.1 p.2 := by
    rw [hratio, cm.2.2.2.1]
    exact hrelOriginal
  have hn : P.nu p.1 p.2 < 0 := by
    rw [cm.2.2.2.2.1]
    exact mul_neg_of_pos_of_neg
      (inv_pos.mpr (mul_pos (by norm_num)
        (neg_pos.mpr (h.solution.nu_neg _ (γ.mem _ (Ioo_subset_Icc_self hsu))))))
      (h.solution.nu_neg _ hpoint)
  have hl : 0 < P.lam p.1 p.2 := by
    rw [cm.2.2.2.2.2.1]
    exact mul_pos (inv_pos.mpr (mul_pos (by norm_num)
      (h.solution.lam_pos _ (γ.mem _ (Ioo_subset_Icc_self hsv)))))
      (h.solution.lam_pos _ hpoint)
  refine ⟨hr, hmass, hgapP, hphi, hQ, hrelative, hn, hl, ?_⟩
  dsimp only [Fields.rUV]
  exact mul_nonpos_of_nonpos_of_nonneg
    (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hn.le hl.le) hr.le)
    (div_nonneg (sub_nonneg.mpr hrelative) (hδ.trans_le hgapP).le)

end EmcsfAcExtension.Global.Observation
