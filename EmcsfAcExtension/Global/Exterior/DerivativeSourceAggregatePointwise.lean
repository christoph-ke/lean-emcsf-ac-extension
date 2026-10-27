module

public import EmcsfAcExtension.Global.Exterior.DerivativeSource
public import EmcsfAcExtension.Global.Exterior.ScalarEnergy

/-! # Pointwise majorant for the exact charged derivative source

Every term of the exact source is retained, including the electromagnetic
commutator. Numerical constants are uniform in the solution and coupling.
Source: `charged_SF_new_version.tex:L1254–L1325`, approved internal project record (S2).
-/

public section

open Complex

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
A purely algebraic norm bound for the printed derivative source.
The coefficients `3` are exact triangle-inequality constants; no
smallness, regularity or equation is assumed. -/
theorem source_bracket_norm_le {e Q r μ q k : ℝ} {φ F : ℂ}
    (hk : 0 ≤ k) (hμ : 0 ≤ μ) (hq : 0 ≤ q) :
    ‖(k : ℂ) * (((1 - q) * ‖F‖ ^ 2 - 3 * μ + 5 * q +
      2 * e * Q * (starRingEnd ℂ φ * F).im : ℝ) * F) +
      I * e * k * (3 * Q * F + Q * φ * (1 + ‖F‖ ^ 2) -
        e * r ^ 2 * φ * (starRingEnd ℂ φ * F).im)‖ ≤
    k * (|1 - q| * ‖F‖ ^ 3 + (3 * μ + 5 * q) * ‖F‖ +
      3 * |e| * |Q| * ‖φ‖ * ‖F‖ ^ 2 + 3 * |e| * |Q| * ‖F‖ +
      |e| * |Q| * ‖φ‖ + e ^ 2 * r ^ 2 * ‖φ‖ ^ 2 * ‖F‖) := by
  have hj : |(starRingEnd ℂ φ * F).im| ≤ ‖φ‖ * ‖F‖ := by
    simpa only [norm_mul, Complex.norm_conj] using Complex.abs_im_le_norm (starRingEnd ℂ φ * F)
  have hb : |(1 - q) * ‖F‖ ^ 2 - 3 * μ + 5 * q +
      2 * e * Q * (starRingEnd ℂ φ * F).im| ≤
      |1 - q| * ‖F‖ ^ 2 + 3 * μ + 5 * q + 2 * |e| * |Q| * ‖φ‖ * ‖F‖ := by
    calc
      _ ≤ |(1 - q) * ‖F‖ ^ 2 - 3 * μ + 5 * q| +
          |2 * e * Q * (starRingEnd ℂ φ * F).im| := abs_add_le _ _
      _ ≤ (|(1 - q) * ‖F‖ ^ 2 - 3 * μ| + |5 * q|) +
          |2 * e * Q * (starRingEnd ℂ φ * F).im| := by gcongr; exact abs_add_le _ _
      _ ≤ ((|(1 - q) * ‖F‖ ^ 2| + |3 * μ|) + |5 * q|) +
          |2 * e * Q * (starRingEnd ℂ φ * F).im| := by gcongr; exact abs_sub _ _
      _ ≤ _ := by
        simp only [abs_mul, abs_of_nonneg (sq_nonneg ‖F‖), abs_of_nonneg hμ,
          abs_of_nonneg hq]
        norm_num only [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
          abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3), abs_of_nonneg (by norm_num : (0:ℝ) ≤ 5)]
        have hh := mul_le_mul_of_nonneg_left hj
          (by positivity : 0 ≤ 2 * |e| * |Q|)
        nlinarith only [hh]
  have hnF : ‖(1 : ℂ) + (‖F‖ : ℂ) ^ 2‖ = 1 + ‖F‖ ^ 2 := by
    rw [show (1 : ℂ) + (‖F‖ : ℂ) ^ 2 = ((1 + ‖F‖ ^ 2 : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hc : ‖3 * (Q : ℂ) * F + Q * φ * (1 + ‖F‖ ^ 2) -
      e * r ^ 2 * φ * (starRingEnd ℂ φ * F).im‖ ≤
      3 * |Q| * ‖F‖ + |Q| * ‖φ‖ * (1 + ‖F‖ ^ 2) +
        |e| * r ^ 2 * ‖φ‖ ^ 2 * ‖F‖ := by
    calc
      _ ≤ ‖3 * (Q : ℂ) * F + Q * φ * (1 + ‖F‖ ^ 2)‖ +
          ‖(e : ℂ) * r ^ 2 * φ * (starRingEnd ℂ φ * F).im‖ := norm_sub_le _ _
      _ ≤ (‖3 * (Q : ℂ) * F‖ + ‖(Q : ℂ) * φ * (1 + ‖F‖ ^ 2)‖) +
          ‖(e : ℂ) * r ^ 2 * φ * (starRingEnd ℂ φ * F).im‖ := by
        gcongr; exact norm_add_le _ _
      _ ≤ _ := by
        simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_ofNat,
          hnF, sq_abs]
        have hh := mul_le_mul_of_nonneg_left hj (by positivity : 0 ≤ |e| * r ^ 2 * ‖φ‖)
        nlinarith only [hh]
  calc
    _ ≤ ‖(k : ℂ) * (((1 - q) * ‖F‖ ^ 2 - 3 * μ + 5 * q +
        2 * e * Q * (starRingEnd ℂ φ * F).im : ℝ) * F)‖ +
        ‖I * e * k * (3 * Q * F + Q * φ * (1 + ‖F‖ ^ 2) -
          e * r ^ 2 * φ * (starRingEnd ℂ φ * F).im)‖ := norm_add_le _ _
    _ = k * |(1 - q) * ‖F‖ ^ 2 - 3 * μ + 5 * q +
        2 * e * Q * (starRingEnd ℂ φ * F).im| * ‖F‖ +
        |e| * k * ‖3 * (Q : ℂ) * F + Q * φ * (1 + ‖F‖ ^ 2) -
          e * r ^ 2 * φ * (starRingEnd ℂ φ * F).im‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk,
        Complex.norm_I, one_mul, mul_assoc]
    _ ≤ k * (|1 - q| * ‖F‖ ^ 2 + 3 * μ + 5 * q +
        2 * |e| * |Q| * ‖φ‖ * ‖F‖) * ‖F‖ +
        |e| * k * (3 * |Q| * ‖F‖ + |Q| * ‖φ‖ * (1 + ‖F‖ ^ 2) +
          |e| * r ^ 2 * ‖φ‖ ^ 2 * ‖F‖) := by gcongr
    _ = _ := by rw [← sq_abs e]; ring

/-- [internal]
Pointwise six-term majorant for the exact charged source. The coefficients
`4`, `65`, `326`, `3` are numerical and uniform in every solution,
coupling, row and point. The terminal consumer supplies these profiles. -/
theorem rawDensitySource_norm_le_of_profiles {ui e u v : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hp : (u, v) ∈ origDomain ui) (huv : u < v)
    (hg : 1 / 2 ≤ 1 - S.mu u v)
    (hX : terminalMass S u / S.r u v ≤ 1)
    (hQ : S.Q u v ^ 2 / S.r u v ^ 2 ≤ 64 * (terminalMass S u / S.r u v))
    (hnu : -S.nu u v ≤ 2 * (-S.nu u 0)) :
    ‖rawDensitySource e S u v‖ ≤ 4 * (-S.nu u 0) *
      (65 * (‖S.theta u v / (S.lam u v : ℂ)‖ ^ 3 / S.r u v ^ 2 * S.lam u v) +
       326 * (terminalMass S u * ‖S.theta u v / (S.lam u v : ℂ)‖ /
         S.r u v ^ 3 * S.lam u v) +
       3 * (|e| * |S.Q u v| * ‖S.phi u v‖ / S.r u v ^ 2 *
         ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v) +
       3 * (|e| * |S.Q u v| / S.r u v ^ 2 *
         ‖S.theta u v / (S.lam u v : ℂ)‖ * S.lam u v) +
       (|e| * |S.Q u v| * ‖S.phi u v‖ / S.r u v ^ 2 * S.lam u v) +
       (e ^ 2 * ‖S.phi u v‖ ^ 2 *
         ‖S.theta u v / (S.lam u v : ℂ)‖ * S.lam u v)) := by
  let r := S.r u v
  let μ := S.mu u v
  let q := S.Q u v ^ 2 / r ^ 2
  let F := S.theta u v / (S.lam u v : ℂ)
  let n := -S.nu u 0
  let k := S.lam u v * (-S.nu u v) / ((1 - μ) * r ^ 2)
  have hr : 0 < r := h.solution.r_pos (u, v) hp huv
  have hl := h.solution.lam_pos (u, v) hp
  have hn := neg_pos.mpr (h.solution.nu_neg (u, v) hp)
  have hp0 : (u, 0) ∈ origDomain ui := ⟨hp.1, hp.2.1, hp.2.1.le, le_rfl⟩
  have hn0 : 0 < n := neg_pos.mpr (h.solution.nu_neg (u, 0) hp0)
  have hgap : 0 < 1 - μ := h.solution.one_sub_mu_pos (u, v) hp
  have hk : 0 ≤ k := div_nonneg (mul_nonneg hl.le hn.le)
    (mul_nonneg hgap.le (sq_nonneg r))
  have hμ : 0 ≤ μ := (h.mu (u, v) hp).1
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq64 : q ≤ 64 := hQ.trans (by nlinarith only [hX])
  have hq1 : |1 - q| ≤ 65 := by rw [abs_le]; constructor <;> linarith
  have hmass := mu_le_terminal_div_radius h hp hr
  have hcoef : 3 * μ + 5 * q ≤ 326 * (terminalMass S u / r) := by
    dsimp only [μ, q, r]
    rw [mul_div_assoc] at hmass
    nlinarith only [hmass, hQ]
  have hkg : (-S.nu u v) / (1 - μ) ≤ 4 * n := by
    apply (div_le_iff₀ hgap).mpr
    have hh := mul_le_mul_of_nonneg_left hg (show 0 ≤ 4 * n by positivity)
    dsimp only [μ, n] at hh ⊢
    linarith only [hh, hnu]
  have hkb : k ≤ 4 * n * S.lam u v / r ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hkg
      (div_nonneg hl.le (sq_nonneg r))
    convert hh using 1 <;> dsimp [k] <;> field_simp [hr.ne', hgap.ne']
  have hb := source_bracket_norm_le (e := e) (Q := S.Q u v) (r := r)
    (φ := S.phi u v) (F := F) hk hμ hq
  change ‖rawDensitySource e S u v‖ ≤ _ at hb
  refine hb.trans ?_
  calc
    _ ≤ k * (65 * ‖F‖ ^ 3 + (326 * (terminalMass S u / r)) * ‖F‖ +
        3 * |e| * |S.Q u v| * ‖S.phi u v‖ * ‖F‖ ^ 2 +
        3 * |e| * |S.Q u v| * ‖F‖ + |e| * |S.Q u v| * ‖S.phi u v‖ +
        e ^ 2 * r ^ 2 * ‖S.phi u v‖ ^ 2 * ‖F‖) := by gcongr
    _ ≤ (4 * n * S.lam u v / r ^ 2) *
        (65 * ‖F‖ ^ 3 + (326 * (terminalMass S u / r)) * ‖F‖ +
        3 * |e| * |S.Q u v| * ‖S.phi u v‖ * ‖F‖ ^ 2 +
        3 * |e| * |S.Q u v| * ‖F‖ + |e| * |S.Q u v| * ‖S.phi u v‖ +
        e ^ 2 * r ^ 2 * ‖S.phi u v‖ ^ 2 * ‖F‖) := by
      apply mul_le_mul_of_nonneg_right hkb
      have hm := mass_nonneg h hp0
      positivity
    _ = _ := by
      have hr0 : S.r u v ≠ 0 := hr.ne'
      dsimp [n, F, r]
      field_simp [hr0]

end EmcsfAcExtension.Global.Exterior
