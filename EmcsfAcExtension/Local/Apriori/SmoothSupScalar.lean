module

public import EmcsfAcExtension.Local.Apriori.SmoothSupRadial
import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # Recovering scalar derivatives from the renormalized suprema

internal project record (N1–N2), `charged_SF_new_version.tex:L6287–6288`. Maxima are taken on the
already existing compact classical triangle before absorbing the cubic term.
The estimates are uniform in the datum and apex; no bound uniform over a
sequence of initial derivative norms is claimed.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem coefficient_ratio_aux {l r A : ℝ} {f : ℂ} (hr0 : 0 ≤ r) (hA : 0 ≤ A)
    (hl : |l| ≤ 1) (hdecay : ‖f‖ ≤ 4 * r * A) :
    |l / r| * ‖f‖ ≤ 4 * A := by
  by_cases hr : r = 0
  · simp only [hr, div_zero, abs_zero, zero_mul]
    positivity
  have hmul := mul_le_mul_of_nonneg_left hdecay (abs_nonneg (l / r))
  have heq : |l / r| * (4 * r * A) = 4 * |l| * A := by
    rw [abs_div, abs_of_nonneg hr0]
    field_simp [hr]
  rw [heq] at hmul
  exact hmul.trans (by nlinarith only [hl, hA])

private theorem renormalized_recovery_aux {m q ε A : ℝ} {d f : ℂ}
    (hm : 1 / 2 ≤ m) (_hε : 0 ≤ ε) (hf : ‖f‖ ≤ 4 * ε)
    (hq : |q| * ‖f‖ ≤ 4 * A) :
    ‖d‖ ≤ 2 * ‖(m : ℂ) * (d - (q : ℂ) * (‖f‖ : ℂ) ^ 2 * f)‖ +
      64 * ε ^ 2 * A := by
  have hm0 : 0 < m := lt_of_lt_of_le (by norm_num) hm
  let j := (m : ℂ) * (d - (q : ℂ) * (‖f‖ : ℂ) ^ 2 * f)
  have heq : d = (m⁻¹ : ℝ) • j + (q : ℂ) * (‖f‖ : ℂ) ^ 2 * f := by
    dsimp only [j]
    rw [Complex.real_smul, Complex.ofReal_inv]
    field_simp [Complex.ofReal_ne_zero.mpr hm0.ne']
    ring
  have hmi : m⁻¹ ≤ 2 := by
    have hi := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hm
    norm_num at hi
    exact hi
  have hf2 : ‖f‖ ^ 2 ≤ 16 * ε ^ 2 := by
    have hi := pow_le_pow_left₀ (norm_nonneg f) hf 2
    nlinarith only [hi]
  calc
    ‖d‖ ≤ ‖(m⁻¹ : ℝ) • j‖ + ‖(q : ℂ) * (‖f‖ : ℂ) ^ 2 * f‖ := by
      rw [heq]
      exact norm_add_le _ _
    _ = m⁻¹ * ‖j‖ + ‖f‖ ^ 2 * (|q| * ‖f‖) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hm0)]
      simp only [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_norm]
      ring
    _ ≤ 2 * ‖j‖ + (16 * ε ^ 2) * (4 * A) :=
      add_le_add (mul_le_mul_of_nonneg_right hmi (norm_nonneg _))
        (mul_le_mul hf2 hq (mul_nonneg (abs_nonneg _) (norm_nonneg _))
          (mul_nonneg (by norm_num) (sq_nonneg _)))
    _ = _ := by ring

private theorem absorbed_max_aux {A j ε : ℝ} (hA : 0 ≤ A) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 16) (hb : A ≤ 2 * j + 64 * ε ^ 2 * A) : A ≤ 4 * j := by
  have hi := pow_le_pow_left₀ hε0 hε 2
  have hs : 64 * ε ^ 2 ≤ 1 / 2 := by nlinarith only [hi]
  have hmul := mul_le_mul_of_nonneg_right hs hA
  linarith only [hb, hmul]

private theorem outgoing_max_aux {e T ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) (hε : ε ≤ 1 / 16) :
    ∃ A : ℝ, 0 ≤ A ∧
      (∀ p ∈ triangle 0 T, ‖pdV (triangle 0 T) S.a p.1 p.2‖ ≤ A) ∧
      ENNReal.ofReal A ≤ 4 * (⨆ p ∈ triangle 0 T, ‖jC1 (triangle 0 T) S p.1 p.2‖ₑ) := by
  let J := ⨆ p ∈ triangle 0 T, ‖jC1 (triangle 0 T) S p.1 p.2‖ₑ
  have hc := continuousOn_pdV hset.c1.c1_a (uniqueDiffOn_triangle hset.pos)
  obtain ⟨p, hp, hmax⟩ := (isCompact_triangle 0 T).exists_isMaxOn
    ⟨(0, 0), le_rfl, le_rfl, hset.pos.le⟩ hc.norm
  let A := ‖pdV (triangle 0 T) S.a p.1 p.2‖
  have hA0 : 0 ≤ A := norm_nonneg _
  have hb : ∀ q ∈ triangle 0 T, ‖pdV (triangle 0 T) S.a q.1 q.2‖ ≤ A :=
    fun q hq => hmax hq
  refine ⟨A, hA0, hb, ?_⟩
  change ENNReal.ofReal A ≤ 4 * J
  by_cases hJ : J = ⊤
  · simp [hJ]
  have hj : ‖jC1 (triangle 0 T) S p.1 p.2‖ ≤ J.toReal := by
    have hle : ‖jC1 (triangle 0 T) S p.1 p.2‖ₑ ≤ J := by
      dsimp only [J]
      exact le_iSup₂_of_le p hp le_rfl
    simpa only [toReal_enorm] using ENNReal.toReal_mono hJ hle
  have hε0 : 0 ≤ ε := ENNReal.toReal_nonneg.trans hset.eps
  have hbox := hset.box p hp
  have hl : |S.lam p.1 p.2| ≤ 1 := by
    rw [abs_of_pos (hset.c1.lam_pos p hp)]
    exact hbox.2.1
  have hd := smooth_outgoing_decay_of_bound hset hA0 hb hp
  have hr0 : 0 ≤ S.r p.1 p.2 :=
    (div_nonneg (sub_nonneg.mpr hp.2.1) (by norm_num)).trans (smooth_radius_bounds_aux hset hp).1
  have hq := coefficient_ratio_aux hr0 hA0 hl hd
  have hn0 := renormalized_recovery_aux (m := 1 - S.mu p.1 p.2)
    (d := pdV (triangle 0 T) S.a p.1 p.2)
    hbox.2.2.2.2.1 hε0 hbox.2.2.2.2.2.2.1 hq
  have hn : A ≤ 2 * ‖jC1 (triangle 0 T) S p.1 p.2‖ + 64 * ε ^ 2 * A := by
    simpa only [jC1, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div,
      Complex.ofReal_pow] using hn0
  have habs : A ≤ 4 * J.toReal := absorbed_max_aux hA0 hε0 hε
    (hn.trans (add_le_add
      (mul_le_mul_of_nonneg_left hj (by norm_num : (0 : ℝ) ≤ 2)) le_rfl))
  calc
    ENNReal.ofReal A ≤ ENNReal.ofReal (4 * J.toReal) := ENNReal.ofReal_le_ofReal habs
    _ = 4 * J := by rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hJ]; norm_num

private theorem incoming_max_aux {e T ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) (hε : ε ≤ 1 / 16) :
    ∃ A : ℝ, 0 ≤ A ∧
      (∀ p ∈ triangle 0 T,
        ‖pdU (triangle 0 T) S.b p.1 p.2 + I * e * S.A p.1 p.2 * S.b p.1 p.2‖ ≤ A) ∧
      ENNReal.ofReal A ≤ 4 * (⨆ p ∈ triangle 0 T, ‖kC1 e (triangle 0 T) S p.1 p.2‖ₑ) := by
  let K := ⨆ p ∈ triangle 0 T, ‖kC1 e (triangle 0 T) S p.1 p.2‖ₑ
  have hc : ContinuousOn (fun p : ℝ × ℝ =>
      pdU (triangle 0 T) S.b p.1 p.2 + I * e * S.A p.1 p.2 * S.b p.1 p.2)
      (triangle 0 T) :=
    (continuousOn_pdU hset.c1.c1_b (uniqueDiffOn_triangle hset.pos)).add
      ((continuousOn_const.mul
        (Complex.continuous_ofReal.comp_continuousOn hset.c1.c1_A.continuousOn)).mul
        hset.c1.c1_b.continuousOn)
  obtain ⟨p, hp, hmax⟩ := (isCompact_triangle 0 T).exists_isMaxOn
    ⟨(0, 0), le_rfl, le_rfl, hset.pos.le⟩ hc.norm
  let A := ‖pdU (triangle 0 T) S.b p.1 p.2 + I * e * S.A p.1 p.2 * S.b p.1 p.2‖
  have hA0 : 0 ≤ A := norm_nonneg _
  have hb : ∀ q ∈ triangle 0 T,
      ‖pdU (triangle 0 T) S.b q.1 q.2 + I * e * S.A q.1 q.2 * S.b q.1 q.2‖ ≤ A :=
    fun q hq => hmax hq
  refine ⟨A, hA0, hb, ?_⟩
  change ENNReal.ofReal A ≤ 4 * K
  by_cases hK : K = ⊤
  · simp [hK]
  have hk : ‖kC1 e (triangle 0 T) S p.1 p.2‖ ≤ K.toReal := by
    have hle : ‖kC1 e (triangle 0 T) S p.1 p.2‖ₑ ≤ K := by
      dsimp only [K]
      exact le_iSup₂_of_le p hp le_rfl
    simpa only [toReal_enorm] using ENNReal.toReal_mono hK hle
  have hε0 : 0 ≤ ε := ENNReal.toReal_nonneg.trans hset.eps
  have hbox := hset.box p hp
  have hn : |S.nu p.1 p.2| ≤ 1 := by
    rw [abs_of_neg (hset.c1.nu_neg p hp)]
    exact hbox.2.2.2.1
  have hd := smooth_incoming_decay_of_bound hset hA0 hb hp
  have hr0 : 0 ≤ S.r p.1 p.2 :=
    (div_nonneg (sub_nonneg.mpr hp.2.1) (by norm_num)).trans (smooth_radius_bounds_aux hset hp).1
  have hq := coefficient_ratio_aux hr0 hA0 hn hd
  have hr1 := renormalized_recovery_aux (m := 1 - S.mu p.1 p.2)
    (d := pdU (triangle 0 T) S.b p.1 p.2 + I * e * S.A p.1 p.2 * S.b p.1 p.2)
    hbox.2.2.2.2.1 hε0 hbox.2.2.2.2.2.2.2 hq
  have hr : A ≤ 2 * ‖kC1 e (triangle 0 T) S p.1 p.2‖ + 64 * ε ^ 2 * A := by
    simpa only [kC1, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div,
      Complex.ofReal_pow] using hr1
  have habs : A ≤ 4 * K.toReal := absorbed_max_aux hA0 hε0 hε
    (hr.trans (add_le_add
      (mul_le_mul_of_nonneg_left hk (by norm_num : (0 : ℝ) ≤ 2)) le_rfl))
  calc
    ENNReal.ofReal A ≤ ENNReal.ofReal (4 * K.toReal) := ENNReal.ofReal_le_ofReal habs
    _ = 4 * K := by rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hK]; norm_num

/-- The normalized scalar derivative and linear radial bounds of internal project record (N1).
The exact coefficients `4` and `16`, with the fixed threshold `ε ≤ 1/16`,
are universal in the bootstrap box, independent of `e,T,M` and smooth data
derivative norms. This is the classical integral-representation route (internal project record).
The renormalized suprema are retained explicitly, with no finiteness premise.
This helper does not close the finite, datum-uniform `#scalar-c1-bounds` node
until the sup-closure estimates have been assembled. -/
theorem smooth_scalar_derivative_recovery_aux {e T ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) (hε : ε ≤ 1 / 16) :
    let J := ⨆ p ∈ triangle 0 T, ‖jC1 (triangle 0 T) S p.1 p.2‖ₑ
    let K := ⨆ p ∈ triangle 0 T, ‖kC1 e (triangle 0 T) S p.1 p.2‖ₑ
    (⨆ p ∈ triangle 0 T, ‖pdV (triangle 0 T) S.a p.1 p.2‖ₑ) ≤ 4 * J ∧
    (⨆ p ∈ triangle 0 T,
      ‖pdU (triangle 0 T) S.b p.1 p.2 + I * e * S.A p.1 p.2 * S.b p.1 p.2‖ₑ) ≤ 4 * K ∧
    ∀ p ∈ triangle 0 T,
      ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ₑ ≤ ENNReal.ofReal (16 * S.r p.1 p.2) * J ∧
      ‖S.xi p.1 p.2 / S.nu p.1 p.2‖ₑ ≤ ENNReal.ofReal (16 * S.r p.1 p.2) * K := by
  dsimp only
  obtain ⟨A, hA0, hA, hAJ⟩ := outgoing_max_aux hset hε
  obtain ⟨B, hB0, hB, hBK⟩ := incoming_max_aux hset hε
  refine ⟨iSup₂_le (fun p hp => (show ‖pdV (triangle 0 T) S.a p.1 p.2‖ₑ ≤
    ENNReal.ofReal A from by simpa only [ofReal_norm] using
      ENNReal.ofReal_le_ofReal (hA p hp)).trans hAJ),
    iSup₂_le (fun p hp => (show
      ‖pdU (triangle 0 T) S.b p.1 p.2 + I * e * S.A p.1 p.2 * S.b p.1 p.2‖ₑ ≤
        ENNReal.ofReal B from by simpa only [ofReal_norm] using
          ENNReal.ofReal_le_ofReal (hB p hp)).trans hBK), ?_⟩
  intro p hp
  have hr : 0 ≤ S.r p.1 p.2 :=
    (div_nonneg (sub_nonneg.mpr hp.2.1) (by norm_num)).trans (smooth_radius_bounds_aux hset hp).1
  have hconvert (X : ℝ≥0∞) (C : ℝ) (_hC : 0 ≤ C) (hCX : ENNReal.ofReal C ≤ 4 * X)
      {f : ℂ} (hf : ‖f‖ ≤ 4 * S.r p.1 p.2 * C) :
      ‖f‖ₑ ≤ ENNReal.ofReal (16 * S.r p.1 p.2) * X := by
    calc
      ‖f‖ₑ ≤ ENNReal.ofReal (4 * S.r p.1 p.2 * C) := by
        simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal hf
      _ = ENNReal.ofReal (4 * S.r p.1 p.2) * ENNReal.ofReal C :=
        ENNReal.ofReal_mul (mul_nonneg (by norm_num) hr)
      _ ≤ ENNReal.ofReal (4 * S.r p.1 p.2) * (4 * X) := mul_le_mul' le_rfl hCX
      _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul
          (mul_nonneg (by norm_num) hr)]
        congr 2
        ring
  exact ⟨hconvert _ A hA0 hAJ (smooth_outgoing_decay_of_bound hset hA0 hA hp),
    hconvert _ B hB0 hBK (smooth_incoming_decay_of_bound hset hB0 hB hp)⟩

end EmcsfAcExtension.Local
