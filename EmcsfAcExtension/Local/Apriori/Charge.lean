module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Calculus.RelativeCharge
import EmcsfAcExtension.Local.Calculus.C1ToSolution2
import EmcsfAcExtension.Local.Calculus.Partials

/-! # Charge bounds in the classical bootstrap box

The Maxwell equations retain a factor of scalar variation, as in
`charged_SF_new_version.tex:L4643–L4648`. All numerical constants are universal.
-/

public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

variable {e s ε M : ℝ} {S : Fields} {h : ℝ → ℂ}

/-- The bootstrap variation parameter is nonnegative. -/
theorem AprioriSetting.eps_nonneg (hset : AprioriSetting e s ε M S h) : 0 ≤ ε :=
  ENNReal.toReal_nonneg.trans hset.eps

/-- The background bound is at least one, uniformly in the data. -/
theorem AprioriSetting.one_le_M (hset : AprioriSetting e s ε M S h) : 1 ≤ M := by
  rw [hset.M_eq]
  linarith only [hset.eps_nonneg, norm_nonneg (h 0)]

/-- The bootstrap radius is nonnegative on the closed triangle. -/
theorem AprioriSetting.radius_nonneg (hset : AprioriSetting e s ε M S h)
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 s) : 0 ≤ S.r u v := by
  rcases eq_or_lt_of_le hp.2.1 with huv | huv
  · change u = v at huv
    subst v
    rw [(hset.c1.axis u hp).1]
  · exact (hset.c1.r_pos (u, v) hp huv).le

/-- The unnormalized outgoing scalar has its literal bootstrap bound;
the coefficient `4` is universal. -/
theorem AprioriSetting.theta_norm_le (hset : AprioriSetting e s ε M S h)
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 s) :
    ‖S.theta u v‖ ≤ 4 * ε * S.lam u v := by
  have hl := hset.c1.lam_pos (u, v) hp
  have hb := (hset.box (u, v) hp).2.2.2.2.2.2.1
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl] at hb
  exact (div_le_iff₀ hl).mp hb

/-- The unnormalized incoming scalar has its literal bootstrap bound;
the coefficient `4` is universal. -/
theorem AprioriSetting.xi_norm_le (hset : AprioriSetting e s ε M S h)
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 s) :
    ‖S.xi u v‖ ≤ 4 * ε * (-S.nu u v) := by
  have hn := hset.c1.nu_neg (u, v) hp
  have hb := (hset.box (u, v) hp).2.2.2.2.2.2.2
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hn] at hb
  exact (div_le_iff₀ (neg_pos.mpr hn)).mp hb

/-- The sharp charge bound from radial integration, with universal coefficient
`2`, independent of `e`, `s`, `M`, and all higher data derivatives. -/
theorem AprioriSetting.charge_le (hset : AprioriSetting e s ε M S h)
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 s) :
    |S.Q u v| ≤ 2 * |e| * M * ε * S.r u v ^ 2 := by
  have hb := Stab.oscillatory_charge_bound (hset.c1.toIsSolution hset.pos) hp.2.1
    (show outSeg u u v ⊆ triangle 0 s from fun p hq => by
      rcases hq with ⟨rfl, hq⟩
      exact ⟨hp.1, hq.1, hq.2.trans hp.2.2⟩)
    (fun x hx => (hset.box (u, x) ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩).2.2.2.2.2.1)
    (fun x hx => (hset.box (u, x) ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩).2.2.2.2.2.2.1)
  convert hb using 1
  ring

/-- Squared charge divided by squared radius, including the totalized axis
value. The literal coefficient `4` is universal. -/
theorem AprioriSetting.charge_sq_div_le (hset : AprioriSetting e s ε M S h)
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 s) :
    S.Q u v ^ 2 / S.r u v ^ 2 ≤ 4 * e ^ 2 * M ^ 2 * ε ^ 2 * S.r u v ^ 2 := by
  by_cases hr : S.r u v = 0
  · simp [hr]
  have hq := pow_le_pow_left₀ (abs_nonneg (S.Q u v)) (hset.charge_le hp) 2
  rw [sq_abs] at hq
  apply (div_le_iff₀ (sq_pos_of_ne_zero hr)).mpr
  convert hq using 1
  simp only [mul_pow, sq_abs]
  ring

private theorem maxwell_norm_le (c r : ℝ) (p z : ℂ) (hr : 0 ≤ r) :
    |c * r * (starRingEnd ℂ p * z).im| ≤ |c| * r * ‖p‖ * ‖z‖ := by
  rw [abs_mul, abs_mul, abs_of_nonneg hr]
  calc
    _ ≤ |c| * r * (‖p‖ * ‖z‖) := by
      gcongr
      simpa only [norm_mul, Complex.norm_conj] using
        Complex.abs_im_le_norm (starRingEnd ℂ p * z)
    _ = _ := by ring

/-- The outgoing Maxwell right side has universal coefficient `4`; no
smallness or higher derivative bound is needed. -/
theorem AprioriSetting.maxwell_v_le (hset : AprioriSetting e s ε M S h)
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 s) :
    |S.QV e u v| ≤ 4 * |e| * M * ε * S.lam u v * S.r u v := by
  have heps := hset.eps_nonneg
  have hM : 0 ≤ M := le_trans (by norm_num) hset.one_le_M
  have hr := hset.radius_nonneg hp
  have hl := (hset.c1.lam_pos (u, v) hp).le
  have hpM := (hset.box (u, v) hp).2.2.2.2.2.1
  calc
    |S.QV e u v| = |e * S.r u v * (starRingEnd ℂ (S.phi u v) * S.theta u v).im| := by
      simp only [Fields.QV, abs_neg]
    _ ≤ |e| * S.r u v * ‖S.phi u v‖ * ‖S.theta u v‖ := maxwell_norm_le _ _ _ _ hr
    _ ≤ |e| * S.r u v * M * (4 * ε * S.lam u v) := by
      gcongr
      exact hset.theta_norm_le hp
    _ = _ := by ring

/-- The incoming Maxwell right side has universal coefficient `4`; no
smallness or higher derivative bound is needed. -/
theorem AprioriSetting.maxwell_u_le (hset : AprioriSetting e s ε M S h)
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 s) :
    |S.QU e u v| ≤ 4 * |e| * M * ε * (-S.nu u v) * S.r u v := by
  have heps := hset.eps_nonneg
  have hM : 0 ≤ M := le_trans (by norm_num) hset.one_le_M
  have hr := hset.radius_nonneg hp
  have hn := (neg_pos.mpr (hset.c1.nu_neg (u, v) hp)).le
  have hpM := (hset.box (u, v) hp).2.2.2.2.2.1
  calc
    |S.QU e u v| ≤ |e| * S.r u v * ‖S.phi u v‖ * ‖S.xi u v‖ := maxwell_norm_le _ _ _ _ hr
    _ ≤ |e| * S.r u v * M * (4 * ε * (-S.nu u v)) := by
      gcongr
      exact hset.xi_norm_le hp
    _ = _ := by ring

/-- [node restart-bv-Q-bounds]
Charge and both Maxwell right sides on the full bootstrap triangle; these
are the classical derivatives off the axis (`charged_SF_new_version.tex:L4643–L4648`).
`C` is universal, independent of `e`, `s`,
`M`, and all smooth data derivative norms. No smallness is needed. -/
theorem bv_q_bounds : ∃ C : ℝ, 0 < C ∧ ∀ (e s ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e s ε M S h → ∀ u v, (u, v) ∈ triangle 0 s →
      |S.Q u v| ≤ C * |e| * M * ε * S.r u v ^ 2 ∧
      |S.QV e u v| ≤ C * |e| * M * ε * S.lam u v * S.r u v ∧
      |S.QU e u v| ≤ C * |e| * M * ε * (-S.nu u v) * S.r u v := by
  refine ⟨4, by norm_num, ?_⟩
  intro e s ε M S h hset u v hp
  have heps := hset.eps_nonneg
  have hM := hset.one_le_M
  exact ⟨(hset.charge_le hp).trans (by gcongr; norm_num),
    hset.maxwell_v_le hp, hset.maxwell_u_le hp⟩

/-- [node restart-bv-Q-bounds]
The charge estimate with the actual within-domain Maxwell derivatives
(`charged_SF_new_version.tex:L4643–L4648`). `C` is universal, independent of `e`, `s`,
`M`, and all higher data norms. No smallness is required. -/
theorem bv_q_bounds_partials :
    ∃ C : ℝ, 0 < C ∧ ∀ (e s ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e s ε M S h → ∀ u v, 0 ≤ u → u < v → v ≤ s →
      |S.Q u v| ≤ C * |e| * M * ε * S.r u v ^ 2 ∧
      |pdV (triangle 0 s) S.Q u v| ≤ C * |e| * M * ε * S.lam u v * S.r u v ∧
      |pdU (triangle 0 s) S.Q u v| ≤ C * |e| * M * ε * (-S.nu u v) * S.r u v := by
  obtain ⟨C, hC, hbound⟩ := bv_q_bounds
  refine ⟨C, hC, ?_⟩
  intro e s ε M S h hset u v hu huv hvs
  have hp : (u, v) ∈ triangle 0 s := ⟨hu, huv.le, hvs⟩
  rw [(hset.c1.eq_v (u, v) hp huv).2.2.2.1,
    (hset.c1.eq_u (u, v) hp huv).2.2.2.1]
  exact hbound e s ε M S h hset u v hp

end EmcsfAcExtension.Local
