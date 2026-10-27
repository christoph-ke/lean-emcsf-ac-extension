module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Apriori.AreaJAux
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # The axis-gauge potential in the classical class

The outgoing constraint is integrated from its zero axis value, as in
`charged_SF_new_version.tex:L4909–L4916`. Both characteristic AC assertions below are
in the internal project record classical class, the smooth scope of erratum internal project record.
They make
no claim about incoming AC of a potential in the broad frozen class.
-/

public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

variable {e s ε M : ℝ} {S : Fields} {h : ℝ → ℂ}

private theorem potential_v_le (hset : AprioriSetting e s ε M S h)
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 s) :
    |S.AV u v| ≤ 8 * |e| * M * ε * S.lam u v := by
  by_cases hr : S.r u v = 0
  · have hM : 0 ≤ M := le_trans (by norm_num) hset.one_le_M
    have hl := (hset.c1.lam_pos (u, v) hp).le
    have he := hset.eps_nonneg
    calc
      |S.AV u v| = 0 := by simp [Fields.AV, hr]
      _ ≤ _ := by positivity
  have hn := hset.c1.nu_neg (u, v) hp
  have hl := hset.c1.lam_pos (u, v) hp
  have hh := hset.c1.one_sub_mu_pos (u, v) hp
  have hden := mul_pos hh (sq_pos_of_ne_zero hr)
  have hq := hset.charge_le hp
  have hfac : 2 * (-S.nu u v) ≤ 4 * (1 - S.mu u v) := by
    linarith only [(hset.box (u, v) hp).2.2.2.1,
      (hset.box (u, v) hp).2.2.2.2.1]
  have hM : 0 ≤ M := le_trans (by norm_num) hset.one_le_M
  have he := hset.eps_nonneg
  rw [Fields.AV, abs_div, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_neg hn, abs_of_pos hl, abs_of_pos hden, div_le_iff₀ hden]
  calc
    _ ≤ 2 * (-S.nu u v) * S.lam u v * (2 * |e| * M * ε * S.r u v ^ 2) := by
      gcongr
      exact mul_nonneg (mul_nonneg (by norm_num) (neg_pos.mpr hn).le) hl.le
    _ = (2 * (-S.nu u v)) * (2 * |e| * M * ε * S.lam u v * S.r u v ^ 2) := by ring
    _ ≤ (4 * (1 - S.mu u v)) *
        (2 * |e| * M * ε * S.lam u v * S.r u v ^ 2) := by
      gcongr
    _ = (8 * |e| * M * ε * S.lam u v) * ((1 - S.mu u v) * S.r u v ^ 2) := by ring

/-- The potential constraint extends as an integral equation to the regular
axis. This identity has no smallness or derivative-size assumption. -/
theorem AprioriSetting.potential_integralForm (hset : AprioriSetting e s ε M S h)
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 s) :
    IntegralForm (S.A u) (S.AV u) u v := by
  have hs : MapsTo (fun x => (u, x)) (Icc u v) (triangle 0 s) :=
    fun x hx => ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩
  have hf := integralForm_pdV hset.c1.c1_A (uniqueDiffOn_triangle hset.pos) hp.2.1 hs
  have heq : pdV (triangle 0 s) S.A u =ᵐ[volume.restrict (uIoc u v)] S.AV u := by
    rw [uIoc_of_le hp.2.1]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact (hset.c1.eq_v (u, x) (hs ⟨hx.1.le, hx.2⟩) hx.1).2.2.2.2.1
  exact ⟨hf.1.congr_ae heq, hf.2.trans (intervalIntegral.integral_congr_ae_restrict heq)⟩

/-- [node restart-sec-independent-area#axis-gauge-potential-bound]
The zero-axis potential is its outgoing constraint integral, with the size
bound of `charged_SF_new_version.tex:L4909–L4916`. `C` is universal: independent of
`e,s,ε,M,S,h` and all higher initial derivatives. No smallness is required. -/
theorem axis_gauge_potential_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (e s ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
      AprioriSetting e s ε M S h → ∀ u v, (u, v) ∈ triangle 0 s →
        S.A u v = ∫ x in u..v, S.AV u x ∧
        |S.A u v| ≤ C * |e| * M * ε * S.r u v := by
  refine ⟨8, by norm_num, ?_⟩
  intro e s ε M S h hset u v hp
  have hf := hset.potential_integralForm hp
  have hA : S.A u v = ∫ x in u..v, S.AV u x := by
    simpa only [hset.data.2 u ⟨hp.1, hp.2.1.trans hp.2.2⟩, sub_zero] using hf.2
  refine ⟨hA, ?_⟩
  have hs : MapsTo (fun x => (u, x)) (Icc u v) (triangle 0 s) :=
    fun x hx => ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩
  have cl : ContinuousOn (S.lam u) (Icc u v) := hset.c1.c1_lam.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hs
  have hb := intervalIntegral.integral_mono_on hp.2.1 hf.1.norm
    ((cl.intervalIntegrable_of_Icc (μ := volume) hp.2.1).const_mul (8 * |e| * M * ε))
    (fun x hx => by simpa only [Real.norm_eq_abs] using potential_v_le hset (hs hx))
  rw [intervalIntegral.integral_const_mul, Area.radius_out_integral hset hp.1 hp.2.1 hp.2.2]
    at hb
  rw [hA, ← Real.norm_eq_abs]
  exact (intervalIntegral.norm_integral_le_integral_norm hp.2.1).trans hb

/-- [node restart-sec-independent-area#potential-characteristic-ac]
The axis-gauge potential is AC on both closed characteristic sections,
including their axis endpoints (`charged_SF_new_version.tex:L4909–L4913`, internal project record
smooth
scope). This qualitative classical assertion needs no smallness and no
uniform derivative norm. -/
theorem potential_characteristic_ac {e s ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e s ε M S h) {u v : ℝ} (hp : (u, v) ∈ triangle 0 s) :
    AbsolutelyContinuousOnInterval (S.A u) u v ∧
      AbsolutelyContinuousOnInterval (fun x => S.A x v) u v := by
  constructor
  · apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le hp.2.1]
    exact hset.c1.c1_A.comp ((contDiffOn_const (c := u)).prodMk contDiffOn_id)
      (fun x hx => ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩)
  · apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le hp.2.1]
    exact hset.c1.c1_A.comp (contDiffOn_id.prodMk (contDiffOn_const (c := v)))
      (fun x hx => ⟨hp.1.trans hx.1, hx.2, hp.2.2⟩)

end EmcsfAcExtension.Local
