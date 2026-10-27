module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Calculus.Reconstruction
import EmcsfAcExtension.Local.Calculus.C1ToSolution2
import EmcsfAcExtension.Local.Calculus.Partials

/-! # Pointwise mass in the classical bootstrap box

The positive mass constraint gives the estimate of `charged_SF_new_version.tex:L4819–L4828`.
The proof uses a polynomial comparison function along each outgoing section,
so the totalized mass ratio is never differentiated on the axis.
-/

public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

variable {e s ε M : ℝ} {S : Fields} {h : ℝ → ℂ}

/-- Ordinary mass is nonnegative on the bootstrap triangle. No smallness or
higher derivative bound is needed. -/
theorem AprioriSetting.mass_nonneg (hset : AprioriSetting e s ε M S h)
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 s) : 0 ≤ S.m u v := by
  have hS := hset.c1.toIsSolution hset.pos
  have hs : inSeg u v v ⊆ triangle 0 s := by
    rintro p ⟨hux, hxv, rfl⟩
    exact ⟨hp.1.trans hux, hxv, hp.2.2⟩
  have hm := stab_incoming_mass hS hp.2.1 hs
  have hi : 0 ≤ ∫ x in u..v, (-S.nu x v) *
      ((1 - S.mu x v) * ‖S.xi x v / S.nu x v‖ ^ 2 + S.Q x v ^ 2 / S.r x v ^ 2) := by
    apply intervalIntegral.integral_nonneg hp.2.1
    intro x hx
    have hxD : (x, v) ∈ triangle 0 s := ⟨hp.1.trans hx.1, hx.2, hp.2.2⟩
    have hn := hset.c1.nu_neg (x, v) hxD
    have hh := hset.c1.one_sub_mu_pos (x, v) hxD
    exact mul_nonneg (neg_pos.mpr hn).le
      (add_nonneg (mul_nonneg hh.le (sq_nonneg _)) (div_nonneg (sq_nonneg _) (sq_nonneg _)))
  linarith only [hm, hi]

/-- The mass ratio is nonnegative, including its frozen zero axis value.
This conclusion is uniform in all parameters. -/
theorem AprioriSetting.mu_nonneg (hset : AprioriSetting e s ε M S h)
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 s) : 0 ≤ S.mu u v :=
  div_nonneg (mul_nonneg (by norm_num) (hset.mass_nonneg hp)) (hset.radius_nonneg hp)

private theorem mass_v_normalized (hset : AprioriSetting e s ε M S h)
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 s) :
    S.mV u v = S.lam u v / 2 *
      ((1 - S.mu u v) * ‖S.theta u v / S.lam u v‖ ^ 2 + S.Q u v ^ 2 / S.r u v ^ 2) := by
  have hl := (hset.c1.lam_pos (u, v) hp).ne'
  simp only [Fields.mV, norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
  field_simp

private theorem mass_v_le (hset : AprioriSetting e s ε M S h)
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 s) :
    S.mV u v ≤ 8 * ε ^ 2 * S.lam u v +
      2 * e ^ 2 * M ^ 2 * ε ^ 2 * S.lam u v * S.r u v ^ 2 := by
  have hh : 1 - S.mu u v ≤ 1 := sub_le_self _ (hset.mu_nonneg hp)
  have hx : ‖S.theta u v / S.lam u v‖ ^ 2 ≤ 16 * ε ^ 2 := by
    convert pow_le_pow_left₀ (norm_nonneg _) (hset.box (u, v) hp).2.2.2.2.2.2.1 2 using 1
    ring
  rw [mass_v_normalized hset hp]
  calc
    _ ≤ S.lam u v / 2 * (1 * (16 * ε ^ 2) +
        4 * e ^ 2 * M ^ 2 * ε ^ 2 * S.r u v ^ 2) := by
      gcongr
      · exact div_nonneg (hset.c1.lam_pos (u, v) hp).le (by norm_num)
      · exact hset.charge_sq_div_le hp
    _ = _ := by ring

/-- The explicit polynomial mass bound, with universal coefficients `8` and
`2/3`, independent of the coupling, triangle, background and higher data norms. -/
theorem AprioriSetting.mass_le (hset : AprioriSetting e s ε M S h)
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 s) :
    S.m u v ≤ 8 * ε ^ 2 * S.r u v +
      (2 / 3) * e ^ 2 * M ^ 2 * ε ^ 2 * S.r u v ^ 3 := by
  have hs : MapsTo (fun x => (u, x)) (Icc u v) (triangle 0 s) :=
    fun x hx => ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩
  have cr := hset.c1.c1_r.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hs
  have cm := hset.c1.c1_m.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hs
  let F (x : ℝ) := 8 * ε ^ 2 * S.r u x +
    (2 / 3) * e ^ 2 * M ^ 2 * ε ^ 2 * S.r u x ^ 3 - S.m u x
  have hd (x : ℝ) (hx : x ∈ Ioo u v) :
      HasDerivAt F (8 * ε ^ 2 * S.lam u x +
        2 * e ^ 2 * M ^ 2 * ε ^ 2 * S.lam u x * S.r u x ^ 2 - S.mV u x) x := by
    have hxp := hs ⟨hx.1.le, hx.2.le⟩
    have dr := (hasDerivWithinAt_pdV hset.c1.c1_r hxp hs).hasDerivAt
      (Icc_mem_nhds hx.1 hx.2)
    have dm := (hasDerivWithinAt_pdV hset.c1.c1_m hxp hs).hasDerivAt
      (Icc_mem_nhds hx.1 hx.2)
    rw [(hset.c1.eq_v (u, x) hxp hx.1).1] at dr
    rw [(hset.c1.eq_v (u, x) hxp hx.1).2.2.1] at dm
    convert ((dr.const_mul (8 * ε ^ 2)).add
      ((dr.pow 3).const_mul ((2 / 3) * e ^ 2 * M ^ 2 * ε ^ 2))).sub dm using 1
    ring
  have hmono : MonotoneOn F (Icc u v) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc u v)
      (((cr.const_mul _).add ((cr.pow 3).const_mul _)).sub cm)
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      change 0 ≤ deriv F x
      rw [(hd x hx).deriv]
      exact sub_nonneg.mpr (mass_v_le hset (hs ⟨hx.1.le, hx.2.le⟩))
  have hf := hmono ⟨le_rfl, hp.2.1⟩ ⟨hp.2.1, le_rfl⟩ hp.2.1
  have hau := hset.c1.axis u (hs ⟨le_rfl, hp.2.1⟩)
  dsimp [F] at hf
  rw [hau.1, hau.2.1] at hf
  linarith only [hf]

/-- The sharp pointwise mass-ratio estimate from the axis, with universal
coefficients `16` and `4/3`. No smallness is required. -/
theorem AprioriSetting.mu_le (hset : AprioriSetting e s ε M S h)
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 s) :
    S.mu u v ≤ 16 * ε ^ 2 + (4 / 3) * e ^ 2 * M ^ 2 * ε ^ 2 * S.r u v ^ 2 := by
  by_cases hr : S.r u v = 0
  · simp only [Fields.mu, hr, div_zero]
    positivity
  have hrp := lt_of_le_of_ne (hset.radius_nonneg hp) (Ne.symm hr)
  rw [Fields.mu, div_le_iff₀ hrp]
  have hm := mul_le_mul_of_nonneg_left (hset.mass_le hp) (by norm_num : (0 : ℝ) ≤ 2)
  convert hm using 1
  ring

/-- [node restart-sec-independent-area#pointwise-mass-bound]
Axis-integrated ordinary mass gives the pointwise small mass ratio
(`charged_SF_new_version.tex:L4819–L4828`). `C` is universal: independent of `e,s,ε,M,S,h`
and all higher initial derivatives. No smallness assumption is needed. -/
theorem pointwise_mass_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (e s ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
      AprioriSetting e s ε M S h → ∀ u v, (u, v) ∈ triangle 0 s →
        0 ≤ S.mu u v ∧ S.mu u v ≤ C * ε ^ 2 * (1 + e ^ 2 * M ^ 2 * S.r u v ^ 2) := by
  refine ⟨16, by norm_num, ?_⟩
  intro e s ε M S h hset u v hp
  refine ⟨hset.mu_nonneg hp, (hset.mu_le hp).trans ?_⟩
  have hn : 0 ≤ e ^ 2 * M ^ 2 * ε ^ 2 * S.r u v ^ 2 := by positivity
  nlinarith only [hn]

end EmcsfAcExtension.Local
