module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.SmoothSupRadial
import EmcsfAcExtension.Local.Apriori.Hardy
import EmcsfAcExtension.Local.Apriori.Mass
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # A datum bound for the initial renormalized supremum

A single bound for the initial derivative is chosen before the constructed
apex and solution. The cubic initial correction costs only a universal
multiple of that bound, as at the end of internal project record's geometric recovery.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem initial_decay {e s ε M D : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e s ε M S h) (hD : 0 ≤ D)
    (hb : ∀ v ∈ Icc 0 s, ‖pdV (triangle 0 s) S.a 0 v‖ ≤ D)
    {v : ℝ} (hv : v ∈ Icc 0 s) :
    ‖S.theta 0 v / S.lam 0 v‖ ≤ 4 * S.r 0 v * D := by
  rcases eq_or_lt_of_le hv.1 with rfl | hv0
  · have ha := (hset.c1.axis 0 ⟨le_rfl, le_rfl, hv.2⟩).2.2.2.2.1
    have hz : S.theta 0 0 / (S.lam 0 0 : ℂ) = 0 := by
      simpa only [Fields.a, add_eq_left] using ha
    simp only [hz, norm_zero, (hset.c1.axis 0 ⟨le_rfl, le_rfl, hv.2⟩).1,
      mul_zero, zero_mul, le_refl]
  have hr := hset.c1.r_pos (0, v) ⟨le_rfl, hv.1, hv.2⟩ hv0
  have cr := hset.c1.c1_r.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn
    (show MapsTo (fun x => (0, x)) (Icc 0 v) (triangle 0 s) from
      fun _ hx => ⟨le_rfl, hx.1, hx.2.trans hv.2⟩)
  have cd := (continuousOn_pdV hset.c1.c1_a (uniqueDiffOn_triangle hset.pos)).comp
    (continuous_const.prodMk continuous_id).continuousOn
    (show MapsTo (fun x => (0, x)) (Icc 0 v) (triangle 0 s) from
      fun _ hx => ⟨le_rfl, hx.1, hx.2.trans hv.2⟩)
  have hi : (∫ x in 0..v, S.r 0 x * ‖pdV (triangle 0 s) S.a 0 x‖) ≤
      S.r 0 v * D * v := by
    calc
      _ ≤ ∫ _ in 0..v, S.r 0 v * D := by
        apply intervalIntegral.integral_mono_on hv.1
          ((cr.mul cd.norm).intervalIntegrable_of_Icc hv.1) intervalIntegrable_const
        intro x hx
        apply mul_le_mul _ (hb x ⟨hx.1, hx.2.trans hv.2⟩) (norm_nonneg _) hr.le
        change S.r 0 x ≤ S.r 0 v
        rw [(hset.data.1 x ⟨hx.1, hx.2.trans hv.2⟩).1, (hset.data.1 v hv).1]
        exact div_le_div_of_nonneg_right hx.2 (by norm_num)
      _ = _ := by rw [intervalIntegral.integral_const]; ring
  calc
    _ ≤ (S.r 0 v)⁻¹ * ∫ x in 0..v, S.r 0 x * ‖pdV (triangle 0 s) S.a 0 x‖ :=
      bv_hardy_out hset.c1 le_rfl hv0 hv.2
    _ ≤ (S.r 0 v)⁻¹ * (S.r 0 v * D * v) :=
      mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hr.le)
    _ = v * D := by field_simp [hr.ne']
    _ ≤ _ := by
      rw [(hset.data.1 v hv).1]
      nlinarith only [mul_nonneg hv.1 hD]

private theorem initial_renormalized_bound {e s ε M D : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e s ε M S h) (hε : ε ≤ 1 / 8) (hD : 0 ≤ D)
    (hb : ∀ v ∈ Icc 0 s, ‖pdV (triangle 0 s) S.a 0 v‖ ≤ D)
    {v : ℝ} (hv : v ∈ Icc 0 s) : ‖jC1 (triangle 0 s) S 0 v‖ ≤ 2 * D := by
  have hp : (0, v) ∈ triangle 0 s := ⟨le_rfl, hv.1, hv.2⟩
  have hr0 := hset.radius_nonneg hp
  have hd := initial_decay hset hD hb hv
  have hl : |S.lam 0 v| ≤ 1 := by
    rw [abs_of_pos (hset.c1.lam_pos _ hp)]
    exact (hset.box _ hp).2.1
  have hratio : |S.lam 0 v / S.r 0 v| * ‖S.theta 0 v / S.lam 0 v‖ ≤ 4 * D := by
    by_cases hr : S.r 0 v = 0
    · simp only [hr, div_zero, abs_zero, zero_mul]
      positivity
    have hh := mul_le_mul_of_nonneg_left hd (abs_nonneg (S.lam 0 v / S.r 0 v))
    have heq : |S.lam 0 v / S.r 0 v| * (4 * S.r 0 v * D) =
        4 * |S.lam 0 v| * D := by
      rw [abs_div, abs_of_nonneg hr0]
      field_simp [hr]
    rw [heq] at hh
    exact hh.trans (by nlinarith only [hl, hD])
  have hε0 := hset.eps_nonneg
  have hf2 : ‖S.theta 0 v / S.lam 0 v‖ ^ 2 ≤ 16 * ε ^ 2 := by
    convert pow_le_pow_left₀ (norm_nonneg _)
      (hset.box _ hp).2.2.2.2.2.2.1 2 using 1; ring
  have hfactor : ‖(1 : ℂ) - (S.mu 0 v : ℂ)‖ ≤ 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (hset.c1.one_sub_mu_pos _ hp)]
    linarith only [hset.mu_nonneg hp]
  have hcubic : ‖S.lam 0 v / S.r 0 v * (‖S.theta 0 v / S.lam 0 v‖ : ℂ) ^ 2 *
      (S.theta 0 v / S.lam 0 v)‖ ≤ 64 * ε ^ 2 * D := by
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      ← Complex.ofReal_div]
    calc
      _ = ‖S.theta 0 v / S.lam 0 v‖ ^ 2 *
          (|S.lam 0 v / S.r 0 v| * ‖S.theta 0 v / S.lam 0 v‖) := by ring
      _ ≤ (16 * ε ^ 2) * (4 * D) := mul_le_mul hf2 hratio (by positivity) (by positivity)
      _ = _ := by ring
  have hsmall : 64 * ε ^ 2 ≤ 1 := by nlinarith only [hε0, hε]
  rw [jC1, norm_mul]
  calc
    _ ≤ 1 * ‖pdV (triangle 0 s) S.a 0 v -
        S.lam 0 v / S.r 0 v * (‖S.theta 0 v / S.lam 0 v‖ : ℂ) ^ 2 *
          (S.theta 0 v / S.lam 0 v)‖ :=
      mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)
    _ ≤ D + 64 * ε ^ 2 * D := by
      rw [one_mul]
      exact (norm_sub_le _ _).trans (add_le_add (hb v hv) hcubic)
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hsmall hD]

/-- A single finite size for the initial derivative and initial `j` is
chosen after the fixed `T,h` and before every constructed apex and
solution. The numeric multiplier two is universal. Only C¹ data are needed;
no bound on an exterior representative of the datum is used. -/
theorem smooth_initial_sup_size_aux {T : ℝ} {h : ℝ → ℂ} (hT : 0 < T)
    (hh : ContDiffOn ℝ 1 h (Icc 0 T)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (e s ε M : ℝ) (S : Fields),
      0 < s → s ≤ T → AprioriSetting e s ε M S h → ε ≤ 1 / 8 →
      (∀ v ∈ Icc 0 s, ‖pdV (triangle 0 s) S.a 0 v‖ ≤ D) ∧
      (⨆ v ∈ Icc 0 s, ‖jC1 (triangle 0 s) S 0 v‖ₑ) ≤ ENNReal.ofReal (2 * D) := by
  have cd := hh.continuousOn_derivWithin (uniqueDiffOn_Icc hT) (by norm_num)
  obtain ⟨A, hA⟩ := isCompact_Icc.bddAbove_image cd.norm
  let D := max 0 A
  have hD : 0 ≤ D := le_max_left _ _
  refine ⟨D, hD, ?_⟩
  intro e s ε M S hs hsT hset hε
  have hb (v : ℝ) (hv : v ∈ Icc 0 s) : ‖pdV (triangle 0 s) S.a 0 v‖ ≤ D := by
    have hvT : v ∈ Icc 0 T := ⟨hv.1, hv.2.trans hsT⟩
    have hsmap : MapsTo (fun x => (0, x)) (Icc 0 s) (triangle 0 s) :=
      fun x hx => ⟨le_rfl, hx.1, hx.2⟩
    have dh := (hh.differentiableOn (by norm_num) v hvT).hasDerivWithinAt.mono
      (Icc_subset_Icc le_rfl hsT)
    have da := (hasDerivWithinAt_pdV hset.c1.c1_a (hsmap hv) hsmap).congr
      (fun x hx => (hset.data.1 x hx).2.symm) ((hset.data.1 v hv).2.symm)
    have he := (uniqueDiffOn_Icc hs v hv).eq_deriv _ da dh
    rw [he]
    exact (hA (mem_image_of_mem _ hvT)).trans (le_max_right _ _)
  refine ⟨hb, ?_⟩
  apply iSup₂_le
  intro v hv
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (initial_renormalized_bound hset hε hD hb hv)

end EmcsfAcExtension.Local
