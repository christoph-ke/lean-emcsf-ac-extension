module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Apriori.GeometryBoxRay
import EmcsfAcExtension.Local.Apriori.GeometryBoxFlux
import EmcsfAcExtension.Local.Apriori.GeometryEnvelopeInitial
import EmcsfAcExtension.Local.Apriori.Mass
import EmcsfAcExtension.Local.Apriori.AreaJAux

/-! # Quantitative improvement of the geometric bootstrap box

The mass constraint first controls the gap. Integrated Raychaudhuri then
controls the outgoing expansion from the initial section and the incoming
expansion from the axis, without a separate Doppler assumption
(`charged_SF_new_version.tex:L4829–L4838`, approved internal project record (28)).
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

/-- The mass ratio is at most `22 ε²` when the charged scale is at most one.
The numerical coefficient depends only on the fixed box and is uniform in
all data, including higher derivatives. No envelope closure is needed. -/
theorem AprioriSetting.mu_le_twenty_two {e T ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) (hδ : |e| * (T / 2) * M ≤ 1)
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 T) : S.mu u v ≤ 22 * ε ^ 2 := by
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans hset.one_le_M
  have hδ0 : 0 ≤ |e| * (T / 2) * M := by have := hset.pos; positivity
  have hδ2 : (|e| * (T / 2) * M) ^ 2 ≤ 1 := by nlinarith only [hδ, hδ0]
  have hr0 := hset.radius_nonneg hp
  have hr : S.r u v ≤ T := (Area.radius_bounds hset hp.1 hp.2.1 hp.2.2).2.trans
    (by linarith only [hp.1, hp.2.2])
  have hscale : e ^ 2 * M ^ 2 * S.r u v ^ 2 ≤
      4 * (|e| * (T / 2) * M) ^ 2 := by
    have hi := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr 2)
      (show 0 ≤ e ^ 2 * M ^ 2 by positivity)
    convert hi using 1
    simp only [mul_pow, sq_abs]
    ring
  have hi := mul_le_mul_of_nonneg_right (hscale.trans
    (mul_le_mul_of_nonneg_left hδ2 (by norm_num : (0 : ℝ) ≤ 4))) (sq_nonneg ε)
  have hm := hset.mu_le hp
  nlinarith only [hm, hi, sq_nonneg ε]

private theorem quotient_gap_error {x m : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hm : 0 ≤ m) (hH : 1 / 2 ≤ 1 - m) : |x - x / (1 - m)| ≤ 2 * m := by
  have hHp : 0 < 1 - m := lt_of_lt_of_le (by norm_num) hH
  have hid : x - x / (1 - m) = -(x * m / (1 - m)) := by field_simp; ring
  rw [hid, abs_neg, abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ hHp).mpr
  have hxm := mul_le_mul_of_nonneg_right hx1 hm
  have hmh := mul_le_mul_of_nonneg_left hH (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hm)
  nlinarith only [hxm, hmh]

/-- [node restart-sec-independent-area#geometry-bootstrap-improvement]
Both expansions differ from `1/2`, and the gap differs from one, by at most
`C ε²` in total. The positive thresholds and `C` precede all data and depend
only on the fixed bootstrap box, uniformly in higher initial derivatives.
The proof has no Doppler premise. -/
theorem geometry_bootstrap_improvement : ∃ ε₀ δ₀ C : ℝ,
    0 < ε₀ ∧ 0 < δ₀ ∧ 0 < C ∧
    ∀ (e T ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e T ε M S h → ε ≤ ε₀ → |e| * (T / 2) * M ≤ δ₀ →
    ∀ u v, (u, v) ∈ triangle 0 T →
      |S.lam u v - 1 / 2| + |-S.nu u v - 1 / 2| + |S.mu u v| ≤ C * ε ^ 2 := by
  obtain ⟨ε₁, δ₁, hε₁, hδ₁, hflux⟩ := closed_quadratic_scalar_budgets
  refine ⟨min ε₁ (1 / 128), min δ₁ 1,
    400, lt_min hε₁ (by norm_num), lt_min hδ₁ (by norm_num), by norm_num, ?_⟩
  intro e T ε M S h hset hε hδ u v hp
  have he := hε.trans (min_le_right _ _)
  have hd := hδ.trans (min_le_right _ _)
  have hε0 := hset.eps_nonneg
  have hL : 14 * ε ^ 2 ≤ 1 := by nlinarith only [he, hε0]
  have hf := hflux e T ε M S h hset (hε.trans (min_le_left _ _))
    (hδ.trans (min_le_left _ _))
  have mu (a b : ℝ) (hab : (a, b) ∈ triangle 0 T) := hset.mu_le_twenty_two hd hab
  have herr (a b : ℝ) (hab : (a, b) ∈ triangle 0 T) :
      |S.lam a b - S.lam a b / (1 - S.mu a b)| ≤ 44 * ε ^ 2 ∧
      |-S.nu a b - -S.nu a b / (1 - S.mu a b)| ≤ 44 * ε ^ 2 := by
    have hb := hset.box (a, b) hab
    constructor
    · exact (quotient_gap_error (hset.c1.lam_pos (a, b) hab).le hb.2.1
        (hset.mu_nonneg hab) hb.2.2.2.2.1).trans (by linarith only [mu a b hab])
    · exact (quotient_gap_error (neg_pos.mpr (hset.c1.nu_neg (a, b) hab)).le
        hb.2.2.2.1 (hset.mu_nonneg hab) hb.2.2.2.2.1).trans
          (by linarith only [mu a b hab])
  have hlam (a b : ℝ) (hab : (a, b) ∈ triangle 0 T) :
      |S.lam a b - 1 / 2| ≤ 116 * ε ^ 2 := by
    have h0b : (0, b) ∈ triangle 0 T := ⟨le_rfl, hab.1.trans hab.2.1, hab.2.2⟩
    have H0 := (hset.box (0, b) h0b).2.2.2.2.1
    have hl0 := hset.initial_lam ⟨h0b.2.1, h0b.2.2⟩
    have hi := hset.incoming_ray_integral hab.1 hab.2.1 hab.2.2
    have hq0 : 0 ≤ ∫ x in 0..a,
        -S.nu x b / S.r x b * ‖S.xi x b / S.nu x b‖ ^ 2 := by
      apply intervalIntegral.integral_nonneg hab.1
      intro x hx
      have hxD : (x, b) ∈ triangle 0 T := ⟨hx.1, hx.2.trans hab.2.1, hab.2.2⟩
      exact mul_nonneg (div_nonneg (neg_pos.mpr (hset.c1.nu_neg (x, b) hxD)).le
        (hset.radius_nonneg hxD)) (sq_nonneg _)
    have hm := intervalIntegral.integral_mono_interval le_rfl hab.1 hab.2.1
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        have hxD : (x, b) ∈ triangle 0 T := ⟨hx.1.le, hx.2, hab.2.2⟩
        exact mul_nonneg (div_nonneg (neg_pos.mpr (hset.c1.nu_neg (x, b) hxD)).le
          (hset.radius_nonneg hxD)) (sq_nonneg _))
      (hset.quadratic_scalar_integrable le_rfl h0b.2.1 hab.2.2).2
    have hlog : |Real.log (S.lam a b / (1 - S.mu a b)) -
        Real.log (S.lam 0 b / (1 - S.mu 0 b))| ≤ 14 * ε ^ 2 := by
      rw [hi, abs_neg, abs_of_nonneg hq0]
      exact hm.trans (hf 0 b le_rfl h0b.2.1 hab.2.2).2
    have hq := abs_sub_le_twice_log_error
      (div_pos (hset.c1.lam_pos (a, b) hab) (hset.c1.one_sub_mu_pos (a, b) hab))
      (div_pos (hset.c1.lam_pos (0, b) h0b) (hset.c1.one_sub_mu_pos (0, b) h0b))
      (by rw [hl0]; exact (div_le_one (hset.c1.one_sub_mu_pos (0, b) h0b)).mpr H0)
      hlog hL
    have ht := abs_sub_le (S.lam a b) (S.lam a b / (1 - S.mu a b)) (1 / 2)
    have ht' := abs_sub_le (S.lam a b / (1 - S.mu a b))
      (S.lam 0 b / (1 - S.mu 0 b)) (1 / 2)
    have herr0 := (herr 0 b h0b).1
    rw [hl0, abs_sub_comm] at herr0
    rw [hl0] at ht' hq
    linarith only [ht, ht', hq, (herr a b hab).1, herr0]
  have hn : |-S.nu u v - 1 / 2| ≤ 188 * ε ^ 2 := by
    have hau : (u, u) ∈ triangle 0 T := ⟨hp.1, le_rfl, hp.2.1.trans hp.2.2⟩
    have ha := hset.c1.axis u hau
    have hna : -S.nu u u = S.lam u u := by linarith only [ha.2.2.2.1]
    have hmu : S.mu u u = 0 := by simp [Fields.mu, ha.1]
    have hi := hset.outgoing_ray_integral hp.1 hp.2.1 hp.2.2
    have hq0 : 0 ≤ ∫ x in u..v,
        S.lam u x / S.r u x * ‖S.theta u x / S.lam u x‖ ^ 2 := by
      apply intervalIntegral.integral_nonneg hp.2.1
      intro x hx
      have hxD : (u, x) ∈ triangle 0 T := ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩
      exact mul_nonneg (div_nonneg (hset.c1.lam_pos (u, x) hxD).le
        (hset.radius_nonneg hxD)) (sq_nonneg _)
    have hlog : |Real.log (-S.nu u v / (1 - S.mu u v)) - Real.log (S.lam u u)| ≤
        14 * ε ^ 2 := by
      rw [hna, hmu, sub_zero, div_one] at hi
      rw [hi, abs_of_nonneg hq0]
      exact (hf u v hp.1 hp.2.1 hp.2.2).1
    have hq := abs_sub_le_twice_log_error
      (div_pos (neg_pos.mpr (hset.c1.nu_neg (u, v) hp))
        (hset.c1.one_sub_mu_pos (u, v) hp))
      (hset.c1.lam_pos (u, u) hau) (hset.box (u, u) hau).2.1 hlog hL
    have ht := abs_sub_le (-S.nu u v) (-S.nu u v / (1 - S.mu u v)) (1 / 2)
    have ht' := abs_sub_le (-S.nu u v / (1 - S.mu u v)) (S.lam u u) (1 / 2)
    linarith only [ht, ht', hq, (herr u v hp).2, hlam u u hau]
  rw [abs_of_nonneg (hset.mu_nonneg hp)]
  linarith only [hlam u v hp, hn, mu u v hp, sq_nonneg ε]

end EmcsfAcExtension.Local
