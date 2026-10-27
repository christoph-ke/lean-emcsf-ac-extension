module

public import EmcsfAcExtension.Local.Apriori.SmoothSupCenter
public import EmcsfAcExtension.Local.Defs.Renormalized
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Apriori.Mass

/-! # Bounded geometric transport from linear scalar decay

The quadratic center orders remove the apparent inverse-square radius
in the common geometric source. All constants depend only on displayed
parameter and scalar size bounds, before the field is chosen.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local

private theorem curvature_ratios {e T ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) {u v : ℝ} (hp : (u, v) ∈ triangle 0 T) :
    curv S u v = (S.mu u v : ℂ) + (1 - S.mu u v) *
      (S.theta u v / S.lam u v) * starRingEnd ℂ (S.xi u v / S.nu u v) := by
  have hl : (S.lam u v : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hset.c1.lam_pos _ hp).ne'
  have hn : (S.nu u v : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hset.c1.nu_neg _ hp).ne
  rw [map_div₀, Complex.conj_ofReal]
  dsimp only [curv]
  field_simp [hl, hn]

/-- A common bound for both scalar decay coefficients controls the
geometric source and the mixed radius source. The constant is chosen
after `e,R,M,D` and before `ε,S,h`, uniformly in all additional derivatives
and in the constructed field. The estimate includes the totalized axis. -/
theorem smooth_geometry_source_of_bound (e R M D : ℝ) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T ε : ℝ) (S : Fields) (h : ℝ → ℂ), T ≤ R →
      AprioriSetting e T ε M S h →
      (∀ q ∈ triangle 0 T,
        ‖S.theta q.1 q.2 / S.lam q.1 q.2‖ ≤ D * S.r q.1 q.2 ∧
        ‖S.xi q.1 q.2 / S.nu q.1 q.2‖ ≤ D * S.r q.1 q.2) →
      ∀ u v, (u, v) ∈ triangle 0 T →
        |geomSource S u v| ≤ C ∧ |S.rUV u v| ≤ C * S.r u v := by
  let Q := 4 * e ^ 2 * M ^ 2 * D ^ 2 * R ^ 2
  let U := 2 * (D ^ 2 + Q)
  let C := 1 + 16 * (U + D ^ 2 + Q)
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro T ε S h hTR hset hdecay u v hp
  have hT := hset.pos
  have hpow := pow_le_pow_left₀ hT.le hTR 2
  have hr0 := hset.radius_nonneg hp
  have hμ0 := hset.mu_nonneg hp
  have hμ : S.mu u v ≤ U * S.r u v ^ 2 := by
    apply ((smooth_mass_center_of_bound hset hD
      (fun q hq => (hdecay q hq).1) hp).2).trans
    dsimp only [U, Q]
    gcongr
  have hq : S.Q u v ^ 2 / S.r u v ^ 2 ≤ Q * S.r u v ^ 2 := by
    apply (smooth_charge_square_of_bound hset hD
      (fun q hq => (hdecay q hq).1) hp).trans
    dsimp only [Q]
    gcongr
  have hq0 : 0 ≤ S.Q u v ^ 2 / S.r u v ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hd := (hset.box (u, v) hp).2.2.2.2.1
  have hd0 := hset.c1.one_sub_mu_pos (u, v) hp
  have hd1 : 1 - S.mu u v ≤ 1 := by linarith only [hμ0]
  have hl := hset.c1.lam_pos (u, v) hp
  have hn := hset.c1.nu_neg (u, v) hp
  have hl1 : |S.lam u v| ≤ 1 := by
    rw [abs_of_pos hl]
    exact (hset.box (u, v) hp).2.1
  have hn1 : |S.nu u v| ≤ 1 := by
    rw [abs_of_neg hn]
    exact (hset.box (u, v) hp).2.2.2.1
  have hcurv : ‖curv S u v‖ ≤ (U + D ^ 2) * S.r u v ^ 2 := by
    rw [curvature_ratios hset hp]
    calc
      _ ≤ ‖(S.mu u v : ℂ)‖ + ‖(1 - (S.mu u v : ℂ)) *
          (S.theta u v / S.lam u v) * starRingEnd ℂ (S.xi u v / S.nu u v)‖ :=
        norm_add_le _ _
      _ = S.mu u v + (1 - S.mu u v) * ‖S.theta u v / S.lam u v‖ *
          ‖S.xi u v / S.nu u v‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hμ0,
          ← Complex.ofReal_one, ← Complex.ofReal_sub, abs_of_pos hd0, RCLike.norm_conj]
      _ ≤ U * S.r u v ^ 2 + 1 * (D * S.r u v) * (D * S.r u v) := by
        gcongr
        · exact (hdecay (u, v) hp).1
        · exact (hdecay (u, v) hp).2
      _ = _ := by ring
  by_cases hr : S.r u v = 0
  · simp only [geomSource, Fields.rUV, hr, zero_pow (by decide : 2 ≠ 0),
      mul_zero, div_zero, zero_mul, neg_zero, abs_zero]
    exact ⟨hC.le, le_rfl⟩
  have hrp : 0 < S.r u v := lt_of_le_of_ne hr0 (Ne.symm hr)
  have hcoeff : |2 * S.nu u v * S.lam u v /
      ((1 - S.mu u v) * S.r u v ^ 2)| ≤ 4 / S.r u v ^ 2 := by
    simp only [abs_div, abs_mul, abs_pow, abs_of_pos hd0, abs_of_pos hrp,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      _ ≤ (2 * 1 * 1) / ((1 / 2) * S.r u v ^ 2) := by
        gcongr
      _ = _ := by ring
  have hreal : |(curv S u v).re - 2 * (S.Q u v ^ 2 / S.r u v ^ 2)| ≤
      (U + D ^ 2 + 2 * Q) * S.r u v ^ 2 := by
    calc
      _ ≤ |(curv S u v).re| + |2 * (S.Q u v ^ 2 / S.r u v ^ 2)| := abs_sub _ _
      _ ≤ (U + D ^ 2) * S.r u v ^ 2 + 2 * (Q * S.r u v ^ 2) := by
        rw [abs_mul, abs_of_nonneg hq0]
        rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        exact add_le_add ((Complex.abs_re_le_norm _).trans hcurv)
          (mul_le_mul_of_nonneg_left hq (by norm_num))
      _ = _ := by ring
  constructor
  · rw [geomSource, abs_mul, abs_neg]
    calc
      _ ≤ (4 / S.r u v ^ 2) * ((U + D ^ 2 + 2 * Q) * S.r u v ^ 2) :=
        mul_le_mul hcoeff hreal (abs_nonneg _) (by positivity)
      _ = 4 * (U + D ^ 2 + 2 * Q) := by field_simp
      _ ≤ C := by dsimp only [C]; linarith only [hU, hQ, sq_nonneg D]
  · have hdiff : |S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2| ≤
        (U + Q) * S.r u v ^ 2 := by
      apply (abs_sub _ _).trans
      rw [abs_of_nonneg hμ0, abs_of_nonneg hq0]
      nlinarith only [hμ, hq]
    rw [Fields.rUV, abs_mul, abs_div, abs_div, abs_mul,
      abs_of_pos hrp, abs_of_pos hd0]
    calc
      _ ≤ (1 * 1) / S.r u v * (((U + Q) * S.r u v ^ 2) / (1 / 2)) := by
        gcongr
      _ = 2 * (U + Q) * S.r u v := by field_simp
      _ ≤ _ := by
        have hh : 2 * (U + Q) ≤ C := by
          dsimp only [C]
          linarith only [hU, hQ, sq_nonneg D]
        exact mul_le_mul_of_nonneg_right hh hr0

end EmcsfAcExtension.Local
