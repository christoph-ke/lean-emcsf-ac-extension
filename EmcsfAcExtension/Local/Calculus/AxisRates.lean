module

public import EmcsfAcExtension.Local.Calculus.AxisRatio
public import EmcsfAcExtension.Local.Calculus.AxisPower
public import EmcsfAcExtension.Local.Calculus.AxisScalarFields
import EmcsfAcExtension.Infra.Calculus.PartialsC1

/-! # Center decay from classical characteristic constraints

Continuous factors, rather than uniform numerical estimates, express the orders needed
at the regular center. Constants are not selected. All functions are constructed by
section integrals on the given triangle.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local

/-- The radius has a strictly positive continuous factor of `v-u` on the entire
positive-time triangle. Its diagonal value is the outgoing expansion. -/
theorem exists_positive_radius_factor_aux {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T)) :
    ∃ R : (ℝ × ℝ) → ℝ, ContinuousOn R (triangle 0 T) ∧
      (∀ p ∈ triangle 0 T, 0 < R p) ∧
      (∀ u v, (u, v) ∈ triangle 0 T → S.r u v = (v - u) * R (u, v)) ∧
      (∀ t ∈ Icc 0 T, R (t, t) = S.lam t t) := by
  obtain ⟨R, cR, hR, haxis⟩ := exists_continuous_axis_factor_aux hT hS.c1_r
  have heq (u v : ℝ) (hp : (u, v) ∈ triangle 0 T) :
      S.r u v = (v - u) * R (u, v) := by
    simpa [(hS.axis u ⟨hp.1, le_rfl, hp.2.1.trans hp.2.2⟩).1] using hR u v hp
  have hdiag (t : ℝ) (ht : t ∈ Icc 0 T) : R (t, t) = S.lam t t := by
    rw [haxis t ht, (radius_axis_partials_aux hT hS ht).2]
  refine ⟨R, cR, ?_, heq, hdiag⟩
  intro p hp
  rcases p with ⟨u, v⟩
  by_cases huv : u < v
  · have h := hS.r_pos (u, v) hp huv
    rw [heq u v hp] at h
    exact (mul_pos_iff.mp h).resolve_right
      (fun hneg => (not_lt.mpr huv.le) (sub_neg.mp hneg.1)) |>.2
  · have huv' : u = v := le_antisymm hp.2.1 (not_lt.mp huv)
    subst v
    rw [hdiag u ⟨hp.1, hp.2.2⟩]
    exact hS.lam_pos _ hp

/-- The charge has a continuous cubic factor in the characteristic distance to
the axis. This is the classical Maxwell center order, without an unspecified
constant or any smoothness beyond the supplied C¹ class. -/
theorem exists_continuous_charge_cubic_factor_aux {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T)) :
    ∃ q : (ℝ × ℝ) → ℝ, ContinuousOn q (triangle 0 T) ∧
      ∀ u v, (u, v) ∈ triangle 0 T → S.Q u v = (v - u) ^ 3 * q (u, v) := by
  obtain ⟨R, cR, hRpos, hrf, hRaxis⟩ := exists_positive_radius_factor_aux hT hS
  have cP := continuousOn_partial_v hS.c1_phi (uniqueDiffOn_triangle hT)
  let G (u v : ℝ) := -e * R (u, v) ^ 2 *
    (starRingEnd ℂ (S.phi u v) * pdV (triangle 0 T) S.phi u v).im
  have cG : ContinuousOn (Function.uncurry G) (triangle 0 T) :=
    ((continuousOn_const.mul (cR.pow 2)).mul
      (Complex.continuous_im.comp_continuousOn (hS.c1_phi.continuousOn.star.mul cP)))
  have heq := eqOn_triangle_of_off_axis_aux hT
    (continuousOn_partial_v hS.c1_Q (uniqueDiffOn_triangle hT))
    ((((continuousOn_snd.sub continuousOn_fst).pow 2).mul cG))
    (fun p hp huv => ?_)
  · exact exists_continuous_axis_power_factor_of_deriv_aux 2 hS.c1_Q cG
      (fun t ht => (hS.axis t ⟨ht.1, le_rfl, ht.2⟩).2.2.1)
      (fun u v hp => heq hp)
  · change pdV (triangle 0 T) S.Q p.1 p.2 = (p.2 - p.1) ^ 2 * G p.1 p.2
    have he := hS.eq_v p hp huv
    have hrC : (S.r p.1 p.2 : ℂ) ≠ 0 := by exact_mod_cast (hS.r_pos p hp huv).ne'
    have ht : S.theta p.1 p.2 =
        (S.r p.1 p.2 : ℂ) * pdV (triangle 0 T) S.phi p.1 p.2 := by
      rw [he.2.2.2.2.2.1]
      dsimp only [Fields.phiV]
      field_simp [hrC]
    rw [he.2.2.2.1]
    dsimp only [Fields.QV, G, Function.uncurry_def]
    rw [ht]
    simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im, zero_mul, add_zero, sub_zero]
    rw [hrf p.1 p.2 hp]
    ring

/-- The charge divided by `r²` has a continuous extension vanishing at the axis.
This is the center order needed in the metric calculation; no size bound is assumed. -/
theorem exists_continuous_charge_square_ratio_aux {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T)) :
    ∃ q : (ℝ × ℝ) → ℝ, ContinuousOn q (triangle 0 T) ∧
      (∀ u v, (u, v) ∈ triangle 0 T → u < v → q (u, v) = S.Q u v / S.r u v ^ 2) ∧
      (∀ t ∈ Icc 0 T, q (t, t) = 0) := by
  obtain ⟨R, cR, hRpos, hrf, _⟩ := exists_positive_radius_factor_aux hT hS
  obtain ⟨q, cq, hq⟩ := exists_continuous_charge_cubic_factor_aux hT hS
  refine ⟨fun p => (p.2 - p.1) * q p / R p ^ 2,
    ((continuousOn_snd.sub continuousOn_fst).mul cq).div (cR.pow 2)
      (fun p hp => pow_ne_zero 2 (hRpos p hp).ne'), ?_, ?_⟩
  · intro u v hp huv
    rw [hrf u v hp, hq u v hp]
    field_simp [(sub_pos.mpr huv).ne', (hRpos (u, v) hp).ne']
  · intro t ht
    simp only [sub_self, zero_mul, zero_div]

/-- The ordinary mass has a continuous cubic factor at the center. Maxwell's
cubic order and the natural scalar constraint make its radial derivative quadratic.
This lemma selects no constants and uses only the classical equations. -/
theorem exists_continuous_mass_cubic_factor_aux {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T)) :
    ∃ m : (ℝ × ℝ) → ℝ, ContinuousOn m (triangle 0 T) ∧
      ∀ u v, (u, v) ∈ triangle 0 T → S.m u v = (v - u) ^ 3 * m (u, v) := by
  obtain ⟨R, cR, hRpos, hrf, _⟩ := exists_positive_radius_factor_aux hT hS
  obtain ⟨q, cq, hq, _⟩ := exists_continuous_charge_square_ratio_aux hT hS
  have cP := continuousOn_partial_v hS.c1_phi (uniqueDiffOn_triangle hT)
  have cm := continuousOn_mu_aux hT hS
  let G (u v : ℝ) := R (u, v) ^ 2 *
    ((1 - S.mu u v) * ‖pdV (triangle 0 T) S.phi u v‖ ^ 2 / (2 * S.lam u v) +
      q (u, v) ^ 2 * S.lam u v / 2)
  have cG : ContinuousOn (Function.uncurry G) (triangle 0 T) :=
    (cR.pow 2).mul
      ((((continuousOn_const.sub cm).mul (cP.norm.pow 2)).div
        (continuousOn_const.mul hS.c1_lam.continuousOn)
        (fun p hp => mul_ne_zero (by norm_num) (hS.lam_pos p hp).ne')).add
      (((cq.pow 2).mul hS.c1_lam.continuousOn).div_const 2))
  have heq := eqOn_triangle_of_off_axis_aux hT
    (continuousOn_partial_v hS.c1_m (uniqueDiffOn_triangle hT))
    (((continuousOn_snd.sub continuousOn_fst).pow 2).mul cG)
    (fun p hp huv => ?_)
  · exact exists_continuous_axis_power_factor_of_deriv_aux 2 hS.c1_m cG
      (fun t ht => (hS.axis t ⟨ht.1, le_rfl, ht.2⟩).2.1)
      (fun u v hp => heq hp)
  · change pdV (triangle 0 T) S.m p.1 p.2 = (p.2 - p.1) ^ 2 * G p.1 p.2
    rw [(hS.eq_v p hp huv).2.2.1]
    dsimp only [Fields.mV, G, Function.uncurry_def]
    rw [theta_eq_radius_partial_aux hT hS hp, hq p.1 p.2 hp huv]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    have hr := (hS.r_pos p hp huv).ne'
    have hl := (hS.lam_pos p hp).ne'
    rw [hrf p.1 p.2 hp]
    field_simp [hr, hl, (hRpos p hp).ne', (sub_pos.mpr huv).ne']

/-- The mass divided by `r²` has a continuous extension vanishing at the axis.
Together with the charge-square quotient this removes the singular metric source. -/
theorem exists_continuous_mass_square_ratio_aux {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T)) :
    ∃ m : (ℝ × ℝ) → ℝ, ContinuousOn m (triangle 0 T) ∧
      (∀ u v, (u, v) ∈ triangle 0 T → u < v → m (u, v) = S.m u v / S.r u v ^ 2) ∧
      (∀ t ∈ Icc 0 T, m (t, t) = 0) := by
  obtain ⟨R, cR, hRpos, hrf, _⟩ := exists_positive_radius_factor_aux hT hS
  obtain ⟨m, cm, hm⟩ := exists_continuous_mass_cubic_factor_aux hT hS
  refine ⟨fun p => (p.2 - p.1) * m p / R p ^ 2,
    ((continuousOn_snd.sub continuousOn_fst).mul cm).div (cR.pow 2)
      (fun p hp => pow_ne_zero 2 (hRpos p hp).ne'), ?_, ?_⟩
  · intro u v hp huv
    rw [hrf u v hp, hm u v hp]
    field_simp [(sub_pos.mpr huv).ne', (hRpos (u, v) hp).ne']
  · intro t ht
    simp only [sub_self, zero_mul, zero_div]

/-- Both cross expansion partials vanish at the regular center. This follows from
the cubic mass and charge factors and holds without any axis-gauge hypothesis. -/
theorem expansion_axis_cross_partials_aux {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    pdU (triangle 0 T) S.lam t t = 0 ∧ pdV (triangle 0 T) S.nu t t = 0 := by
  obtain ⟨m, cm, hm, hmaxis⟩ := exists_continuous_mass_square_ratio_aux hT hS
  obtain ⟨q, cq, hq, hqaxis⟩ := exists_continuous_charge_square_ratio_aux hT hS
  let E (u v : ℝ) := S.nu u v * S.lam u v / (1 - S.mu u v) *
    (2 * m (u, v) - S.r u v * q (u, v) ^ 2)
  have cE : ContinuousOn (Function.uncurry E) (triangle 0 T) :=
    ((hS.c1_nu.continuousOn.mul hS.c1_lam.continuousOn).div
      (continuousOn_const.sub (continuousOn_mu_aux hT hS))
      (fun p hp => (hS.one_sub_mu_pos p hp).ne')).mul
      ((continuousOn_const.mul cm).sub (hS.c1_r.continuousOn.mul (cq.pow 2)))
  have he (p : ℝ × ℝ) (hp : p ∈ triangle 0 T) (huv : p.1 < p.2) :
      S.rUV p.1 p.2 = E p.1 p.2 := by
    dsimp only [Fields.rUV, E]
    rw [hm p.1 p.2 hp huv, hq p.1 p.2 hp huv]
    dsimp only [Fields.mu]
    have hr := (hS.r_pos p hp huv).ne'
    have hmu := (hS.one_sub_mu_pos p hp).ne'
    change 1 - 2 * S.m p.1 p.2 / S.r p.1 p.2 ≠ 0 at hmu
    field_simp [hr, hmu]
  have hl := eqOn_triangle_of_off_axis_aux hT
    (continuousOn_partial_u hS.c1_lam (uniqueDiffOn_triangle hT)) cE
    (fun p hp huv => (hS.eq_u p hp huv).2.1.trans (he p hp huv))
  have hn := eqOn_triangle_of_off_axis_aux hT
    (continuousOn_partial_v hS.c1_nu (uniqueDiffOn_triangle hT)) cE
    (fun p hp huv => (hS.eq_v p hp huv).2.1.trans (he p hp huv))
  have hp : (t, t) ∈ triangle 0 T := ⟨ht.1, le_rfl, ht.2⟩
  have hz : E t t = 0 := by
    simp only [E, hmaxis t ht, hqaxis t ht, mul_zero, zero_pow (by decide : 2 ≠ 0),
      sub_zero]
  exact ⟨(hl hp).trans hz, (hn hp).trans hz⟩

end EmcsfAcExtension.Local
