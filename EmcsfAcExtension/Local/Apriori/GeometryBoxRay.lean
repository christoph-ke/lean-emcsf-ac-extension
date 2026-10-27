module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.GeometryBoxFlux
import EmcsfAcExtension.Local.Calculus.Raychaudhuri
import EmcsfAcExtension.Local.Calculus.AxisRatio
import Mathlib.Analysis.Complex.Exponential

/-! # Integrated logarithmic Raychaudhuri estimates

Both logarithmic identities are integrated in their own null orientation,
including the axis endpoint by continuity. Only the quadratic scalar budgets
are used (`charged_SF_new_version.tex:L4829–L4838`, approved internal project record (28)).
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local

/-- On the interval of positive values whose reference value is at most one,
a logarithmic error of at most one controls the absolute error with universal
coefficient `2`. There are no field or data parameters. -/
theorem abs_sub_le_twice_log_error {a b L : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hb1 : b ≤ 1) (hlog : |Real.log a - Real.log b| ≤ L) (hL : L ≤ 1) :
    |a - b| ≤ 2 * L := by
  have he := Real.abs_exp_sub_one_le (hlog.trans hL)
  have hid : a - b = b * (Real.exp (Real.log a - Real.log b) - 1) := by
    rw [Real.exp_sub, Real.exp_log ha, Real.exp_log hb]
    field_simp
  rw [hid, abs_mul, abs_of_pos hb]
  calc
    _ ≤ 1 * (2 * |Real.log a - Real.log b|) :=
      mul_le_mul hb1 he (abs_nonneg _) (by norm_num)
    _ ≤ 2 * L := by linarith only [hlog]

private theorem incoming_ray_density {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hp : (u, v) ∈ triangle 0 T) (huv : u < v) :
    ‖S.xi u v‖ ^ 2 / (S.nu u v * S.r u v) =
      -(-S.nu u v / S.r u v * ‖S.xi u v / S.nu u v‖ ^ 2) := by
  have hn := (hS.nu_neg (u, v) hp).ne
  have hr := (hS.r_pos (u, v) hp huv).ne'
  simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
  field_simp

private theorem outgoing_ray_density {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hp : (u, v) ∈ triangle 0 T) (huv : u < v) :
    ‖S.theta u v‖ ^ 2 / (S.lam u v * S.r u v) =
      S.lam u v / S.r u v * ‖S.theta u v / S.lam u v‖ ^ 2 := by
  have hl := (hS.lam_pos (u, v) hp).ne'
  have hr := (hS.r_pos (u, v) hp huv).ne'
  simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
  field_simp

/-- The incoming logarithmic expansion is its initial value minus the
incoming quadratic scalar budget. The identity includes the axis and
has exact coefficient one, with no smallness requirement. -/
theorem AprioriSetting.incoming_ray_integral {e T ε M : ℝ}
    {S : Fields} {h : ℝ → ℂ} (hset : AprioriSetting e T ε M S h)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    Real.log (S.lam u v / (1 - S.mu u v)) -
        Real.log (S.lam 0 v / (1 - S.mu 0 v)) =
      -(∫ x in 0..u, -S.nu x v / S.r x v * ‖S.xi x v / S.nu x v‖ ^ 2) := by
  have hv : 0 ≤ v := hu.trans huv
  have hs : MapsTo (fun x : ℝ => (x, v)) (Icc 0 u) (triangle 0 T) :=
    fun x hx => ⟨hx.1, hx.2.trans huv, hvT⟩
  have cH := (continuousOn_const (c := (1 : ℝ))).sub
    (continuousOn_mu_aux hset.pos hset.c1)
  have cF := (hset.c1.c1_lam.continuousOn.div cH
    (fun p hp => (hset.c1.one_sub_mu_pos p hp).ne')).log
      (fun p hp => (div_pos (hset.c1.lam_pos p hp)
        (hset.c1.one_sub_mu_pos p hp)).ne')
  have csec := cF.comp (continuous_id.prodMk continuous_const).continuousOn hs
  have iq : IntervalIntegrable (fun x =>
      -S.nu x v / S.r x v * ‖S.xi x v / S.nu x v‖ ^ 2) volume 0 u :=
    (hset.quadratic_scalar_integrable le_rfl hv hvT).2.mono_set
    (by simpa only [uIcc_of_le hu, uIcc_of_le hv] using Icc_subset_Icc le_rfl huv)
  have hd (x : ℝ) (hx : x ∈ Ioo 0 u) : HasDerivAt
      (fun x => Real.log (S.lam x v / (1 - S.mu x v)))
      (-(-S.nu x v / S.r x v * ‖S.xi x v / S.nu x v‖ ^ 2)) x := by
    have hxv : x < v := hx.2.trans_le huv
    have hi := (eq_ray_in hset.c1 hx.1.le hxv hvT).hasDerivAt
      (Icc_mem_nhds hx.1 hxv)
    rwa [incoming_ray_density hset.c1 (hs ⟨hx.1.le, hx.2.le⟩) hxv] at hi
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu csec hd iq.neg
  rw [intervalIntegral.integral_neg] at hi
  exact hi.symm

/-- The outgoing logarithmic expansion is its axis value plus the outgoing
quadratic scalar budget. The identity has exact coefficient one, including
both endpoints, and requires no smallness. -/
theorem AprioriSetting.outgoing_ray_integral {e T ε M : ℝ}
    {S : Fields} {h : ℝ → ℂ} (hset : AprioriSetting e T ε M S h)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    Real.log (-S.nu u v / (1 - S.mu u v)) -
        Real.log (-S.nu u u / (1 - S.mu u u)) =
      ∫ x in u..v, S.lam u x / S.r u x * ‖S.theta u x / S.lam u x‖ ^ 2 := by
  have hs : MapsTo (fun x : ℝ => (u, x)) (Icc u v) (triangle 0 T) :=
    fun x hx => ⟨hu, hx.1, hx.2.trans hvT⟩
  have cH := (continuousOn_const (c := (1 : ℝ))).sub
    (continuousOn_mu_aux hset.pos hset.c1)
  have cF := (hset.c1.c1_nu.continuousOn.neg.div cH
    (fun p hp => (hset.c1.one_sub_mu_pos p hp).ne')).log
      (fun p hp => (div_pos (neg_pos.mpr (hset.c1.nu_neg p hp))
        (hset.c1.one_sub_mu_pos p hp)).ne')
  have csec := cF.comp (continuous_const.prodMk continuous_id).continuousOn hs
  have iq := (hset.quadratic_scalar_integrable hu huv hvT).1
  have hd (x : ℝ) (hx : x ∈ Ioo u v) : HasDerivAt
      (fun x => Real.log (-S.nu u x / (1 - S.mu u x)))
      (S.lam u x / S.r u x * ‖S.theta u x / S.lam u x‖ ^ 2) x := by
    have hi := (eq_ray_out hset.c1 hu hx.1 (hx.2.le.trans hvT)).hasDerivAt
      (Icc_mem_nhds hx.1 (hx.2.trans_le hvT))
    rwa [outgoing_ray_density hset.c1 (hs ⟨hx.1.le, hx.2.le⟩) hx.1] at hi
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv csec hd iq).symm

end EmcsfAcExtension.Local
