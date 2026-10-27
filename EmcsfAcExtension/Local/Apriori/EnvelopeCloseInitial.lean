module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.Hardy
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity
import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # The initial outgoing renormalized derivative budget

The mass factor is at most one and the cubic correction is bounded by the
initial Hardy integral. This proves the budget of `charged_SF_new_version.tex:L4732–L4733`
with a universal constant and no smallness assumption on the variation.
-/

public section

open Set MeasureTheory Filter Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem mass_nonneg {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) : 0 ≤ S.m u v := by
  have hc : ContinuousOn (S.m u) (Icc u v) := hS.c1_m.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn
    (show MapsTo (fun x => (u, x)) (Icc u v) (triangle 0 T) from
      fun x hx => ⟨hu, hx.1, hx.2.trans hvT⟩)
  have hd (x : ℝ) (hx : x ∈ Ioo u v) : HasDerivAt (S.m u) (S.mV u x) x := by
    have hp : (u, x) ∈ triangle 0 T := ⟨hu, hx.1.le, hx.2.le.trans hvT⟩
    have hh := hasDerivWithinAt_pdV hS.c1_m hp
      (show MapsTo (fun x => (u, x)) (Icc u v) (triangle 0 T) from
        fun x hx => ⟨hu, hx.1, hx.2.trans hvT⟩)
    rw [(hS.eq_v (u, x) hp hx.1).2.2.1] at hh
    exact hh.hasDerivAt (Icc_mem_nhds hx.1 hx.2)
  have hm : MonotoneOn (S.m u) (Icc u v) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc u v) hc
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hd x hx).deriv]
      have hμ := hS.one_sub_mu_pos (u, x) ⟨hu, hx.1.le, hx.2.le.trans hvT⟩
      have hlam := hS.lam_pos (u, x) ⟨hu, hx.1.le, hx.2.le.trans hvT⟩
      unfold Fields.mV
      positivity
  have hh := hm ⟨le_rfl, huv⟩ ⟨huv, le_rfl⟩ huv
  rwa [(hS.axis u ⟨hu, le_rfl, huv.trans hvT⟩).2.1] at hh

private theorem norm_cubic (q : ℝ) (x : ℂ) :
    ‖(q : ℂ) * (‖x‖ : ℂ) ^ 2 * x‖ = |q| * ‖x‖ ^ 2 * ‖x‖ := by
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_norm]

private theorem initial_pointwise {e T ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) {v : ℝ} (hv : v ∈ Icc 0 T) :
    ‖jC1 (triangle 0 T) S 0 v‖ ≤ ‖pdV (triangle 0 T) S.a 0 v‖ +
      (16 * ε ^ 2) * (S.lam 0 v / S.r 0 v * ‖S.theta 0 v / S.lam 0 v‖) := by
  have hp : (0, v) ∈ triangle 0 T := ⟨le_rfl, hv.1, hv.2⟩
  have hμ : 0 ≤ S.mu 0 v := div_nonneg
    (mul_nonneg (by norm_num) (mass_nonneg hset.c1 le_rfl hv.1 hv.2))
    (hset.radius_nonneg hp)
  have hγ := hset.c1.one_sub_mu_pos (0, v) hp
  have hq : 0 ≤ S.lam 0 v / S.r 0 v :=
    div_nonneg (hset.c1.lam_pos (0, v) hp).le (hset.radius_nonneg hp)
  have hx := (hset.box (0, v) hp).2.2.2.2.2.2.1
  have hx2 : ‖S.theta 0 v / S.lam 0 v‖ ^ 2 ≤ 16 * ε ^ 2 := by
    convert pow_le_pow_left₀ (norm_nonneg _) hx 2 using 1; ring
  have hγnorm : ‖(1 : ℂ) - (S.mu 0 v : ℂ)‖ = 1 - S.mu 0 v := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hγ]
  rw [jC1, norm_mul, hγnorm]
  calc
    _ ≤ 1 * ‖pdV (triangle 0 T) S.a 0 v -
        S.lam 0 v / S.r 0 v * (‖S.theta 0 v / S.lam 0 v‖ : ℂ) ^ 2 *
          (S.theta 0 v / S.lam 0 v)‖ := by gcongr; linarith only [hμ]
    _ ≤ ‖pdV (triangle 0 T) S.a 0 v‖ +
        ‖S.lam 0 v / S.r 0 v * (‖S.theta 0 v / S.lam 0 v‖ : ℂ) ^ 2 *
          (S.theta 0 v / S.lam 0 v)‖ := by
      rw [one_mul]
      exact norm_sub_le _ _
    _ ≤ _ := by
      apply add_le_add le_rfl
      rw [← Complex.ofReal_div, norm_cubic, abs_of_nonneg hq]
      calc
        _ = ‖S.theta 0 v / S.lam 0 v‖ ^ 2 *
            (S.lam 0 v / S.r 0 v * ‖S.theta 0 v / S.lam 0 v‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hx2
          (mul_nonneg hq (norm_nonneg _))

/-- [node restart-sec-independent-area#initial-j-budget]
The initial outgoing renormalized derivative has mass at most `ε + C ε³`.
The constant is universal within the fixed bootstrap box, independently of
the coupling, interval, background size, and all smooth derivative norms.
-/
theorem initial_j_budget : ∃ C : ℝ, 0 < C ∧
    ∀ (e s ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e s ε M S h →
      (∫⁻ v in Icc 0 s, ‖jC1 (triangle 0 s) S 0 v‖ₑ) ≤
        ENNReal.ofReal (ε + C * ε ^ 3) := by
  refine ⟨16, by norm_num, ?_⟩
  intro e s ε M S h hset
  have cj : ContinuousOn (jC1 (triangle 0 s) S 0) (Icc 0 s) :=
    (continuousOn_jC1_aux hset.pos hset.c1).comp (f := fun v : ℝ => (0, v))
    (continuous_const.prodMk continuous_id).continuousOn
    (show MapsTo (fun v => (0, v)) (Icc 0 s) (triangle 0 s) from
      fun v hv => ⟨le_rfl, hv.1, hv.2⟩)
  have cd : ContinuousOn (pdV (triangle 0 s) S.a 0) (Icc 0 s) :=
    (continuousOn_pdV hset.c1.c1_a (uniqueDiffOn_triangle hset.pos)).comp
    (continuous_const.prodMk continuous_id).continuousOn
    (show MapsTo (fun v => (0, v)) (Icc 0 s) (triangle 0 s) from
      fun v hv => ⟨le_rfl, hv.1, hv.2⟩)
  have hj := cj.intervalIntegrable_of_Icc (μ := volume) hset.pos.le
  have hd := cd.intervalIntegrable_of_Icc (μ := volume) hset.pos.le
  have hh := bv_hardy_out_integrated hset.c1 le_rfl hset.pos.le le_rfl
  have hv : (eVariationOn (S.a 0) (Icc 0 s)).toReal ≤ ε := by
    have he : eVariationOn (S.a 0) (Icc 0 s) = eVariationOn h (Icc 0 s) :=
      eVariationOn.congr (fun v hv => (hset.data.1 v hv).2)
    rw [he]
    exact hset.eps
  rw [← ofReal_integral_norm_eq_lintegral_enorm
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hset.pos.le).mp hj),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hset.pos.le]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∫ v in 0..s, ‖pdV (triangle 0 s) S.a 0 v‖ +
        (16 * ε ^ 2) * (S.lam 0 v / S.r 0 v * ‖S.theta 0 v / S.lam 0 v‖) :=
      intervalIntegral.integral_mono_on hset.pos.le hj.norm
        (hd.norm.add (hh.1.const_mul _)) (fun v hv => initial_pointwise hset hv)
    _ = (∫ v in 0..s, ‖pdV (triangle 0 s) S.a 0 v‖) +
        (16 * ε ^ 2) * ∫ v in 0..s,
          S.lam 0 v / S.r 0 v * ‖S.theta 0 v / S.lam 0 v‖ := by
      rw [intervalIntegral.integral_add hd.norm (hh.1.const_mul _),
        intervalIntegral.integral_const_mul]
    _ ≤ ε + (16 * ε ^ 2) * ε := by
      apply add_le_add
      · rw [← bv_variation_out hset.c1 le_rfl hset.pos.le le_rfl]
        exact hv
      · exact mul_le_mul_of_nonneg_left (hh.2.trans hv) (by positivity)
    _ = _ := by ring

end EmcsfAcExtension.Local
