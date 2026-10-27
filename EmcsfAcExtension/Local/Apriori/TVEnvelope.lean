module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Frozen.CovVarIn
import EmcsfAcExtension.Local.Apriori.Hardy
import EmcsfAcExtension.Local.Apriori.TVEnvelopeAux
import EmcsfAcExtension.Infra.Calculus.PartialsC1
import EmcsfAcExtension.Infra.HardyQuadratic

/-! # Exact variation bounds from the classical envelopes

Absolute integration and radial Hardy absorb the cubic corrections with the
literal coefficient `16 * ε²`, as in `charged_SF_new_version.tex:L4620–L4631` and the approved
incoming repair. No constant depends on the coupling or on smooth data norms.
-/

public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem c1_a_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) :
    ContDiffOn ℝ 1 (Function.uncurry S.a) (triangle 0 T) := by
  have hi := (hS.c1_lam.inv (fun p hp => (hS.lam_pos p hp).ne')).smul hS.c1_theta
  change ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.phi p.1 p.2 + S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ)) _
  convert hS.c1_phi.add hi using 1
  funext p
  change S.phi p.1 p.2 + S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ) =
    S.phi p.1 p.2 + (S.lam p.1 p.2)⁻¹ • S.theta p.1 p.2
  simp only [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm]

private theorem section_v_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T u v : ℝ} {f : ℝ → ℝ → E}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle 0 T))
    (hu : 0 ≤ u) (_huv : u ≤ v) (hvT : v ≤ T) :
    ContDiffOn ℝ 1 (f u) (Icc u v) :=
  hf.comp ((contDiffOn_const (c := u)).prodMk contDiffOn_id)
    (fun _ hx => ⟨hu, hx.1, hx.2.trans hvT⟩)

private theorem partial_v_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T u v : ℝ} {f : ℝ → ℝ → E}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle 0 T))
    (hT : 0 < T) (hu : 0 ≤ u) (hvT : v ≤ T) :
    ContinuousOn (pdV (triangle 0 T) f u) (Icc u v) :=
  (continuousOn_partial_v hf (uniqueDiffOn_triangle hT)).comp
    (continuous_const.prodMk continuous_id).continuousOn
    (fun _ hx => ⟨hu, hx.1, hx.2.trans hvT⟩)

private theorem c1_b_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) :
    ContDiffOn ℝ 1 (Function.uncurry S.b) (triangle 0 T) := by
  have hi := (hS.c1_nu.inv (fun p hp => (hS.nu_neg p hp).ne)).smul hS.c1_xi
  change ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.phi p.1 p.2 + S.xi p.1 p.2 / (S.nu p.1 p.2 : ℂ)) _
  convert hS.c1_phi.add hi using 1
  funext p
  change S.phi p.1 p.2 + S.xi p.1 p.2 / (S.nu p.1 p.2 : ℂ) =
    S.phi p.1 p.2 + (S.nu p.1 p.2)⁻¹ • S.xi p.1 p.2
  simp only [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm]

private theorem section_u_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T u v : ℝ} {f : ℝ → ℝ → E}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle 0 T))
    (hu : 0 ≤ u) (_huv : u ≤ v) (hvT : v ≤ T) :
    ContDiffOn ℝ 1 (fun x => f x v) (Icc u v) :=
  hf.comp (contDiffOn_id.prodMk (contDiffOn_const (c := v)))
    (fun _ hx => ⟨hu.trans hx.1, hx.2, hvT⟩)

private theorem partial_u_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T u v : ℝ} {f : ℝ → ℝ → E}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle 0 T))
    (hT : 0 < T) (hu : 0 ≤ u) (hvT : v ≤ T) :
    ContinuousOn (fun x => pdU (triangle 0 T) f x v) (Icc u v) :=
  (continuousOn_partial_u hf (uniqueDiffOn_triangle hT)).comp
    (continuous_id.prodMk continuous_const).continuousOn
    (fun _ hx => ⟨hu.trans hx.1, hx.2, hvT⟩)

private theorem norm_deriv_aux {h q B : ℝ} {d x : ℂ}
    (hh : 0 < h) (hx : ‖x‖ ^ 2 ≤ B) :
    ‖d‖ ≤ h⁻¹ * ‖(h : ℂ) * (d - (q : ℂ) * (‖x‖ : ℂ) ^ 2 * x)‖ +
      B * (|q| * ‖x‖) := by
  have heq : d = (h⁻¹ : ℝ) • ((h : ℂ) * (d - (q : ℂ) * (‖x‖ : ℂ) ^ 2 * x)) +
      (q : ℂ) * (‖x‖ : ℂ) ^ 2 * x := by
    rw [Complex.real_smul, Complex.ofReal_inv]
    field_simp [Complex.ofReal_ne_zero.mpr hh.ne']
    ring
  calc
    ‖d‖ = ‖(h⁻¹ : ℝ) • ((h : ℂ) * (d - (q : ℂ) * (‖x‖ : ℂ) ^ 2 * x)) +
        (q : ℂ) * (‖x‖ : ℂ) ^ 2 * x‖ := congrArg norm heq
    _ ≤ ‖(h⁻¹ : ℝ) • ((h : ℂ) * (d - (q : ℂ) * (‖x‖ : ℂ) ^ 2 * x))‖ +
        ‖(q : ℂ) * (‖x‖ : ℂ) ^ 2 * x‖ := by
      exact norm_add_le _ _
    _ = h⁻¹ * ‖(h : ℂ) * (d - (q : ℂ) * (‖x‖ : ℂ) ^ 2 * x)‖ +
        ‖x‖ ^ 2 * (|q| * ‖x‖) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh)]
      simp only [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_norm]
      ring
    _ ≤ _ := add_le_add le_rfl
      (mul_le_mul_of_nonneg_right hx (mul_nonneg (abs_nonneg _) (norm_nonneg _)))

private theorem inv_mass_bound_aux {e T ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) {p : ℝ × ℝ} (hp : p ∈ triangle 0 T) :
    (1 - S.mu p.1 p.2)⁻¹ ≤ 2 := by
  have hb := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) (hset.box p hp).2.2.2.2.1
  norm_num at hb
  exact hb

private theorem radius_nonneg_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {p : ℝ × ℝ} (hp : p ∈ triangle 0 T) :
    0 ≤ S.r p.1 p.2 := by
  rcases eq_or_lt_of_le hp.2.1 with heq | hlt
  · rw [← heq, (hS.axis p.1 ⟨hp.1, le_rfl, heq.trans_le hp.2.2⟩).1]
  · exact (hS.r_pos p hp hlt).le

/-- [node restart-bv-TVJ]
The exact outgoing absorption estimate (`charged_SF_new_version.tex:L4620–L4625`).
The displayed coefficients are universal, independent of `e`, `s`, `M`, and
all higher data norms. This undivided inequality requires no smallness
assumption and no division by `1 - 16 * ε²`. -/
theorem bv_tvj {e s ε M : ℝ} {S : Fields} {h : ℝ → ℂ} (hset : AprioriSetting e s ε M S h)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvs : v ≤ s) :
    (1 - 16 * ε ^ 2) * (eVariationOn (S.a u) (Icc u v)).toReal ≤
      (⨆ w ∈ Icc u v, (1 - S.mu u w)⁻¹) *
        ∫ x in u..v, (outEnv 0 (jC1 (triangle 0 s) S) x).toReal := by
  let H : ℝ := ⨆ w ∈ Icc u v, (1 - S.mu u w)⁻¹
  have hbound : BddAbove (⋃ w : ℝ, Set.range (fun _ : w ∈ Icc u v => (1 - S.mu u w)⁻¹)) := by
    refine ⟨2, ?_⟩
    intro y hy
    rcases Set.mem_iUnion.mp hy with ⟨w, hw⟩
    rcases hw with ⟨hw, rfl⟩
    exact inv_mass_bound_aux hset (p := (u, w)) ⟨hu, hw.1, hw.2.trans hvs⟩
  have hH : ∀ w ∈ Icc u v, (1 - S.mu u w)⁻¹ ≤ H :=
    fun w hw => le_ciSup₂ hbound w hw
  have hH0 : 0 ≤ H := (inv_nonneg.mpr
    (hset.c1.one_sub_mu_pos (u, u) ⟨hu, le_rfl, huv.trans hvs⟩).le).trans (hH u ⟨le_rfl, huv⟩)
  have hHardy := bv_hardy_out_integrated hset.c1 hu huv hvs
  have hJ := (apriori_envelopes_integrable hset).1.mono_set
    (show uIcc u v ⊆ uIcc 0 s by
      rw [uIcc_of_le huv, uIcc_of_le hset.pos.le]
      exact Icc_subset_Icc hu hvs)
  have hD : IntervalIntegrable (pdV (triangle 0 s) S.a u) volume u v :=
    ContinuousOn.intervalIntegrable_of_Icc huv
      (partial_v_aux (c1_a_aux hset.c1) hset.pos hu hvs)
  have hi := intervalIntegral.integral_mono_on huv hD.norm
    ((hJ.const_mul H).add (hHardy.1.const_mul (16 * ε ^ 2))) (fun x hx => by
      have hp : (u, x) ∈ triangle 0 s := ⟨hu, hx.1, hx.2.trans hvs⟩
      have hx2 : ‖S.theta u x / S.lam u x‖ ^ 2 ≤ 16 * ε ^ 2 := by
        calc
          _ ≤ (4 * ε) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hset.box (u, x) hp).2.2.2.2.2.2.1 2
          _ = _ := by ring
      have hn := norm_deriv_aux (hset.c1.one_sub_mu_pos (u, x) hp) hx2
        (q := S.lam u x / S.r u x) (d := pdV (triangle 0 s) S.a u x)
      have hq : 0 ≤ S.lam u x / S.r u x :=
        div_nonneg (hset.c1.lam_pos (u, x) hp).le (radius_nonneg_aux hset.c1 hp)
      rw [abs_of_nonneg hq] at hn
      have hj : ‖jC1 (triangle 0 s) S u x‖ ≤ (outEnv 0 (jC1 (triangle 0 s) S) x).toReal := by
        simpa only [toReal_enorm] using ENNReal.toReal_mono
          (apriori_envelopes_finite hset ⟨hu.trans hx.1, hx.2.trans hvs⟩).1
          (enorm_le_normEnvelope (jC1 (triangle 0 s) S) ⟨hu, hx.1⟩)
      have hn' : ‖pdV (triangle 0 s) S.a u x‖ ≤
          (1 - S.mu u x)⁻¹ * ‖jC1 (triangle 0 s) S u x‖ +
            16 * ε ^ 2 * (S.lam u x / S.r u x * ‖S.theta u x / S.lam u x‖) := by
        simpa only [jC1, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div,
          Complex.ofReal_pow] using hn
      exact hn'.trans (add_le_add
        (mul_le_mul (hH x hx) hj (norm_nonneg _) hH0) le_rfl))
  rw [intervalIntegral.integral_add (hJ.const_mul H) (hHardy.1.const_mul (16 * ε ^ 2)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    ← bv_variation_out hset.c1 hu huv hvs] at hi
  have hb := hi.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hHardy.2 (mul_nonneg (by norm_num) (sq_nonneg ε))))
  dsimp only [H] at hb
  linarith only [hb]

/-- [node restart-bv-TVK]
The exact incoming covariant absorption estimate (`charged_SF_new_version.tex:L4626–L4629`),
using the approved internal project record repair. All displayed coefficients are
universal and independent of `e`, `s`, `M`, and higher data norms. -/
theorem bv_tvk {e s ε M : ℝ} {S : Fields} {h : ℝ → ℂ} (hset : AprioriSetting e s ε M S h)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvs : v ≤ s) :
    (1 - 16 * ε ^ 2) *
        (∫ x in u..v, ‖pdU (triangle 0 s) S.b x v + I * e * S.A x v * S.b x v‖) ≤
      (⨆ w ∈ Icc u v, (1 - S.mu w v)⁻¹) *
        ∫ x in u..v, (inEnv s (kC1 e (triangle 0 s) S) x).toReal := by
  let H : ℝ := ⨆ w ∈ Icc u v, (1 - S.mu w v)⁻¹
  have hbound : BddAbove (⋃ w : ℝ, Set.range (fun _ : w ∈ Icc u v => (1 - S.mu w v)⁻¹)) := by
    refine ⟨2, ?_⟩
    intro y hy
    rcases Set.mem_iUnion.mp hy with ⟨w, hw⟩
    rcases hw with ⟨hw, rfl⟩
    exact inv_mass_bound_aux hset (p := (w, v)) ⟨hu.trans hw.1, hw.2, hvs⟩
  have hH : ∀ w ∈ Icc u v, (1 - S.mu w v)⁻¹ ≤ H :=
    fun w hw => le_ciSup₂ hbound w hw
  have hH0 : 0 ≤ H := (inv_nonneg.mpr
    (hset.c1.one_sub_mu_pos (v, v) ⟨hu.trans huv, le_rfl, hvs⟩).le).trans (hH v ⟨huv, le_rfl⟩)
  have hHardy := bv_hardy_in_integrated hset.c1 hu huv hvs
  have hK := (apriori_envelopes_integrable hset).2.mono_set
    (show uIcc u v ⊆ uIcc 0 s by
      rw [uIcc_of_le huv, uIcc_of_le hset.pos.le]
      exact Icc_subset_Icc hu hvs)
  have hD : IntervalIntegrable
      (fun x => pdU (triangle 0 s) S.b x v + I * e * S.A x v * S.b x v) volume u v :=
    ContinuousOn.intervalIntegrable_of_Icc huv
      ((partial_u_aux (c1_b_aux hset.c1) hset.pos hu hvs).add
        (((continuousOn_const (c := (I * e : ℂ))).mul
          (Complex.continuous_ofReal.comp_continuousOn
            (section_u_aux hset.c1.c1_A hu huv hvs).continuousOn)).mul
              (section_u_aux (c1_b_aux hset.c1) hu huv hvs).continuousOn))
  have hi := intervalIntegral.integral_mono_on huv hD.norm
    ((hK.const_mul H).add (hHardy.1.const_mul (16 * ε ^ 2))) (fun x hx => by
      have hp : (x, v) ∈ triangle 0 s := ⟨hu.trans hx.1, hx.2, hvs⟩
      have hx2 : ‖S.xi x v / S.nu x v‖ ^ 2 ≤ 16 * ε ^ 2 := by
        calc
          _ ≤ (4 * ε) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hset.box (x, v) hp).2.2.2.2.2.2.2 2
          _ = _ := by ring
      have hn := norm_deriv_aux (hset.c1.one_sub_mu_pos (x, v) hp) hx2
        (q := S.nu x v / S.r x v)
        (d := pdU (triangle 0 s) S.b x v + I * e * S.A x v * S.b x v)
      have hq : S.nu x v / S.r x v ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (hset.c1.nu_neg (x, v) hp).le
          (radius_nonneg_aux hset.c1 hp)
      rw [abs_of_nonpos hq, ← neg_div] at hn
      have hk : ‖kC1 e (triangle 0 s) S x v‖ ≤ (inEnv s (kC1 e (triangle 0 s) S) x).toReal := by
        simpa only [toReal_enorm] using ENNReal.toReal_mono
          (apriori_envelopes_finite hset ⟨hu.trans hx.1, hx.2.trans hvs⟩).2
          (le_iSup₂_of_le v ⟨hx.2, hvs⟩
            (le_rfl : ‖kC1 e (triangle 0 s) S x v‖ₑ ≤ ‖kC1 e (triangle 0 s) S x v‖ₑ))
      have hn' : ‖pdU (triangle 0 s) S.b x v + I * e * S.A x v * S.b x v‖ ≤
          (1 - S.mu x v)⁻¹ * ‖kC1 e (triangle 0 s) S x v‖ +
            16 * ε ^ 2 * (-S.nu x v / S.r x v * ‖S.xi x v / S.nu x v‖) := by
        simpa only [kC1, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div,
          Complex.ofReal_pow] using hn
      exact hn'.trans (add_le_add
        (mul_le_mul (hH x hx) hk (norm_nonneg _) hH0) le_rfl))
  rw [intervalIntegral.integral_add (hK.const_mul H) (hHardy.1.const_mul (16 * ε ^ 2)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
  have hb := hi.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hHardy.2 (mul_nonneg (by norm_num) (sq_nonneg ε))))
  dsimp only [H] at hb
  linarith only [hb]

/-- [node restart-bv-TVK]
The incoming TV bound with precisely the frozen `covVarIn` representative.
The coefficient `16` and the reciprocal mass supremum have the same universal
scope as in `bv_tvk`. -/
theorem bv_tvk_cov {e s ε M : ℝ} {S : Fields} {h : ℝ → ℂ} (hset : AprioriSetting e s ε M S h)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvs : v ≤ s) :
    (1 - 16 * ε ^ 2) * (covVarIn e S.A S.b u v v).toReal ≤
      (⨆ w ∈ Icc u v, (1 - S.mu w v)⁻¹) *
        ∫ x in u..v, (inEnv s (kC1 e (triangle 0 s) S) x).toReal := by
  rw [bv_variation_in hset.c1 hu huv hvs]
  exact bv_tvk hset hu huv hvs

private theorem real_biSup_le_aux {a b C : ℝ} {f : ℝ → ℝ}
    (hC : 0 ≤ C) (hf : ∀ x ∈ Icc a b, f x ≤ C) : (⨆ x ∈ Icc a b, f x) ≤ C := by
  apply ciSup_le
  intro x
  rw [ciSup_eq_ite]
  split_ifs with hx
  · exact hf x hx
  · simpa only [Real.sSup_empty] using hC

private theorem quadratic_out_aux {e s ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e s ε M S h) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvs : v ≤ s) :
    (∫ x in u..v, S.lam u x / S.r u x * ‖S.theta u x / S.lam u x‖ ^ 2) ≤
      4 * ε * (eVariationOn (S.a u) (Icc u v)).toReal := by
  have hH := bv_hardy_out_integrated hset.c1 hu huv hvs
  have hfun : ContinuousOn (fun x => S.theta u x / (S.lam u x : ℂ)) (Icc u v) :=
    (section_v_aux hset.c1.c1_theta hu huv hvs).continuousOn.div
      (Complex.continuous_ofReal.comp_continuousOn
        (section_v_aux hset.c1.c1_lam hu huv hvs).continuousOn)
      (fun x hx => Complex.ofReal_ne_zero.mpr
        (hset.c1.lam_pos (u, x) ⟨hu, hx.1, hx.2.trans hvs⟩).ne')
  have h4 : 0 ≤ 4 * ε := (norm_nonneg (S.theta u u / S.lam u u)).trans
    (hset.box (u, u) ⟨hu, le_rfl, huv.trans hvs⟩).2.2.2.2.2.2.1
  have hi := integrable_and_integral_weight_mul_norm_sq_le
    (hfun.aestronglyMeasurable measurableSet_Icc)
    (show ∀ᵐ x ∂volume.restrict (Icc u v), 0 ≤ S.lam u x / S.r u x from by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact div_nonneg (hset.c1.lam_pos (u, x) ⟨hu, hx.1, hx.2.trans hvs⟩).le
        (radius_nonneg_aux hset.c1 (p := (u, x)) ⟨hu, hx.1, hx.2.trans hvs⟩))
    (show ∀ᵐ x ∂volume.restrict (Icc u v), S.lam u x / S.r u x ≠ 0 →
      ‖S.theta u x / S.lam u x‖ ≤ 4 * ε from by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact fun _ => (hset.box (u, x) ⟨hu, hx.1, hx.2.trans hvs⟩).2.2.2.2.2.2.1)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le huv).mp hH.1)
  have hb := hi.2
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le huv, ← intervalIntegral.integral_of_le huv] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left hH.2 h4)

private theorem quadratic_in_aux {e s ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e s ε M S h) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvs : v ≤ s) :
    (∫ x in u..v, -S.nu x v / S.r x v * ‖S.xi x v / S.nu x v‖ ^ 2) ≤
      4 * ε * ∫ x in u..v, ‖pdU (triangle 0 s) S.b x v + I * e * S.A x v * S.b x v‖ := by
  have hH := bv_hardy_in_integrated hset.c1 hu huv hvs
  have hfun : ContinuousOn (fun x => S.xi x v / (S.nu x v : ℂ)) (Icc u v) :=
    (section_u_aux hset.c1.c1_xi hu huv hvs).continuousOn.div
      (Complex.continuous_ofReal.comp_continuousOn
        (section_u_aux hset.c1.c1_nu hu huv hvs).continuousOn)
      (fun x hx => Complex.ofReal_ne_zero.mpr
        (hset.c1.nu_neg (x, v) ⟨hu.trans hx.1, hx.2, hvs⟩).ne)
  have h4 : 0 ≤ 4 * ε := (norm_nonneg (S.xi v v / S.nu v v)).trans
    (hset.box (v, v) ⟨hu.trans huv, le_rfl, hvs⟩).2.2.2.2.2.2.2
  have hi := integrable_and_integral_weight_mul_norm_sq_le
    (hfun.aestronglyMeasurable measurableSet_Icc)
    (show ∀ᵐ x ∂volume.restrict (Icc u v), 0 ≤ -S.nu x v / S.r x v from by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact div_nonneg (neg_pos.mpr (hset.c1.nu_neg (x, v) ⟨hu.trans hx.1, hx.2, hvs⟩)).le
        (radius_nonneg_aux hset.c1 (p := (x, v)) ⟨hu.trans hx.1, hx.2, hvs⟩))
    (show ∀ᵐ x ∂volume.restrict (Icc u v), -S.nu x v / S.r x v ≠ 0 →
      ‖S.xi x v / S.nu x v‖ ≤ 4 * ε from by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact fun _ => (hset.box (x, v) ⟨hu.trans hx.1, hx.2, hvs⟩).2.2.2.2.2.2.2)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le huv).mp hH.1)
  have hb := hi.2
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le huv, ← intervalIntegral.integral_of_le huv] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left hH.2 h4)

private theorem flux_absorb_aux {ε V X F : ℝ} (hε0 : 0 ≤ ε)
    (hε : 16 * ε ^ 2 < 1) (htv : (1 - 16 * ε ^ 2) * V ≤ 2 * X)
    (hF : F ≤ 4 * ε * V) : F ≤ (8 * ε / (1 - 16 * ε ^ 2)) * X := by
  have hv : V ≤ 2 * X / (1 - 16 * ε ^ 2) :=
    (le_div_iff₀ (sub_pos.mpr hε)).mpr (by simpa only [mul_comm] using htv)
  calc
    F ≤ 4 * ε * V := hF
    _ ≤ 4 * ε * (2 * X / (1 - 16 * ε ^ 2)) :=
      mul_le_mul_of_nonneg_left hv (mul_nonneg (by norm_num) hε0)
    _ = _ := by ring

/-- [node restart-bv-fluxes]
Outgoing quadratic budget on every shortened axis-to-point section
(`charged_SF_new_version.tex:L4632–L4640`). The explicit coefficient is
`8 * ε / (1 - 16 * ε²)`, uniform in `e`, `s`, `M`, and all higher data norms.
For any fixed numerical margin `η > 0` with `η ≤ 1 - 16 * ε²`, it is at most
`8 * ε / η`; no uniformity as `16 * ε²` tends to `1` is claimed. -/
theorem bv_fluxes_out_margin {e s ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e s ε M S h) (hε : 16 * ε ^ 2 < 1) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvs : v ≤ s) :
    (∫ x in u..v, S.lam u x / S.r u x * ‖S.theta u x / S.lam u x‖ ^ 2) ≤
      (8 * ε / (1 - 16 * ε ^ 2)) *
        ∫ x in u..v, (outEnv 0 (jC1 (triangle 0 s) S) x).toReal := by
  have hsup : (⨆ w ∈ Icc u v, (1 - S.mu u w)⁻¹) ≤ 2 :=
    real_biSup_le_aux (by norm_num) (fun w hw => inv_mass_bound_aux hset (p := (u, w))
      ⟨hu, hw.1, hw.2.trans hvs⟩)
  have hJ0 : 0 ≤ ∫ x in u..v, (outEnv 0 (jC1 (triangle 0 s) S) x).toReal :=
    intervalIntegral.integral_nonneg huv (fun _ _ => ENNReal.toReal_nonneg)
  exact flux_absorb_aux (ENNReal.toReal_nonneg.trans hset.eps) hε
    ((bv_tvj hset hu huv hvs).trans (mul_le_mul_of_nonneg_right hsup hJ0))
    (quadratic_out_aux hset hu huv hvs)

/-- [node restart-bv-fluxes]
Incoming quadratic budget on every shortened axis-to-point section, using the
approved covariant Hardy repair (`charged_SF_new_version.tex:L4632–L4640`). The explicit
coefficient `8 * ε / (1 - 16 * ε²)` depends only on `ε`, uniformly in `e`, `s`,
`M`, and all higher data norms. A fixed numerical margin `η > 0` with
`η ≤ 1 - 16 * ε²` bounds it by `8 * ε / η`; no uniformity at the absorption
threshold is claimed. -/
theorem bv_fluxes_in_margin {e s ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e s ε M S h) (hε : 16 * ε ^ 2 < 1) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvs : v ≤ s) :
    (∫ x in u..v, -S.nu x v / S.r x v * ‖S.xi x v / S.nu x v‖ ^ 2) ≤
      (8 * ε / (1 - 16 * ε ^ 2)) *
        ∫ x in u..v, (inEnv s (kC1 e (triangle 0 s) S) x).toReal := by
  have hsup : (⨆ w ∈ Icc u v, (1 - S.mu w v)⁻¹) ≤ 2 :=
    real_biSup_le_aux (by norm_num) (fun w hw => inv_mass_bound_aux hset (p := (w, v))
      ⟨hu.trans hw.1, hw.2, hvs⟩)
  have hK0 : 0 ≤ ∫ x in u..v, (inEnv s (kC1 e (triangle 0 s) S) x).toReal :=
    intervalIntegral.integral_nonneg huv (fun _ _ => ENNReal.toReal_nonneg)
  exact flux_absorb_aux (ENNReal.toReal_nonneg.trans hset.eps) hε
    ((bv_tvk hset hu huv hvs).trans (mul_le_mul_of_nonneg_right hsup hK0))
    (quadratic_in_aux hset hu huv hvs)

/-- [node restart-bv-fluxes]
Both full-triangle quadratic scalar budgets (`charged_SF_new_version.tex:L4632–L4640`).
The explicit coefficient `8 * ε / (1 - 16 * ε²)` is uniform in `e`, `s`, `M`,
and all higher data norms. For a fixed numerical margin `η > 0` with
`η ≤ 1 - 16 * ε²`, it is at most `8 * ε / η`. -/
theorem bv_fluxes_margin {e s ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e s ε M S h) (hε : 16 * ε ^ 2 < 1) :
    (⨆ u ∈ Icc 0 s, ∫ v in u..s,
      S.lam u v / S.r u v * ‖S.theta u v / S.lam u v‖ ^ 2) ≤
        (8 * ε / (1 - 16 * ε ^ 2)) *
          ∫ x in 0..s, (outEnv 0 (jC1 (triangle 0 s) S) x).toReal ∧
    (⨆ v ∈ Icc 0 s, ∫ u in 0..v,
      -S.nu u v / S.r u v * ‖S.xi u v / S.nu u v‖ ^ 2) ≤
        (8 * ε / (1 - 16 * ε ^ 2)) *
          ∫ x in 0..s, (inEnv s (kC1 e (triangle 0 s) S) x).toReal := by
  have heps : 0 ≤ 8 * ε / (1 - 16 * ε ^ 2) :=
    div_nonneg (mul_nonneg (by norm_num) (ENNReal.toReal_nonneg.trans hset.eps))
      (sub_pos.mpr hε).le
  have henv := apriori_envelopes_integrable hset
  constructor
  · apply real_biSup_le_aux (mul_nonneg heps
      (intervalIntegral.integral_nonneg hset.pos.le (fun _ _ => ENNReal.toReal_nonneg)))
    intro u hu
    exact (bv_fluxes_out_margin hset hε hu.1 hu.2 le_rfl).trans
      (mul_le_mul_of_nonneg_left
        (intervalIntegral.integral_mono_interval hu.1 hu.2 le_rfl
          (ae_of_all _ (fun _ => ENNReal.toReal_nonneg)) henv.1) heps)
  · apply real_biSup_le_aux (mul_nonneg heps
      (intervalIntegral.integral_nonneg hset.pos.le (fun _ _ => ENNReal.toReal_nonneg)))
    intro v hv
    exact (bv_fluxes_in_margin hset hε le_rfl hv.1 hv.2).trans
      (mul_le_mul_of_nonneg_left
        (intervalIntegral.integral_mono_interval le_rfl hv.1 hv.2
          (ae_of_all _ (fun _ => ENNReal.toReal_nonneg)) henv.2) heps)

private theorem small_eps_aux {e s ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e s ε M S h) (hε : ε ≤ 1 / 8) :
    0 ≤ ε ∧ 16 * ε ^ 2 ≤ 1 / 4 := by
  have h0 : 0 ≤ ε := (show 0 ≤ datumVar h s from ENNReal.toReal_nonneg).trans hset.eps
  have hb := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hε 2) (by norm_num : (0 : ℝ) ≤ 16)
  norm_num at hb
  exact ⟨h0, hb⟩

private theorem small_flux_coeff_aux {ε : ℝ} (h0 : 0 ≤ ε)
    (hε : 16 * ε ^ 2 ≤ 1 / 4) : 8 * ε / (1 - 16 * ε ^ 2) ≤ 12 * ε := by
  apply (div_le_iff₀ (by linarith only [hε] : 0 < 1 - 16 * ε ^ 2)).mpr
  calc
    8 * ε ≤ 12 * ε * (3 / 4) := by linarith only [h0]
    _ ≤ 12 * ε * (1 - 16 * ε ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith only [hε]) (mul_nonneg (by norm_num) h0)

/-- Outgoing quadratic budget at the fixed margin `ε ≤ 1/8`, as a corollary of
`bv_fluxes_out_margin`. The coefficient `12` is universal, independent of `e`,
`s`, `M`, and all higher data norms. -/
theorem bv_fluxes_out {e s ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e s ε M S h) (hε : ε ≤ 1 / 8) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvs : v ≤ s) :
    (∫ x in u..v, S.lam u x / S.r u x * ‖S.theta u x / S.lam u x‖ ^ 2) ≤
      12 * ε * ∫ x in u..v, (outEnv 0 (jC1 (triangle 0 s) S) x).toReal := by
  have heps := small_eps_aux hset hε
  exact (bv_fluxes_out_margin hset (heps.2.trans_lt (by norm_num)) hu huv hvs).trans
    (mul_le_mul_of_nonneg_right (small_flux_coeff_aux heps.1 heps.2)
      (intervalIntegral.integral_nonneg huv (fun _ _ => ENNReal.toReal_nonneg)))

/-- Incoming quadratic budget at the fixed margin `ε ≤ 1/8`, as a corollary of
`bv_fluxes_in_margin`. The universal coefficient `12` is independent of `e`,
`s`, `M`, and all higher data norms. -/
theorem bv_fluxes_in {e s ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e s ε M S h) (hε : ε ≤ 1 / 8) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvs : v ≤ s) :
    (∫ x in u..v, -S.nu x v / S.r x v * ‖S.xi x v / S.nu x v‖ ^ 2) ≤
      12 * ε * ∫ x in u..v, (inEnv s (kC1 e (triangle 0 s) S) x).toReal := by
  have heps := small_eps_aux hset hε
  exact (bv_fluxes_in_margin hset (heps.2.trans_lt (by norm_num)) hu huv hvs).trans
    (mul_le_mul_of_nonneg_right (small_flux_coeff_aux heps.1 heps.2)
      (intervalIntegral.integral_nonneg huv (fun _ _ => ENNReal.toReal_nonneg)))

end EmcsfAcExtension.Local
