module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Infra.Calculus.PartialsC1

/-! # Regularity of the classical characteristic envelopes

Auxiliary analytic facts for the exact TV inequalities at
`charged_SF_new_version.tex:L4620–L4631`. Suprema are taken over the closed fibers in the
frozen architecture. Their measurability follows from continuous off-axis
sections and the separate continuous diagonal values.
-/

public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem aemeasurable_out_aux {E : Type*} [NormedAddCommGroup E]
    {a b : ℝ} {f : ℝ → ℝ → E}
    (hf : ContinuousOn (Function.uncurry f) (triangle a b ∩ {p | p.1 < p.2}))
    (hd : ContinuousOn (fun x => f x x) (Icc a b)) :
    AEMeasurable (outEnv a f) (volume.restrict (Icc a b)) := by
  have hc : ∀ t ∈ Icc (0 : ℝ) 1,
      ContinuousOn (fun v => f (a + t * (v - a)) v) (Ioc a b) := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with rfl | ht1
    · simpa only [one_mul, add_sub_cancel] using hd.mono Ioc_subset_Icc_self
    · apply hf.comp (show Continuous (fun v : ℝ => (a + t * (v - a), v)) by fun_prop).continuousOn
      intro v hv
      have hlo := mul_nonneg ht.1 (sub_nonneg.mpr hv.1.le)
      have hhi := mul_lt_mul_of_pos_right ht1 (sub_pos.mpr hv.1)
      have hleft : a ≤ a + t * (v - a) := by linarith only [hlo]
      have hstrict : a + t * (v - a) < v := by linarith only [hhi]
      exact ⟨⟨hleft, hstrict.le, hv.2⟩, hstrict⟩
  have hl : LowerSemicontinuousOn
      (fun v => ⨆ t ∈ Icc (0 : ℝ) 1, ‖f (a + t * (v - a)) v‖ₑ) (Ioc a b) :=
    lowerSemicontinuousOn_biSup (fun t ht => (hc t ht).enorm.lowerSemicontinuousOn)
  have heq : ∀ v ∈ Ioc a b, outEnv a f v =
      ⨆ t ∈ Icc (0 : ℝ) 1, ‖f (a + t * (v - a)) v‖ₑ := by
    intro v hv
    apply le_antisymm
    · apply iSup₂_le
      intro u hu
      have hden : 0 < v - a := sub_pos.mpr hv.1
      have ht : (u - a) / (v - a) ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg (sub_nonneg.mpr hu.1) hden.le,
          (div_le_one hden).mpr (sub_le_sub_right hu.2 a)⟩
      have hx : a + (u - a) / (v - a) * (v - a) = u := by
        rw [div_mul_cancel₀ _ hden.ne']
        ring
      apply le_iSup₂_of_le ((u - a) / (v - a)) ht
      rw [hx]
    · apply iSup₂_le
      intro t ht
      have hlo := mul_nonneg ht.1 (sub_nonneg.mpr hv.1.le)
      have hhi := mul_le_mul_of_nonneg_right ht.2 (sub_nonneg.mpr hv.1.le)
      apply enorm_le_normEnvelope f
      constructor <;> linarith only [hlo, hhi]
  have hm : Measurable (fun v : Ioc a b => outEnv a f v) := by
    convert (lowerSemicontinuous_restrict_iff.mpr hl).measurable using 1
    funext v
    exact heq v v.property
  simpa only [restrict_Ioc_eq_restrict_Icc] using
    aemeasurable_restrict_of_measurable_subtype (μ := volume) measurableSet_Ioc hm

private theorem aemeasurable_in_aux {E : Type*} [NormedAddCommGroup E]
    {a b : ℝ} {f : ℝ → ℝ → E}
    (hf : ContinuousOn (Function.uncurry f) (triangle a b ∩ {p | p.1 < p.2}))
    (hd : ContinuousOn (fun x => f x x) (Icc a b)) :
    AEMeasurable (inEnv b f) (volume.restrict (Icc a b)) := by
  have hc : ∀ t ∈ Icc (0 : ℝ) 1,
      ContinuousOn (fun u => f u (u + t * (b - u))) (Ico a b) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with ht0 | ht0
    · rw [← ht0]
      simpa only [zero_mul, add_zero] using hd.mono Ico_subset_Icc_self
    · apply hf.comp (show Continuous (fun u : ℝ => (u, u + t * (b - u))) by
        fun_prop).continuousOn
      intro u hu
      have hlo := mul_pos ht0 (sub_pos.mpr hu.2)
      have hhi := mul_le_mul_of_nonneg_right ht.2 (sub_nonneg.mpr hu.2.le)
      have hstrict : u < u + t * (b - u) := by linarith only [hlo]
      have hright : u + t * (b - u) ≤ b := by linarith only [hhi]
      exact ⟨⟨hu.1, hstrict.le, hright⟩, hstrict⟩
  have hl : LowerSemicontinuousOn
      (fun u => ⨆ t ∈ Icc (0 : ℝ) 1, ‖f u (u + t * (b - u))‖ₑ) (Ico a b) :=
    lowerSemicontinuousOn_biSup (fun t ht => (hc t ht).enorm.lowerSemicontinuousOn)
  have heq : ∀ u ∈ Ico a b, inEnv b f u =
      ⨆ t ∈ Icc (0 : ℝ) 1, ‖f u (u + t * (b - u))‖ₑ := by
    intro u hu
    apply le_antisymm
    · apply iSup₂_le
      intro v hv
      have hden : 0 < b - u := sub_pos.mpr hu.2
      have ht : (v - u) / (b - u) ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg (sub_nonneg.mpr hv.1) hden.le,
          (div_le_one hden).mpr (sub_le_sub_right hv.2 u)⟩
      have hx : u + (v - u) / (b - u) * (b - u) = v := by
        rw [div_mul_cancel₀ _ hden.ne']
        ring
      apply le_iSup₂_of_le ((v - u) / (b - u)) ht
      rw [hx]
    · apply iSup₂_le
      intro t ht
      have hlo := mul_nonneg ht.1 (sub_nonneg.mpr hu.2.le)
      have hhi := mul_le_mul_of_nonneg_right ht.2 (sub_nonneg.mpr hu.2.le)
      have hseg : u + t * (b - u) ∈ Icc u b := by
        constructor <;> linarith only [hlo, hhi]
      exact le_iSup₂_of_le (u + t * (b - u)) hseg le_rfl
  have hm : Measurable (fun u : Ico a b => inEnv b f u) := by
    convert (lowerSemicontinuous_restrict_iff.mpr hl).measurable using 1
    funext u
    exact heq u u.property
  simpa only [restrict_Ico_eq_restrict_Icc] using
    aemeasurable_restrict_of_measurable_subtype (μ := volume) measurableSet_Ico hm

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

private theorem mass_nonneg_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) : 0 ≤ S.m u v := by
  have hd : ∀ x ∈ Ioo u v, HasDerivAt (S.m u) (S.mV u x) x := by
    intro x hx
    have hr := (hasDerivWithinAt_section_v hS.c1_m
      ⟨hu, hx.1.le, hx.2.le.trans hvT⟩ (s := Icc u v)
      (fun _ hs => ⟨hu, hs.1, hs.2.trans hvT⟩)).hasDerivAt (Icc_mem_nhds hx.1 hx.2)
    change HasDerivAt (S.m u) (pdV (triangle 0 T) S.m u x) x at hr
    rw [(hS.eq_v (u, x) ⟨hu, hx.1.le, hx.2.le.trans hvT⟩ hx.1).2.2.1] at hr
    exact hr
  have hm : MonotoneOn (S.m u) (Icc u v) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc u v)
      (section_v_aux hS.c1_m hu huv hvT).continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hd x hx).deriv]
      have hmu := hS.one_sub_mu_pos (u, x) ⟨hu, hx.1.le, hx.2.le.trans hvT⟩
      have hlam := hS.lam_pos (u, x) ⟨hu, hx.1.le, hx.2.le.trans hvT⟩
      unfold Fields.mV
      positivity
  have h := hm ⟨le_rfl, huv⟩ ⟨huv, le_rfl⟩ huv
  rwa [(hS.axis u ⟨hu, le_rfl, huv.trans hvT⟩).2.1] at h

private theorem mu_nonneg_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {p : ℝ × ℝ} (hp : p ∈ triangle 0 T) :
    0 ≤ S.mu p.1 p.2 := by
  have hr : 0 ≤ S.r p.1 p.2 := by
    rcases eq_or_lt_of_le hp.2.1 with h | h
    · rw [← h, (hS.axis p.1 ⟨hp.1, le_rfl, h.trans_le hp.2.2⟩).1]
    · exact (hS.r_pos p hp h).le
  exact div_nonneg (mul_nonneg (by norm_num)
    (mass_nonneg_aux hS hp.1 hp.2.1 hp.2.2)) hr

private theorem continuous_jk_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) (hT : 0 < T) :
    (ContinuousOn (Function.uncurry (jC1 (triangle 0 T) S))
      (triangle 0 T ∩ {p | p.1 < p.2}) ∧
      ContinuousOn (fun x => jC1 (triangle 0 T) S x x) (Icc 0 T)) ∧
    (ContinuousOn (Function.uncurry (kC1 e (triangle 0 T) S))
      (triangle 0 T ∩ {p | p.1 < p.2}) ∧
      ContinuousOn (fun x => kC1 e (triangle 0 T) S x x) (Icc 0 T)) := by
  have cb := (c1_b_aux hS).continuousOn
  have cv := continuousOn_partial_v (c1_a_aux hS) (uniqueDiffOn_triangle hT)
  have cu := continuousOn_partial_u (c1_b_aux hS) (uniqueDiffOn_triangle hT)
  have cmu : ContinuousOn (Function.uncurry S.mu) (triangle 0 T ∩ {p | p.1 < p.2}) :=
    (continuousOn_const.mul (hS.c1_m.continuousOn.mono inter_subset_left)).div
      (hS.c1_r.continuousOn.mono inter_subset_left) (fun p hp => (hS.r_pos p hp.1 hp.2).ne')
  have cr := hS.c1_r.continuousOn.mono
    (show triangle 0 T ∩ {p | p.1 < p.2} ⊆ triangle 0 T from inter_subset_left)
  have cl := hS.c1_lam.continuousOn.mono
    (show triangle 0 T ∩ {p | p.1 < p.2} ⊆ triangle 0 T from inter_subset_left)
  have cn := hS.c1_nu.continuousOn.mono
    (show triangle 0 T ∩ {p | p.1 < p.2} ⊆ triangle 0 T from inter_subset_left)
  have cr0 : ∀ p ∈ triangle 0 T ∩ {p | p.1 < p.2}, S.r p.1 p.2 ≠ 0 :=
    fun p hp => (hS.r_pos p hp.1 hp.2).ne'
  have cx := (hS.c1_theta.continuousOn.mono inter_subset_left).div
    (Complex.continuous_ofReal.comp_continuousOn cl)
      (fun p hp => Complex.ofReal_ne_zero.mpr (hS.lam_pos p hp.1).ne')
  have cy := (hS.c1_xi.continuousOn.mono inter_subset_left).div
    (Complex.continuous_ofReal.comp_continuousOn cn)
      (fun p hp => Complex.ofReal_ne_zero.mpr (hS.nu_neg p hp.1).ne)
  have ch := Complex.continuous_ofReal.comp_continuousOn
    ((continuousOn_const (c := (1 : ℝ))).sub cmu)
  have cj := ch.mul ((cv.mono inter_subset_left).sub
    (((Complex.continuous_ofReal.comp_continuousOn (cl.div cr cr0)).mul
      (Complex.continuous_ofReal.comp_continuousOn (cx.norm.pow 2))).mul cx))
  have ck := ch.mul (((cu.mono inter_subset_left).add
    (((continuousOn_const (c := (I * e : ℂ))).mul (Complex.continuous_ofReal.comp_continuousOn
      (hS.c1_A.continuousOn.mono inter_subset_left))).mul (cb.mono inter_subset_left))).sub
    (((Complex.continuous_ofReal.comp_continuousOn (cn.div cr cr0)).mul
      (Complex.continuous_ofReal.comp_continuousOn (cy.norm.pow 2))).mul cy))
  have hd : MapsTo (fun x : ℝ => (x, x)) (Icc 0 T) (triangle 0 T) :=
    fun x hx => ⟨hx.1, le_rfl, hx.2⟩
  have cjaxis : ∀ x ∈ Icc 0 T, jC1 (triangle 0 T) S x x = pdV (triangle 0 T) S.a x x := by
    intro x hx
    simp only [jC1, Fields.mu, (hS.axis x (hd hx)).1, div_zero, sub_zero,
      Complex.ofReal_zero, zero_mul, one_mul]
  have ckaxis : ∀ x ∈ Icc 0 T, kC1 e (triangle 0 T) S x x =
      pdU (triangle 0 T) S.b x x + I * e * S.A x x * S.b x x := by
    intro x hx
    simp only [kC1, Fields.mu, (hS.axis x (hd hx)).1, div_zero, sub_zero,
      Complex.ofReal_zero, zero_mul, one_mul]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · apply cj.congr
    rintro ⟨u, v⟩ _
    simp only [Function.uncurry_apply_pair, jC1, pdV, Function.comp_apply, Pi.mul_apply,
      Pi.sub_apply, Pi.div_apply, Pi.pow_apply, Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_div, Complex.ofReal_pow]
  · exact (cv.comp (continuous_id.prodMk continuous_id).continuousOn hd).congr
      (fun x hx => cjaxis x hx)
  · apply ck.congr
    rintro ⟨u, v⟩ _
    simp only [Function.uncurry_apply_pair, kC1, pdU, Function.comp_apply, Pi.mul_apply,
      Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply, Complex.ofReal_sub,
      Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_pow]
  · exact ((cu.add (((continuousOn_const (c := (I * e : ℂ))).mul
      (Complex.continuous_ofReal.comp_continuousOn hS.c1_A.continuousOn)).mul cb)).comp
        (continuous_id.prodMk continuous_id).continuousOn hd).congr
      (fun x hx => ckaxis x hx)

private theorem norm_renorm_aux {h q B : ℝ} {d x g : ℂ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (hx : ‖x‖ ^ 2 ≤ B) (hc : (q : ℂ) * x = g) :
    ‖(h : ℂ) * (d - (q : ℂ) * (‖x‖ : ℂ) ^ 2 * x)‖ ≤ ‖d‖ + B * ‖g‖ := by
  have heq : (q : ℂ) * (‖x‖ : ℂ) ^ 2 * x = (‖x‖ : ℂ) ^ 2 * g := by
    rw [← hc]
    ring
  rw [heq, norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hh]
  calc
    _ ≤ 1 * ‖d - (‖x‖ : ℂ) ^ 2 * g‖ := mul_le_mul_of_nonneg_right hh1 (norm_nonneg _)
    _ ≤ ‖d‖ + ‖(‖x‖ : ℂ) ^ 2 * g‖ := by rw [one_mul]; exact norm_sub_le _ _
    _ = ‖d‖ + ‖x‖ ^ 2 * ‖g‖ := by rw [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_norm]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hx (norm_nonneg g))

private theorem norm_jk_le_aux {e T ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) {p : ℝ × ℝ} (hp : p ∈ triangle 0 T) :
    ‖jC1 (triangle 0 T) S p.1 p.2‖ ≤ ‖pdV (triangle 0 T) S.a p.1 p.2‖ +
      16 * ε ^ 2 * ‖pdV (triangle 0 T) S.phi p.1 p.2‖ ∧
    ‖kC1 e (triangle 0 T) S p.1 p.2‖ ≤
      ‖pdU (triangle 0 T) S.b p.1 p.2 + I * e * S.A p.1 p.2 * S.b p.1 p.2‖ +
      16 * ε ^ 2 * ‖pdU (triangle 0 T) S.phi p.1 p.2 + I * e * S.A p.1 p.2 * S.phi p.1 p.2‖ := by
  have hh := (hset.c1.one_sub_mu_pos p hp).le
  have hh1 : 1 - S.mu p.1 p.2 ≤ 1 := sub_le_self _ (mu_nonneg_aux hset.c1 hp)
  have hB : 0 ≤ 16 * ε ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
  rcases eq_or_lt_of_le hp.2.1 with heq | huv
  · have hr := (hset.c1.axis p.1 ⟨hp.1, le_rfl, heq.trans_le hp.2.2⟩).1
    rw [← heq]
    constructor
    · simp only [jC1, Fields.mu, hr, div_zero, sub_zero,
        Complex.ofReal_zero, zero_mul, one_mul]
      exact le_add_of_nonneg_right (mul_nonneg hB (norm_nonneg _))
    · simp only [kC1, Fields.mu, hr, div_zero, sub_zero,
        Complex.ofReal_zero, zero_mul, one_mul]
      exact le_add_of_nonneg_right (mul_nonneg hB (norm_nonneg _))
  have hr := Complex.ofReal_ne_zero.mpr (hset.c1.r_pos p hp huv).ne'
  have hl := Complex.ofReal_ne_zero.mpr (hset.c1.lam_pos p hp).ne'
  have hn := Complex.ofReal_ne_zero.mpr (hset.c1.nu_neg p hp).ne
  have hx : ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ^ 2 ≤ 16 * ε ^ 2 := by
    calc
      _ ≤ (4 * ε) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hset.box p hp).2.2.2.2.2.2.1 2
      _ = _ := by ring
  have hy : ‖S.xi p.1 p.2 / S.nu p.1 p.2‖ ^ 2 ≤ 16 * ε ^ 2 := by
    calc
      _ ≤ (4 * ε) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hset.box p hp).2.2.2.2.2.2.2 2
      _ = _ := by ring
  have hcx : ((S.lam p.1 p.2 / S.r p.1 p.2 : ℝ) : ℂ) *
      (S.theta p.1 p.2 / S.lam p.1 p.2) = pdV (triangle 0 T) S.phi p.1 p.2 := by
    rw [(hset.c1.eq_v p hp huv).2.2.2.2.2.1, Fields.phiV, Complex.ofReal_div]
    field_simp [hr, hl]
  have hcy : ((S.nu p.1 p.2 / S.r p.1 p.2 : ℝ) : ℂ) *
      (S.xi p.1 p.2 / S.nu p.1 p.2) =
      pdU (triangle 0 T) S.phi p.1 p.2 + I * e * S.A p.1 p.2 * S.phi p.1 p.2 := by
    rw [(hset.c1.eq_u p hp huv).2.2.2.2.1, Fields.phiU, sub_add_cancel, Complex.ofReal_div]
    field_simp [hr, hn]
  constructor
  · simpa only [jC1, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div,
      Complex.ofReal_pow] using norm_renorm_aux hh hh1 hx hcx
      (d := pdV (triangle 0 T) S.a p.1 p.2)
  · simpa only [kC1, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div,
      Complex.ofReal_pow] using norm_renorm_aux hh hh1 hy hcy
      (d := pdU (triangle 0 T) S.b p.1 p.2 + I * e * S.A p.1 p.2 * S.b p.1 p.2)

private theorem envelope_bound_aux {e T ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc 0 T,
      outEnv 0 (jC1 (triangle 0 T) S) x ≤ ENNReal.ofReal C ∧
      inEnv T (kC1 e (triangle 0 T) S) x ≤ ENNReal.ofReal C := by
  have cv := continuousOn_partial_v (c1_a_aux hset.c1) (uniqueDiffOn_triangle hset.pos)
  have cu := continuousOn_partial_u (c1_b_aux hset.c1) (uniqueDiffOn_triangle hset.pos)
  have pv := continuousOn_partial_v hset.c1.c1_phi (uniqueDiffOn_triangle hset.pos)
  have pu := continuousOn_partial_u hset.c1.c1_phi (uniqueDiffOn_triangle hset.pos)
  have cb := (c1_b_aux hset.c1).continuousOn
  have cp := hset.c1.c1_phi.continuousOn
  have cA := Complex.continuous_ofReal.comp_continuousOn hset.c1.c1_A.continuousOn
  have cd := cu.add (((continuousOn_const (c := (I * e : ℂ))).mul cA).mul cb)
  have cdp := pu.add (((continuousOn_const (c := (I * e : ℂ))).mul cA).mul cp)
  let B : ℝ × ℝ → ℝ := fun p =>
    ‖pdV (triangle 0 T) S.a p.1 p.2‖ +
    ‖pdU (triangle 0 T) S.b p.1 p.2 + I * e * S.A p.1 p.2 * S.b p.1 p.2‖ +
    16 * ε ^ 2 * (‖pdV (triangle 0 T) S.phi p.1 p.2‖ +
      ‖pdU (triangle 0 T) S.phi p.1 p.2 + I * e * S.A p.1 p.2 * S.phi p.1 p.2‖)
  have cB : ContinuousOn B (triangle 0 T) :=
    (cv.norm.add cd.norm).add (continuousOn_const.mul (pv.norm.add cdp.norm))
  obtain ⟨C, hC⟩ := (isCompact_triangle 0 T).bddAbove_image cB
  have hB0 : ∀ p, 0 ≤ B p := by intro p; dsimp only [B]; positivity
  have hC0 : 0 ≤ C := (hB0 (0, 0)).trans (hC (mem_image_of_mem _
    (show (0, 0) ∈ triangle 0 T from ⟨le_rfl, le_rfl, hset.pos.le⟩)))
  have hjk : ∀ p ∈ triangle 0 T,
      ‖jC1 (triangle 0 T) S p.1 p.2‖ ≤ C ∧ ‖kC1 e (triangle 0 T) S p.1 p.2‖ ≤ C := by
    intro p hp
    have hn := norm_jk_le_aux hset hp
    have hb := hC (mem_image_of_mem B hp)
    have hB : 0 ≤ 16 * ε ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
    dsimp only [B] at hb
    have hg0 := norm_nonneg (pdV (triangle 0 T) S.a p.1 p.2)
    have hd0 := norm_nonneg (pdU (triangle 0 T) S.b p.1 p.2 +
      I * e * S.A p.1 p.2 * S.b p.1 p.2)
    have hpv0 := mul_nonneg hB (norm_nonneg (pdV (triangle 0 T) S.phi p.1 p.2))
    have hpu0 := mul_nonneg hB (norm_nonneg (pdU (triangle 0 T) S.phi p.1 p.2 +
      I * e * S.A p.1 p.2 * S.phi p.1 p.2))
    constructor
    · linarith only [hn.1, hb, hd0, hpu0]
    · linarith only [hn.2, hb, hg0, hpv0]
  refine ⟨C, hC0, ?_⟩
  intro x hx
  constructor
  · apply iSup₂_le
    intro u hu
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hjk (u, x) ⟨hu.1, hu.2, hx.2⟩).1
  · apply iSup₂_le
    intro v hv
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hjk (x, v) ⟨hx.1, hv.1, hv.2⟩).2

/-- Classical bootstrap envelopes are finite on all controlled labels. This is
an analytic finiteness assertion, with no universal bound on higher derivatives. -/
theorem apriori_envelopes_finite {e T ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) {x : ℝ} (hx : x ∈ Icc 0 T) :
    outEnv 0 (jC1 (triangle 0 T) S) x ≠ ⊤ ∧
      inEnv T (kC1 e (triangle 0 T) S) x ≠ ⊤ := by
  obtain ⟨C, _, hC⟩ := envelope_bound_aux hset
  exact ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hC x hx).1,
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hC x hx).2⟩

/-- The real outgoing and incoming classical bootstrap envelopes are integrable
on the full label interval. The finite dominator is used only to justify
integration; no higher derivative bound enters the exported TV estimates. -/
theorem apriori_envelopes_integrable {e T ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) :
    IntervalIntegrable (fun x => (outEnv 0 (jC1 (triangle 0 T) S) x).toReal) volume 0 T ∧
    IntervalIntegrable (fun x => (inEnv T (kC1 e (triangle 0 T) S) x).toReal) volume 0 T := by
  obtain ⟨C, hC0, hC⟩ := envelope_bound_aux hset
  have hc := continuous_jk_aux hset.c1 hset.pos
  have hj := (aemeasurable_out_aux hc.1.1 hc.1.2).ennreal_toReal.aestronglyMeasurable
  have hk := (aemeasurable_in_aux hc.2.1 hc.2.2).ennreal_toReal.aestronglyMeasurable
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hset.pos.le,
    intervalIntegrable_iff_integrableOn_Icc_of_le hset.pos.le]
  constructor
  · apply Integrable.of_bound hj C
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hC x hx).1
    rwa [ENNReal.toReal_ofReal hC0] at hb
  · apply Integrable.of_bound hk C
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hC x hx).2
    rwa [ENNReal.toReal_ofReal hC0] at hb

end EmcsfAcExtension.Local


