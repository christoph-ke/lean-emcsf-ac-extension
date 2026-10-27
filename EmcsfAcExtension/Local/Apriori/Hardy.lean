module

public import EmcsfAcExtension.Local.Defs.C1Class
public import EmcsfAcExtension.Frozen.CovVarIn
import EmcsfAcExtension.Infra.HardyQuadratic
import EmcsfAcExtension.Infra.Calculus.PartialsC1

/-! # Radial Hardy estimates on classical null sections

The outgoing estimates at `charged_SF_new_version.tex:L4595–L4603` follow from the
weighted one-variable Hardy inequalities. All displayed coefficients are exactly
one and independent of the coupling, triangle, solution, and data size.
-/

public section

open MeasureTheory Set Filter Topology Complex

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

private theorem deriv_v_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T u v : ℝ} {f : ℝ → ℝ → E}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle 0 T))
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    ∀ᵐ x, x ∈ uIcc u v → HasDerivAt (f u) (pdV (triangle 0 T) f u x) x := by
  have ha : ∀ᵐ x : ℝ, x ≠ u := by simp [ae_iff, measure_singleton]
  have hb : ∀ᵐ x : ℝ, x ≠ v := by simp [ae_iff, measure_singleton]
  filter_upwards [ha, hb] with x hxu hxv hx
  rw [uIcc_of_le huv] at hx
  exact (hasDerivWithinAt_section_v hf ⟨hu, hx.1, hx.2.trans hvT⟩
    (s := Icc u v) (fun _ hs => ⟨hu, hs.1, hs.2.trans hvT⟩)).hasDerivAt
      (Icc_mem_nhds (lt_of_le_of_ne hx.1 hxu.symm) (lt_of_le_of_ne hx.2 hxv))

private theorem radius_v_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    ∫ s in u..v, S.lam u s = S.r u v := by
  have hc := (section_v_aux hS.c1_r hu huv hvT).continuousOn
  have hi := (section_v_aux hS.c1_lam hu huv hvT).continuousOn
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv hc
    (fun x hx => by
      have hd := (hasDerivWithinAt_section_v hS.c1_r
        ⟨hu, hx.1.le, hx.2.le.trans hvT⟩ (s := Icc u v)
        (fun _ hs => ⟨hu, hs.1, hs.2.trans hvT⟩)).hasDerivAt (Icc_mem_nhds hx.1 hx.2)
      change HasDerivAt (S.r u) (pdV (triangle 0 T) S.r u x) x at hd
      rw [(hS.eq_v (u, x) ⟨hu, hx.1.le, hx.2.le.trans hvT⟩ hx.1).1] at hd
      exact hd)
    (ContinuousOn.intervalIntegrable_of_Icc huv hi)
  simpa only [(hS.axis u ⟨hu, le_rfl, huv.trans hvT⟩).1, sub_zero] using heq

private theorem reconstruction_v_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    radialAverage (S.lam u) (S.a u) u v = S.phi u v := by
  have ca := (section_v_aux (c1_a_aux hS) hu huv.le hvT).continuousOn
  have cr := (section_v_aux hS.c1_r hu huv.le hvT).continuousOn
  have cp := (section_v_aux hS.c1_phi hu huv.le hvT).continuousOn
  have cl := (section_v_aux hS.c1_lam hu huv.le hvT).continuousOn
  have heq : (∫ x in u..v, (S.lam u x : ℂ) * S.a u x) =
      (S.r u v : ℂ) * S.phi u v - (S.r u u : ℂ) * S.phi u u :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv.le
    (Complex.continuous_ofReal.comp_continuousOn cr |>.mul cp)
    (fun x hx => by
      have hr := (hasDerivWithinAt_section_v hS.c1_r
        ⟨hu, hx.1.le, hx.2.le.trans hvT⟩ (s := Icc u v)
        (fun _ hs => ⟨hu, hs.1, hs.2.trans hvT⟩)).hasDerivAt (Icc_mem_nhds hx.1 hx.2)
      have hp := (hasDerivWithinAt_section_v hS.c1_phi
        ⟨hu, hx.1.le, hx.2.le.trans hvT⟩ (s := Icc u v)
        (fun _ hs => ⟨hu, hs.1, hs.2.trans hvT⟩)).hasDerivAt (Icc_mem_nhds hx.1 hx.2)
      change HasDerivAt (S.r u) (pdV (triangle 0 T) S.r u x) x at hr
      change HasDerivAt (S.phi u) (pdV (triangle 0 T) S.phi u x) x at hp
      have he := hS.eq_v (u, x) ⟨hu, hx.1.le, hx.2.le.trans hvT⟩ hx.1
      rw [he.1] at hr
      rw [he.2.2.2.2.2.1, Fields.phiV] at hp
      convert hr.ofReal_comp.mul hp using 1
      · rfl
      change (S.lam u x : ℂ) * (S.phi u x + S.theta u x / (S.lam u x : ℂ)) =
        (S.lam u x : ℂ) * S.phi u x + (S.r u x : ℂ) * (S.theta u x / (S.r u x : ℂ))
      have hrl : (S.r u x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
        (hS.r_pos (u, x) ⟨hu, hx.1.le, hx.2.le.trans hvT⟩ hx.1).ne'
      have hll : (S.lam u x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
        (hS.lam_pos (u, x) ⟨hu, hx.1.le, hx.2.le.trans hvT⟩).ne'
      field_simp [hrl, hll])
    (ContinuousOn.intervalIntegrable_of_Icc huv.le
      ((Complex.continuous_ofReal.comp_continuousOn cl).mul ca))
  rw [(hS.axis u ⟨hu, le_rfl, huv.le.trans hvT⟩).1, Complex.ofReal_zero,
    zero_mul, sub_zero] at heq
  unfold radialAverage
  rw [radius_v_aux hS hu huv.le hvT]
  simp only [Complex.real_smul, heq]
  have hr := (hS.r_pos (u, v) ⟨hu, huv.le, hvT⟩ huv).ne'
  rw [Complex.ofReal_inv, ← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hr), one_mul]

/-- [node restart-bv-hardy-out]
Outgoing radial moment estimate (`charged_SF_new_version.tex:L4597–L4603`).
The exact coefficient one is independent of `e`, `T`, `S`, and data size. -/
theorem bv_hardy_out {e T : ℝ} {S : Fields} (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    ‖S.theta u v / S.lam u v‖ ≤
      (S.r u v)⁻¹ * ∫ s in u..v, S.r u s * ‖pdV (triangle 0 T) S.a u s‖ := by
  have hT : 0 < T := lt_of_le_of_lt hu (huv.trans_le hvT)
  have hw : IntervalIntegrable (S.lam u) volume u v :=
    ContinuousOn.intervalIntegrable_of_Icc huv.le
      (section_v_aux hS.c1_lam hu huv.le hvT).continuousOn
  have hf : AbsolutelyContinuousOnInterval (S.a u) u v := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le huv.le]
    exact section_v_aux (c1_a_aux hS) hu huv.le hvT
  have hh : IntervalIntegrable (pdV (triangle 0 T) S.a u) volume u v :=
    ContinuousOn.intervalIntegrable_of_Icc huv.le (partial_v_aux (c1_a_aux hS) hT hu hvT)
  have hm := norm_sub_radialAverage_le_moment huv.le hw
    (fun x hx => (hS.lam_pos (u, x) ⟨hu, hx.1, hx.2.trans hvT⟩).le) hf hh
    (deriv_v_aux (c1_a_aux hS) hu huv.le hvT)
    (by rw [radius_v_aux hS hu huv.le hvT]; exact hS.r_pos (u, v) ⟨hu, huv.le, hvT⟩ huv)
  rw [reconstruction_v_aux hS hu huv hvT, radius_v_aux hS hu huv.le hvT] at hm
  simp only [Fields.a, add_sub_cancel_left] at hm
  convert hm using 1
  apply congrArg (fun z : ℝ => (S.r u v)⁻¹ * z)
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le huv.le] at hx
  dsimp only
  rw [radius_v_aux hS hu hx.1 (hx.2.trans hvT)]

/-- [node restart-bv-hardy-out]
The outgoing Hardy integrand is integrable, and its integral on every shortened
axis-to-point section is bounded by the normalized scalar variation.
The exact coefficient one is independent of all solution parameters. -/
theorem bv_hardy_out_integrated {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    IntervalIntegrable (fun x => S.lam u x / S.r u x *
      ‖S.theta u x / S.lam u x‖) volume u v ∧
    (∫ x in u..v, S.lam u x / S.r u x * ‖S.theta u x / S.lam u x‖) ≤
      (eVariationOn (S.a u) (Icc u v)).toReal := by
  rcases eq_or_lt_of_le huv with rfl | huv
  · constructor
    · exact IntervalIntegrable.refl
    · rw [intervalIntegral.integral_same]
      exact ENNReal.toReal_nonneg
  have hf : AbsolutelyContinuousOnInterval (S.a u) u v := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le huv.le]
    exact section_v_aux (c1_a_aux hS) hu huv.le hvT
  have hw : IntervalIntegrable (S.lam u) volume u v :=
    ContinuousOn.intervalIntegrable_of_Icc huv.le
      (section_v_aux hS.c1_lam hu huv.le hvT).continuousOn
  have hi := integrable_and_integral_weighted_deviation_le_variation huv.le hw
    (fun x hx => (hS.lam_pos (u, x) ⟨hu, hx.1, hx.2.trans hvT⟩).le)
    (section_v_aux (c1_a_aux hS) hu huv.le hvT).continuousOn
    (hf.boundedVariationOn_Icc huv.le)
  have heq : ∀ x ∈ uIoc u v,
      S.lam u x / (∫ t in u..x, S.lam u t) *
          ‖S.a u x - radialAverage (S.lam u) (S.a u) u x‖ =
        S.lam u x / S.r u x * ‖S.theta u x / S.lam u x‖ := by
    intro x hx
    rw [uIoc_of_le huv.le] at hx
    rw [radius_v_aux hS hu hx.1.le (hx.2.trans hvT),
      reconstruction_v_aux hS hu hx.1 (hx.2.trans hvT)]
    simp only [Fields.a, add_sub_cancel_left]
  refine ⟨hi.1.congr heq, ?_⟩
  rw [← intervalIntegral.integral_congr_ae (ae_of_all _ heq)]
  exact hi.2

/-- The outgoing normalized scalar variation equals the integral of its within
partial derivative norm. No constant or higher derivative norm occurs. -/
theorem bv_variation_out {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    (eVariationOn (S.a u) (Icc u v)).toReal =
      ∫ x in u..v, ‖pdV (triangle 0 T) S.a u x‖ := by
  have hf : AbsolutelyContinuousOnInterval (S.a u) u v := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le huv]
    exact section_v_aux (c1_a_aux hS) hu huv hvT
  rw [hf.toReal_eVariationOn_eq_integral_norm_deriv huv]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [deriv_v_aux (c1_a_aux hS) hu huv hvT] with x hx hmem
  rw [(hx (uIoc_subset_uIcc hmem)).deriv]

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

private theorem deriv_u_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T u v : ℝ} {f : ℝ → ℝ → E}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle 0 T))
    (hu : 0 ≤ u) (_huv : u ≤ v) (hvT : v ≤ T) {x : ℝ} (hx : x ∈ Ioo u v) :
    HasDerivAt (fun x => f x v) (pdU (triangle 0 T) f x v) x :=
  (hasDerivWithinAt_section_u hf ⟨hu.trans hx.1.le, hx.2.le, hvT⟩
    (s := Icc u v) (fun _ hs => ⟨hu.trans hs.1, hs.2, hvT⟩)).hasDerivAt
      (Icc_mem_nhds hx.1 hx.2)

private theorem radius_u_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    ∫ x in u..v, -S.nu x v = S.r u v := by
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv
    (section_u_aux hS.c1_r hu huv hvT).continuousOn
    (fun x hx => by
      have hd := deriv_u_aux hS.c1_r hu huv hvT hx
      rw [(hS.eq_u (x, v) ⟨hu.trans hx.1.le, hx.2.le, hvT⟩ hx.2).1] at hd
      exact hd)
    (ContinuousOn.intervalIntegrable_of_Icc huv
      (section_u_aux hS.c1_nu hu huv hvT).continuousOn)
  rw [(hS.axis v ⟨hu.trans huv, le_rfl, hvT⟩).1, zero_sub] at heq
  rw [intervalIntegral.integral_neg, heq, neg_neg]

private theorem radius_reverse_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    ∫ x in (-v)..(-u), -S.nu (-x) v = S.r u v := by
  rw [intervalIntegral.integral_comp_neg (fun x => -S.nu x v), neg_neg, neg_neg]
  exact radius_u_aux hS hu huv hvT

private theorem unit_frame_aux {a b e : ℝ} {A : ℝ → ℝ}
    (hab : a ≤ b) (hA : ContinuousOn A (Icc a b)) :
    ∃ P : ℝ → ℂ, ContDiff ℝ 1 P ∧ (∀ x, ‖P x‖ = 1) ∧
      ∀ x ∈ Icc a b, P x = Complex.exp (I * e * ∫ t in a..x, A t) ∧
        HasDerivAt P (P x * (I * e * A x)) x := by
  let B : ℝ → ℝ := fun t => A (projIcc a b hab t)
  have hB : Continuous B := hA.domRestrict.comp continuous_projIcc
  have hBA : ∀ x ∈ Icc a b, B x = A x := by
    intro x hx
    dsimp only [B]
    rw [projIcc_of_mem hab hx]
  let F : ℝ → ℝ := fun x => ∫ t in a..x, B t
  have hdF : ∀ x, HasDerivAt F (B x) x := fun x => (hB.integral_hasStrictDerivAt a x).hasDerivAt
  have hF : ContDiff ℝ 1 F := contDiff_one_iff_deriv.mpr
    ⟨fun x => (hdF x).differentiableAt,
      by convert hB using 1; funext x; exact (hdF x).deriv⟩
  let P : ℝ → ℂ := fun x => Complex.exp (I * e * F x)
  have hPc : ContDiff ℝ 1 P :=
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hF) :
      ContDiff ℝ 1 (fun x => (I * e) * (F x : ℂ))).cexp
  refine ⟨P, hPc, ?_, ?_⟩
  · intro x
    simp [P, Complex.norm_exp]
  · intro x hx
    have hFx : F x = ∫ t in a..x, A t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hx.1] at ht
      exact hBA t ⟨ht.1, ht.2.trans hx.2⟩
    refine ⟨by simp only [P, hFx], ?_⟩
    simpa only [P, hBA x hx] using ((hdF x).ofReal_comp.const_mul (I * e)).cexp

private theorem reconstruction_in_aux {e T c v : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) (hc : 0 ≤ c) (hcv : c ≤ v) (hvT : v ≤ T)
    {P : ℝ → ℂ} (hP : ContDiff ℝ 1 P)
    (hdP : ∀ x ∈ Icc c v, HasDerivAt P (P x * (I * e * S.A x v)) x)
    {u : ℝ} (hcu : c ≤ u) (huv : u < v) :
    radialAverage (fun x => -S.nu (-x) v) (fun x => P (-x) * S.b (-x) v) (-v) (-u) =
      P u * S.phi u v := by
  have hu := hc.trans hcu
  have cr := (section_u_aux hS.c1_r hu huv.le hvT).continuousOn
  have cp := hP.continuous.continuousOn.mul
    (section_u_aux hS.c1_phi hu huv.le hvT).continuousOn
  have cb := hP.continuous.continuousOn.mul
    (section_u_aux (c1_b_aux hS) hu huv.le hvT).continuousOn
  have cn := (section_u_aux hS.c1_nu hu huv.le hvT).continuousOn
  have heq : (∫ x in u..v, (S.nu x v : ℂ) * (P x * S.b x v)) =
      (S.r v v : ℂ) * (P v * S.phi v v) - (S.r u v : ℂ) * (P u * S.phi u v) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv.le
      ((Complex.continuous_ofReal.comp_continuousOn cr).mul cp)
      (fun x hx => by
        have hr := deriv_u_aux hS.c1_r hu huv.le hvT hx
        have hp := deriv_u_aux hS.c1_phi hu huv.le hvT hx
        have he := hS.eq_u (x, v) ⟨hu.trans hx.1.le, hx.2.le, hvT⟩ hx.2
        rw [he.1] at hr
        rw [he.2.2.2.2.1, Fields.phiU] at hp
        convert hr.ofReal_comp.mul ((hdP x ⟨hcu.trans hx.1.le, hx.2.le⟩).mul hp) using 1
        · rfl
        change (S.nu x v : ℂ) * (P x * (S.phi x v + S.xi x v / (S.nu x v : ℂ))) =
          (S.nu x v : ℂ) * (P x * S.phi x v) + (S.r x v : ℂ) *
            (P x * (I * e * S.A x v) * S.phi x v +
              P x * (S.xi x v / (S.r x v : ℂ) - I * e * S.A x v * S.phi x v))
        have hr0 := Complex.ofReal_ne_zero.mpr
          (hS.r_pos (x, v) ⟨hu.trans hx.1.le, hx.2.le, hvT⟩ hx.2).ne'
        have hn0 := Complex.ofReal_ne_zero.mpr
          (hS.nu_neg (x, v) ⟨hu.trans hx.1.le, hx.2.le, hvT⟩).ne
        field_simp [hr0, hn0]
        ring)
      (ContinuousOn.intervalIntegrable_of_Icc huv.le
        ((Complex.continuous_ofReal.comp_continuousOn cn).mul cb))
  rw [(hS.axis v ⟨hc.trans hcv, le_rfl, hvT⟩).1, Complex.ofReal_zero, zero_mul,
    zero_sub] at heq
  unfold radialAverage
  rw [radius_reverse_aux hS hu huv.le hvT]
  simp only [Complex.real_smul]
  have hi : (∫ x in (-v)..(-u), ((-S.nu (-x) v : ℝ) : ℂ) * (P (-x) * S.b (-x) v)) =
      (S.r u v : ℂ) * (P u * S.phi u v) := by
    simp only [Complex.ofReal_neg, neg_mul]
    rw [intervalIntegral.integral_neg,
      intervalIntegral.integral_comp_neg (fun x => (S.nu x v : ℂ) * (P x * S.b x v)),
      neg_neg, neg_neg, heq, neg_neg]
  rw [hi, Complex.ofReal_inv, ← mul_assoc,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr
      (hS.r_pos (u, v) ⟨hu, huv.le, hvT⟩ huv).ne'), one_mul]

private theorem reverse_frame_aux {e T u v : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T)
    {P : ℝ → ℂ} (hP : ContDiff ℝ 1 P)
    (hdP : ∀ x ∈ Icc u v, HasDerivAt P (P x * (I * e * S.A x v)) x) :
    AbsolutelyContinuousOnInterval (fun x => P (-x) * S.b (-x) v) (-v) (-u) ∧
    IntervalIntegrable (fun x => -(P (-x) *
      (pdU (triangle 0 T) S.b (-x) v + I * e * S.A (-x) v * S.b (-x) v))) volume (-v) (-u) ∧
    ∀ᵐ x, x ∈ uIcc (-v) (-u) → HasDerivAt (fun x => P (-x) * S.b (-x) v)
      (-(P (-x) * (pdU (triangle 0 T) S.b (-x) v + I * e * S.A (-x) v * S.b (-x) v))) x := by
  have hT : 0 < T := lt_of_le_of_lt hu (huv.trans_le hvT)
  have hm : MapsTo Neg.neg (Icc (-v) (-u)) (Icc u v) := by
    intro x hx
    constructor <;> linarith only [hx.1, hx.2]
  have hf : ContDiffOn ℝ 1 (fun x => P (-x) * S.b (-x) v) (Icc (-v) (-u)) :=
    (hP.contDiffOn.mul (section_u_aux (c1_b_aux hS) hu huv.le hvT)).comp
      (contDiff_id.neg).contDiffOn hm
  have hc : ContinuousOn (fun x => -(P x *
      (pdU (triangle 0 T) S.b x v + I * e * S.A x v * S.b x v))) (Icc u v) :=
    (hP.continuous.continuousOn.mul ((partial_u_aux (c1_b_aux hS) hT hu hvT).add
      ((continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
        (section_u_aux hS.c1_A hu huv.le hvT).continuousOn)).mul
          (section_u_aux (c1_b_aux hS) hu huv.le hvT).continuousOn))).neg
  refine ⟨?_, ContinuousOn.intervalIntegrable_of_Icc (neg_le_neg huv.le)
    (hc.comp continuous_neg.continuousOn hm), ?_⟩
  · apply ContDiffOn.absolutelyContinuousOnInterval
    rwa [uIcc_of_le (neg_le_neg huv.le)]
  · have ha : ∀ᵐ x : ℝ, x ≠ -v := by simp [ae_iff, measure_singleton]
    have hb : ∀ᵐ x : ℝ, x ≠ -u := by simp [ae_iff, measure_singleton]
    filter_upwards [ha, hb] with x hxv hxu hx
    rw [uIcc_of_le (neg_le_neg huv.le)] at hx
    have hleft : -v < x := lt_of_le_of_ne hx.1 hxv.symm
    have hright : x < -u := lt_of_le_of_ne hx.2 hxu
    have hxx : -x ∈ Ioo u v := by constructor <;> linarith only [hleft, hright]
    have hd := (hdP (-x) ⟨hxx.1.le, hxx.2.le⟩).mul
      (deriv_u_aux (c1_b_aux hS) hu huv.le hvT hxx)
    convert hd.scomp x (hasDerivAt_neg x) using 1
    · rfl
    simp only [neg_one_smul]
    ring

/-- [node restart-bv-hardy-in]
Incoming radial moment in the unitary parallel frame, as repaired in
internal project record, section `restart-bv-hardy-in` (`charged_SF_new_version.tex:L4604–L4613`).
The exact coefficient one is independent of all parameters; no box is needed. -/
theorem bv_hardy_in {e T : ℝ} {S : Fields} (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    ‖S.xi u v / S.nu u v‖ ≤ (S.r u v)⁻¹ * ∫ x in u..v, S.r x v *
      ‖pdU (triangle 0 T) S.b x v + I * e * S.A x v * S.b x v‖ := by
  obtain ⟨P, hP, hPn, hPd⟩ := unit_frame_aux (e := e) huv.le
    (section_u_aux hS.c1_A hu huv.le hvT).continuousOn
  have hder := reverse_frame_aux hS hu huv hvT hP (fun x hx => (hPd x hx).2)
  have hm : MapsTo Neg.neg (Icc (-v) (-u)) (Icc u v) := by
    intro x hx
    constructor <;> linarith only [hx.1, hx.2]
  have hw : IntervalIntegrable (fun x => -S.nu (-x) v) volume (-v) (-u) :=
    ContinuousOn.intervalIntegrable_of_Icc (neg_le_neg huv.le)
      ((section_u_aux hS.c1_nu hu huv.le hvT).continuousOn.neg.comp
        continuous_neg.continuousOn hm)
  have hi := norm_sub_radialAverage_le_moment (neg_le_neg huv.le) hw
    (fun x hx => (neg_pos.mpr (hS.nu_neg (-x, v) ⟨hu.trans (hm hx).1, (hm hx).2, hvT⟩)).le)
    hder.1 hder.2.1 hder.2.2
    (by rw [radius_reverse_aux hS hu huv.le hvT]; exact hS.r_pos (u, v) ⟨hu, huv.le, hvT⟩ huv)
  rw [reconstruction_in_aux hS hu huv.le hvT hP (fun x hx => (hPd x hx).2) le_rfl huv,
    radius_reverse_aux hS hu huv.le hvT] at hi
  simp only [neg_neg] at hi
  have hdev : ‖P u * S.b u v - P u * S.phi u v‖ = ‖S.xi u v / S.nu u v‖ := by
    rw [← mul_sub, norm_mul, hPn, one_mul, Fields.b, add_sub_cancel_left]
  rw [hdev] at hi
  convert hi using 1
  apply congrArg (fun z : ℝ => (S.r u v)⁻¹ * z)
  have href := intervalIntegral.integral_comp_neg (fun x => S.r x v *
    ‖pdU (triangle 0 T) S.b x v + I * e * S.A x v * S.b x v‖) (a := -v) (b := -u)
  simp only [neg_neg] at href
  rw [← href]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le (neg_le_neg huv.le)] at hx
  dsimp only
  have hr := radius_reverse_aux hS (hu.trans (hm hx).1) (hm hx).2 hvT
  simp only [neg_neg] at hr
  rw [hr, norm_neg, norm_mul, hPn, one_mul]

/-- [node restart-bv-hardy-in]
Integrability and the incoming Hardy integral on any shortened axis-to-point
section. The right side is the covariant derivative norm, with exact universal
coefficient one, as in the approved incoming repair. -/
theorem bv_hardy_in_integrated {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    IntervalIntegrable (fun x => -S.nu x v / S.r x v *
      ‖S.xi x v / S.nu x v‖) volume u v ∧
    (∫ x in u..v, -S.nu x v / S.r x v * ‖S.xi x v / S.nu x v‖) ≤
      ∫ x in u..v, ‖pdU (triangle 0 T) S.b x v + I * e * S.A x v * S.b x v‖ := by
  rcases eq_or_lt_of_le huv with rfl | huv
  · exact ⟨IntervalIntegrable.refl,
      by rw [intervalIntegral.integral_same, intervalIntegral.integral_same]⟩
  obtain ⟨P, hP, hPn, hPd⟩ := unit_frame_aux (e := e) huv.le
    (section_u_aux hS.c1_A hu huv.le hvT).continuousOn
  have hder := reverse_frame_aux hS hu huv hvT hP (fun x hx => (hPd x hx).2)
  have hm : MapsTo Neg.neg (Icc (-v) (-u)) (Icc u v) := by
    intro x hx
    constructor <;> linarith only [hx.1, hx.2]
  have hw : IntervalIntegrable (fun x => -S.nu (-x) v) volume (-v) (-u) :=
    ContinuousOn.intervalIntegrable_of_Icc (neg_le_neg huv.le)
      ((section_u_aux hS.c1_nu hu huv.le hvT).continuousOn.neg.comp
        continuous_neg.continuousOn hm)
  have hfc : ContinuousOn (fun x => P (-x) * S.b (-x) v) (Icc (-v) (-u)) := by
    simpa only [uIcc_of_le (neg_le_neg huv.le)] using hder.1.continuousOn
  have hi := integrable_and_integral_weighted_deviation_le_variation (neg_le_neg huv.le) hw
    (fun x hx => (neg_pos.mpr (hS.nu_neg (-x, v) ⟨hu.trans (hm hx).1, (hm hx).2, hvT⟩)).le)
    hfc (hder.1.boundedVariationOn_Icc (neg_le_neg huv.le))
  have heq : ∀ x ∈ uIoc (-v) (-u),
      (-S.nu (-x) v) / (∫ t in (-v)..x, -S.nu (-t) v) *
        ‖P (-x) * S.b (-x) v - radialAverage (fun t => -S.nu (-t) v)
          (fun t => P (-t) * S.b (-t) v) (-v) x‖ =
      -S.nu (-x) v / S.r (-x) v * ‖S.xi (-x) v / S.nu (-x) v‖ := by
    intro x hx
    rw [uIoc_of_le (neg_le_neg huv.le)] at hx
    have hxx : -x < v := by linarith only [hx.1]
    have hux : u ≤ -x := by linarith only [hx.2]
    have hr := radius_reverse_aux hS (hu.trans hux) hxx.le hvT
    have hp := reconstruction_in_aux hS hu huv.le hvT hP
      (fun x hx => (hPd x hx).2) hux hxx
    simp only [neg_neg] at hr hp
    rw [hr, hp, ← mul_sub, norm_mul, hPn, one_mul]
    simp only [Fields.b, add_sub_cancel_left]
  have hii := hi.1.congr heq
  refine ⟨(IntervalIntegrable.iff_comp_neg).mpr hii.symm, ?_⟩
  have hvar := hder.1.toReal_eVariationOn_eq_integral_norm_deriv (neg_le_neg huv.le)
  rw [hvar] at hi
  have hdint : (∫ x in (-v)..(-u), ‖deriv (fun x => P (-x) * S.b (-x) v) x‖) =
      ∫ x in u..v, ‖pdU (triangle 0 T) S.b x v + I * e * S.A x v * S.b x v‖ := by
    calc
      _ = ∫ x in (-v)..(-u), ‖pdU (triangle 0 T) S.b (-x) v +
          I * e * S.A (-x) v * S.b (-x) v‖ := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hder.2.2] with x hx hmem
        rw [(hx (uIoc_subset_uIcc hmem)).deriv, norm_neg, norm_mul, hPn, one_mul]
      _ = _ := by
        simpa only [neg_neg] using intervalIntegral.integral_comp_neg
          (fun x => ‖pdU (triangle 0 T) S.b x v + I * e * S.A x v * S.b x v‖)
          (a := -v) (b := -u)
  have hb := hi.2
  rw [intervalIntegral.integral_congr_ae (ae_of_all _ heq), hdint] at hb
  have href := intervalIntegral.integral_comp_neg
    (fun x => -S.nu x v / S.r x v * ‖S.xi x v / S.nu x v‖) (a := -v) (b := -u)
  simp only [neg_neg] at href
  rwa [href] at hb

/-- The frozen covariant incoming variation is exactly the integral of the
covariant within-partial norm on a classical section. The transported curve
uses the frozen phase with base point `u`. No parameter-dependent constant occurs. -/
theorem bv_variation_in {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    (covVarIn e S.A S.b u v v).toReal =
      ∫ x in u..v, ‖pdU (triangle 0 T) S.b x v + I * e * S.A x v * S.b x v‖ := by
  obtain ⟨P, hP, hPn, hPd⟩ := unit_frame_aux (e := e) huv
    (section_u_aux hS.c1_A hu huv hvT).continuousOn
  have hf : AbsolutelyContinuousOnInterval (fun x => P x * S.b x v) u v := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le huv]
    exact hP.contDiffOn.mul (section_u_aux (c1_b_aux hS) hu huv hvT)
  have heq : covVarIn e S.A S.b u v v = eVariationOn (fun x => P x * S.b x v) (Icc u v) := by
    unfold covVarIn
    apply eVariationOn.congr
    intro x hx
    change Complex.exp (I * e * ∫ t in u..x, S.A t v) * S.b x v = P x * S.b x v
    rw [(hPd x hx).1]
  rw [heq, hf.toReal_eVariationOn_eq_integral_norm_deriv huv]
  apply intervalIntegral.integral_congr_ae
  have ha : ∀ᵐ x : ℝ, x ≠ u := by simp [ae_iff, measure_singleton]
  have hb : ∀ᵐ x : ℝ, x ≠ v := by simp [ae_iff, measure_singleton]
  filter_upwards [ha, hb] with x hxu hxv hx
  rw [uIoc_of_le huv] at hx
  have hxx : x ∈ Ioo u v := ⟨hx.1, lt_of_le_of_ne hx.2 hxv⟩
  have hd := (hPd x ⟨hx.1.le, hx.2⟩).2.mul
    (deriv_u_aux (c1_b_aux hS) hu huv hvT hxx)
  have hd' : HasDerivAt (fun x => P x * S.b x v)
      (P x * (pdU (triangle 0 T) S.b x v + I * e * S.A x v * S.b x v)) x := by
    convert hd using 1
    ring
  rw [hd'.deriv, norm_mul, hPn, one_mul]

end EmcsfAcExtension.Local
