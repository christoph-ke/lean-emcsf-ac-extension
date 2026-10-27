module

public import EmcsfAcExtension.Local.Calculus.Curvature
public import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Curvature representations integrated from the regular center

The integrands extend continuously to the classical axis. The fundamental theorem
therefore integrates the off-axis primitive identities without an assumed endpoint
limit or an unproved integrability premise. The incoming formula uses the auditor's
explicit integrals while the incoming definitions packet is still absent.
-/

public section

open Set Complex MeasureTheory

namespace EmcsfAcExtension.Local

private theorem continuousOn_charge_ratio_aux {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T)) :
    ContinuousOn (fun p : ℝ × ℝ => S.Q p.1 p.2 / S.r p.1 p.2) (triangle 0 T) := by
  obtain ⟨q, cq, hq, haxis⟩ := exists_continuous_charge_ratio_aux hT hS
  apply cq.congr
  intro p hp
  rcases p with ⟨u, v⟩
  change S.Q u v / S.r u v = q (u, v)
  by_cases huv : u < v
  · exact (hq u v hp huv).symm
  · have he : u = v := le_antisymm hp.2.1 (not_lt.mp huv)
    subst v
    rw [haxis u ⟨hp.1, hp.2.2⟩, (hS.axis u hp).1, div_zero]

private theorem continuousOn_curvature_em_aux {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T)) :
    ContinuousOn (fun p : ℝ × ℝ =>
      ((S.lam p.1 p.2 * S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 : ℝ) : ℂ) -
        I * e * S.Q p.1 p.2 * S.theta p.1 p.2 * starRingEnd ℂ (S.phi p.1 p.2))
      (triangle 0 T) ∧
    ContinuousOn (fun p : ℝ × ℝ =>
      ((S.nu p.1 p.2 * S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 : ℝ) : ℂ) +
        I * e * S.Q p.1 p.2 * S.xi p.1 p.2 * starRingEnd ℂ (S.phi p.1 p.2))
      (triangle 0 T) := by
  have cq := continuousOn_charge_ratio_aux hT hS
  have cl : ContinuousOn (fun p : ℝ × ℝ =>
      ((S.lam p.1 p.2 * S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 : ℝ) : ℂ))
      (triangle 0 T) := by
    apply (continuous_ofReal.comp_continuousOn (hS.c1_lam.continuousOn.mul (cq.pow 2))).congr
    intro p hp
    simp only [Function.comp_apply, Function.uncurry_def, Pi.mul_apply, Pi.pow_apply]
    congr 1
    rw [div_pow]
    ring
  have cn : ContinuousOn (fun p : ℝ × ℝ =>
      ((S.nu p.1 p.2 * S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 : ℝ) : ℂ))
      (triangle 0 T) := by
    apply (continuous_ofReal.comp_continuousOn (hS.c1_nu.continuousOn.mul (cq.pow 2))).congr
    intro p hp
    simp only [Function.comp_apply, Function.uncurry_def, Pi.mul_apply, Pi.pow_apply]
    congr 1
    rw [div_pow]
    ring
  have cQ := continuous_ofReal.comp_continuousOn hS.c1_Q.continuousOn
  have cp : ContinuousOn (fun p : ℝ × ℝ => starRingEnd ℂ (S.phi p.1 p.2))
      (triangle 0 T) := by
    simpa only [starRingEnd_apply, Function.uncurry_def, Function.comp_apply,
      Pi.div_apply] using hS.c1_phi.continuousOn.star
  exact ⟨cl.sub ((((continuousOn_const (c := I * e)).mul cQ).mul
    hS.c1_theta.continuousOn).mul cp),
    cn.add ((((continuousOn_const (c := I * e)).mul cQ).mul
      hS.c1_xi.continuousOn).mul cp)⟩

private theorem continuousOn_curvature_scalar_aux {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T)) :
    ContinuousOn (fun p : ℝ × ℝ => (S.r p.1 p.2 : ℂ) *
      starRingEnd ℂ (S.xi p.1 p.2 / S.nu p.1 p.2) * jC1 (triangle 0 T) S p.1 p.2)
      (triangle 0 T) ∧
    ContinuousOn (fun p : ℝ × ℝ => (S.r p.1 p.2 : ℂ) *
      starRingEnd ℂ (S.theta p.1 p.2 / S.lam p.1 p.2) * kC1 e (triangle 0 T) S p.1 p.2)
      (triangle 0 T) := by
  have cr := continuous_ofReal.comp_continuousOn hS.c1_r.continuousOn
  have cn : ContinuousOn (fun p : ℝ × ℝ => starRingEnd ℂ (S.xi p.1 p.2 / S.nu p.1 p.2))
      (triangle 0 T) := by
    simpa only [starRingEnd_apply, Function.uncurry_def, Function.comp_apply,
      Pi.div_apply] using (hS.c1_xi.continuousOn.div
      (continuous_ofReal.comp_continuousOn hS.c1_nu.continuousOn)
      (fun p hp => Complex.ofReal_ne_zero.mpr (hS.nu_neg p hp).ne)).star
  have cl : ContinuousOn (fun p : ℝ × ℝ => starRingEnd ℂ (S.theta p.1 p.2 / S.lam p.1 p.2))
      (triangle 0 T) := by
    simpa only [starRingEnd_apply, Function.uncurry_def, Function.comp_apply,
      Pi.div_apply] using (hS.c1_theta.continuousOn.div
      (continuous_ofReal.comp_continuousOn hS.c1_lam.continuousOn)
      (fun p hp => Complex.ofReal_ne_zero.mpr (hS.lam_pos p hp).ne')).star
  exact ⟨(cr.mul cn).mul (continuousOn_jC1_aux hT hS),
    (cr.mul cl).mul (continuousOn_kC1_aux hT hS)⟩

/-- [node restart-sec-bv-stability-independent#curvature-radial-representation]
The outgoing scalar primitive and electromagnetic remainder reconstruct the curvature,
charged_SF_new_version.tex:L5041–5046. This is a classical statement (internal project record); the
proof already
works on the C¹ class by the integral route, with no frozen-AC interpretation claimed. -/
theorem Stab.curvature_radial_representation {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    curv S u v = curvScalar (triangle 0 T) S u v + curvEM e S u v := by
  have hT : 0 < T := hu.trans_lt (huv.trans_le hvT)
  let F (s : ℝ) := (S.r u s : ℂ) * starRingEnd ℂ (S.xi u s / S.nu u s) *
    jC1 (triangle 0 T) S u s
  let E (s : ℝ) := ((S.lam u s * S.Q u s ^ 2 / S.r u s ^ 2 : ℝ) : ℂ) -
    I * e * S.Q u s * S.theta u s * starRingEnd ℂ (S.phi u s)
  let P (s : ℝ) := (S.r u s : ℂ) * curv S u s
  have hseg (s : ℝ) (hs : s ∈ Icc u v) : (u, s) ∈ triangle 0 T :=
    ⟨hu, hs.1, hs.2.trans hvT⟩
  have cF : ContinuousOn F (Icc u v) :=
    (continuousOn_curvature_scalar_aux hT hS).1.comp
      (continuousOn_const.prodMk continuousOn_id) hseg
  have cE : ContinuousOn E (Icc u v) :=
    (continuousOn_curvature_em_aux hT hS).1.comp (f := fun s : ℝ => (u, s))
      (continuousOn_const.prodMk continuousOn_id) hseg
  have cP : ContinuousOn P (Icc u v) :=
    ((continuous_ofReal.comp_continuousOn hS.c1_r.continuousOn).mul
      (continuousOn_curv_aux hT hS)).comp
        (continuousOn_const.prodMk continuousOn_id) hseg
  have hd (s : ℝ) (hs : s ∈ Ioo u v) : HasDerivAt P (F s + E s) s := by
    apply ((bv_c_v hS hu hs.1 (hs.2.le.trans hvT)).hasDerivAt
      (Icc_mem_nhds hs.1 (hs.2.trans_le hvT))).congr_deriv
    dsimp only [F, E]
    simp only [map_div₀, Complex.conj_ofReal]
    ring
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv.le cP hd
    ((cF.add cE).intervalIntegrable_of_Icc huv.le)
  rw [intervalIntegral.integral_add (cF.intervalIntegrable_of_Icc huv.le)
    (cE.intervalIntegrable_of_Icc huv.le)] at heq
  have hra := (hS.axis u ⟨hu, le_rfl, huv.le.trans hvT⟩).1
  change (∫ s in u..v, F s) + (∫ s in u..v, E s) =
    (S.r u v : ℂ) * curv S u v - (S.r u u : ℂ) * curv S u u at heq
  rw [hra, ofReal_zero, zero_mul, sub_zero] at heq
  have hr : (S.r u v : ℂ) ≠ 0 := by
    exact_mod_cast (hS.r_pos (u, v) ⟨hu, huv.le, hvT⟩ huv).ne'
  calc
    curv S u v = (S.r u v : ℂ)⁻¹ * ((S.r u v : ℂ) * curv S u v) := by
      rw [← mul_assoc, inv_mul_cancel₀ hr, one_mul]
    _ = (S.r u v : ℂ)⁻¹ * ((∫ s in u..v, F s) + ∫ s in u..v, E s) := by rw [heq]
    _ = _ := by rw [mul_add]; rfl

/-- Incoming conjugate curvature representation with the explicit auditor integrals
of internal project record. The minus signs come from integrating backwards from `(v,v)`.
This classical identity has no gauge or smallness hypothesis. -/
theorem Stab.curvature_radial_representation_in {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    starRingEnd ℂ (curv S u v) =
      -((S.r u v : ℂ)⁻¹ * ∫ s in u..v,
        (S.r s v : ℂ) * starRingEnd ℂ (S.theta s v / S.lam s v) *
          kC1 e (triangle 0 T) S s v) +
      -((S.r u v : ℂ)⁻¹ * ∫ s in u..v,
        ((S.nu s v * S.Q s v ^ 2 / S.r s v ^ 2 : ℝ) : ℂ) +
          I * e * S.Q s v * S.xi s v * starRingEnd ℂ (S.phi s v)) := by
  have hT : 0 < T := hu.trans_lt (huv.trans_le hvT)
  let F (s : ℝ) := (S.r s v : ℂ) * starRingEnd ℂ (S.theta s v / S.lam s v) *
    kC1 e (triangle 0 T) S s v
  let E (s : ℝ) := ((S.nu s v * S.Q s v ^ 2 / S.r s v ^ 2 : ℝ) : ℂ) +
    I * e * S.Q s v * S.xi s v * starRingEnd ℂ (S.phi s v)
  let P (s : ℝ) := (S.r s v : ℂ) * starRingEnd ℂ (curv S s v)
  have hseg (s : ℝ) (hs : s ∈ Icc u v) : (s, v) ∈ triangle 0 T :=
    ⟨hu.trans hs.1, hs.2, hvT⟩
  have cF : ContinuousOn F (Icc u v) :=
    (continuousOn_curvature_scalar_aux hT hS).2.comp
      (continuousOn_id.prodMk continuousOn_const) hseg
  have cE : ContinuousOn E (Icc u v) := by
    have hc := (continuousOn_curvature_em_aux hT hS).2.comp
      (continuousOn_id.prodMk continuousOn_const) hseg
    exact hc
  have cC : ContinuousOn (fun p : ℝ × ℝ => starRingEnd ℂ (curv S p.1 p.2))
      (triangle 0 T) := by
    simpa only [starRingEnd_apply, Function.uncurry_def, Function.comp_apply,
      Pi.div_apply] using (continuousOn_curv_aux hT hS).star
  have cP : ContinuousOn P (Icc u v) :=
    ((continuous_ofReal.comp_continuousOn hS.c1_r.continuousOn).mul cC).comp
      (continuousOn_id.prodMk continuousOn_const) hseg
  have hd (s : ℝ) (hs : s ∈ Ioo u v) : HasDerivAt P (F s + E s) s := by
    apply ((bv_c_u hS (hu.trans hs.1.le) hs.2 hvT).hasDerivAt
      (Icc_mem_nhds (hu.trans_lt hs.1) hs.2)).congr_deriv
    dsimp only [F, E]
    simp only [map_div₀, Complex.conj_ofReal]
    ring
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv.le cP hd
    ((cF.add cE).intervalIntegrable_of_Icc huv.le)
  rw [intervalIntegral.integral_add (cF.intervalIntegrable_of_Icc huv.le)
    (cE.intervalIntegrable_of_Icc huv.le)] at heq
  have hra := (hS.axis v ⟨hu.trans huv.le, le_rfl, hvT⟩).1
  change (∫ s in u..v, F s) + (∫ s in u..v, E s) =
    (S.r v v : ℂ) * starRingEnd ℂ (curv S v v) -
      (S.r u v : ℂ) * starRingEnd ℂ (curv S u v) at heq
  rw [hra, ofReal_zero, zero_mul, zero_sub] at heq
  have hr : (S.r u v : ℂ) ≠ 0 := by
    exact_mod_cast (hS.r_pos (u, v) ⟨hu, huv.le, hvT⟩ huv).ne'
  calc
    starRingEnd ℂ (curv S u v) =
        -((S.r u v : ℂ)⁻¹ * (-((S.r u v : ℂ) * starRingEnd ℂ (curv S u v)))) := by
      rw [mul_neg, neg_neg, ← mul_assoc, inv_mul_cancel₀ hr, one_mul]
    _ = -((S.r u v : ℂ)⁻¹ * ((∫ s in u..v, F s) + ∫ s in u..v, E s)) := by rw [heq]
    _ = _ := by rw [mul_add, neg_add]

end EmcsfAcExtension.Local
