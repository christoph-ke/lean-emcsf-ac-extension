module

public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Defs.Domains
public import EmcsfAcExtension.Global.Defs.Curves
public import EmcsfAcExtension.Global.Defs.Renormalized
public import EmcsfAcExtension.Global.Defs.Interaction
public import EmcsfAcExtension.Global.Defs.Stages
public import EmcsfAcExtension.Global.Defs.Relabel
public import EmcsfAcExtension.Global.Defs.Observation
public import EmcsfAcExtension.Local.Defs.Params
import EmcsfAcExtension.Infra.AC.Relabel

/-! # Characterizations of the Root A definitions

The frozen objects retain their source meanings. Coordinate and gauge identities are
proved for each equation right side; derivative rules state their regularity inputs.
No frozen theorem anchor or provider is imported.
-/

public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global

/-- [def-node eq:ct-j]
[def-node sec:charged-step7#exterior-interaction-variable]
The frozen derivative is the source's normalized formula (charged_SF_new_version.tex:L1427–L1435,
L3131–L3136). -/
theorem jOut_eq (S : Fields) (u v : ℝ) (hlam : S.lam u v ≠ 0) :
    jOut S u v = (1 - S.mu u v) * S.lam u v *
      (alphaPrime S u v - (1 / S.r u v : ℝ) *
        ‖S.theta u v / S.lam u v‖ ^ 2 * (S.theta u v / S.lam u v)) := by
  have hc : (S.lam u v : ℂ) ≠ 0 := by exact_mod_cast hlam
  unfold jOut alphaPrime
  push_cast
  field_simp

/-- [def-node eq:ct-C]
The shared complex curvature is the product of normalized ratios
(charged_SF_new_version.tex:L3137–L3145), including at zero denominators. -/
theorem curv_eq (S : Fields) (u v : ℝ) :
    Local.curv S u v = S.mu u v + (1 - S.mu u v) *
      (S.theta u v / S.lam u v) * starRingEnd ℂ (S.xi u v / S.nu u v) := by
  simp [Local.curv, map_div₀, div_mul_div_comm, mul_div_assoc, mul_assoc]

/-- [def-node eq:ct-Ej]
The shared electromagnetic remainder uses the frozen Maxwell right side
(charged_SF_new_version.tex:L3176–L3184). -/
theorem emSourceJ_eq (e : ℝ) (S : Fields) (u v : ℝ) :
    Local.emSourceJ e S u v =
      (-S.nu u v) * S.lam u v / S.r u v ^ 2 *
        (5 * (S.Q u v ^ 2 / S.r u v ^ 2) * (S.theta u v / S.lam u v) +
          I * e * S.Q u v * (3 * (S.theta u v / S.lam u v) + S.phi u v)) +
      I * e * (-S.nu u v) / S.r u v * S.QV e u v * S.phi u v := by
  unfold Local.emSourceJ
  ring

/-- [def-node eq:ct-zeta]
[def-node eq:co-eta]
The shared charged scale at label length `2R` (charged_SF_new_version.tex:L1977–L1979,
L3362–L3365). -/
theorem sigma_two_mul (e M R : ℝ) : Local.sigma e M (2 * R) = e ^ 2 * M ^ 2 * R ^ 2 := by
  simp [Local.sigma]

/-- [internal]
The curve representative on an incoming segment is the frozen parallel representative
(charged_SF_new_version.tex:L882–L882). -/
theorem curveParallel_in (e : ℝ) (S : Fields) (f : ℝ → ℝ → ℂ) (s x v : ℝ) :
    curveParallel e S f id (fun _ => v) s x =
      Complex.exp (I * e * ∫ y in s..x, S.A y v) * f x v := by
  simp [curveParallel]

/-- [def-node sec:charged-equations#covariant-variation]
Incoming curve variation is exactly frozen `covVarIn` (charged_SF_new_version.tex:L882–L882). -/
theorem curveCovVar_in (e : ℝ) (S : Fields) (f : ℝ → ℝ → ℂ) (s t v : ℝ) :
    curveCovVar e S f id (fun _ => v) s t = covVarIn e S.A f s t v := by
  unfold curveCovVar covVarIn
  congr 1
  funext x
  exact curveParallel_in e S f s x v

private theorem inv_lipschitz {d : ℝ} (hd : 0 < d) :
    LipschitzOnWith (Real.toNNReal (d⁻¹ ^ 2)) (Inv.inv : ℝ → ℝ) (Ici d) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  have hx0 : 0 < x := lt_of_lt_of_le hd hx
  have hy0 : 0 < y := lt_of_lt_of_le hd hy
  calc
    dist x⁻¹ y⁻¹ = dist x y / (x * y) := by
      simpa [Real.norm_eq_abs, abs_of_pos hx0, abs_of_pos hy0] using
        (dist_inv_inv₀ (ne_of_gt hx0) (ne_of_gt hy0))
    _ ≤ dist x y / (d * d) :=
      div_le_div_of_nonneg_left dist_nonneg (mul_pos hd hd)
        (mul_le_mul hx hy (le_of_lt hd) (le_of_lt hx0))
    _ = _ := by
      change dist x y / (d * d) = max (d⁻¹ ^ 2) 0 * dist x y
      rw [max_eq_left (sq_nonneg _)]
      simp only [div_eq_mul_inv, mul_inv_rev, pow_two]
      ring

/-- [internal]
The derivative of the inverse null label is the reciprocal derivative at its preimage
(charged_SF_new_version.tex:L4137–L4161 and L4189–L4193). -/
theorem IsNullRelabel.deriv_symm {F : ℝ ≃o ℝ} (hF : IsNullRelabel F) (x : ℝ) :
    deriv (F.symm : ℝ → ℝ) x = (deriv (F : ℝ → ℝ) (F.symm x))⁻¹ := by
  exact ((hF.1.differentiable (by norm_num) (F.symm x)).hasDerivAt.of_local_left_inverse
    F.symm.continuous.continuousAt (ne_of_gt (hF.2.1 _))
      (Filter.Eventually.of_forall F.apply_symm_apply)).deriv

/-- [internal]
Increasing C¹ null labels with positive locally BV derivative are closed under inversion
(charged_SF_new_version.tex:L4137–L4161 and L4189–L4193; internal project record N2). -/
theorem IsNullRelabel.symm {F : ℝ ≃o ℝ} (hF : IsNullRelabel F) : IsNullRelabel F.symm := by
  refine ⟨F.toHomeomorph.contDiff_symm_deriv (fun x => ne_of_gt (hF.2.1 x))
    (fun x => (hF.1.differentiable (by norm_num) x).hasDerivAt) hF.1, ?_, ?_⟩
  · intro x
    rw [hF.deriv_symm]
    exact inv_pos.mpr (hF.2.1 _)
  · intro a b
    by_cases hab : a ≤ b
    · have hc : Continuous (fun x => deriv (F : ℝ → ℝ) (F.symm x)) :=
        hF.1.continuous_deriv_one.comp F.symm.continuous
      obtain ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hc.continuousOn
      have hvar : BoundedVariationOn (fun x => deriv (F : ℝ → ℝ) (F.symm x)) (Icc a b) := by
        rw [BoundedVariationOn, ← Function.comp_def,
          eVariationOn.comp_Icc_eq_of_monotoneOn _ (F.symm.monotone.monotoneOn _)
            (F.symm.image_Icc a b)]
        exact ne_of_lt (hF.2.2 _ _)
      have hb := (inv_lipschitz (hF.2.1 (F.symm x))).comp_boundedVariationOn
        (fun y hy => hmin hy) hvar
      have heq : deriv (F.symm : ℝ → ℝ) =
          Inv.inv ∘ (fun x => deriv (F : ℝ → ℝ) (F.symm x)) :=
        funext hF.deriv_symm
      rw [heq]
      exact lt_top_iff_ne_top.mpr hb
    · simp [Icc_eq_empty hab]

private theorem mass_jacobian_algebra (c mu q r l : ℝ) (z : ℂ) (hc : c ≠ 0) :
    (1 - mu) * ‖(c : ℂ) * z‖ ^ 2 / (2 * (c * l)) + q ^ 2 * (c * l) / (2 * r ^ 2) =
      c * ((1 - mu) * ‖z‖ ^ 2 / (2 * l) + q ^ 2 * l / (2 * r ^ 2)) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  simp only [div_eq_mul_inv, mul_inv_rev]
  field_simp

/-- [internal]
The mass ratio is a scalar under null relabeling (charged_SF_new_version.tex:L3954–L4161). -/
theorem nullPullback_mu (S : Fields) (U V : ℝ → ℝ) (u v : ℝ) :
    (nullPullback S U V).mu u v = S.mu (U u) (V v) := rfl

/-- [internal]
All nonlinear frozen equation right sides under null relabeling
(charged_SF_new_version.tex:L3954–L4161, L4189–L4193). The radius equations are the defining
`lam` and `nu` fields. These identities use the actual pointwise label derivatives. -/
theorem nullPullback_rhs (S : Fields) (U V : ℝ → ℝ) (e u v du dv : ℝ)
    (hU : HasDerivAt U du u) (hV : HasDerivAt V dv v) (hdu : 0 < du) (hdv : 0 < dv) :
    (nullPullback S U V).rUV u v = du * dv * S.rUV (U u) (V v) ∧
    (nullPullback S U V).mV u v = dv * S.mV (U u) (V v) ∧
    (nullPullback S U V).mU u v = du * S.mU (U u) (V v) ∧
    (nullPullback S U V).QV e u v = dv * S.QV e (U u) (V v) ∧
    (nullPullback S U V).QU e u v = du * S.QU e (U u) (V v) ∧
    (nullPullback S U V).AV u v = du * dv * S.AV (U u) (V v) ∧
    (nullPullback S U V).phiV u v = dv * S.phiV (U u) (V v) ∧
    (nullPullback S U V).phiU e u v = du * S.phiU e (U u) (V v) ∧
    (nullPullback S U V).xiV e u v = du * dv * S.xiV e (U u) (V v) ∧
    (nullPullback S U V).thetaU e u v = du * dv * S.thetaU e (U u) (V v) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Fields.rUV, Fields.mu, nullPullback, hU.deriv, hV.deriv]; ring
  · simpa only [Fields.mV, Fields.mu, nullPullback, hV.deriv] using
      mass_jacobian_algebra dv (S.mu (U u) (V v)) (S.Q (U u) (V v))
        (S.r (U u) (V v)) (S.lam (U u) (V v)) (S.theta (U u) (V v)) (ne_of_gt hdv)
  · simpa only [Fields.mU, Fields.mu, nullPullback, hU.deriv] using
      mass_jacobian_algebra du (S.mu (U u) (V v)) (S.Q (U u) (V v))
        (S.r (U u) (V v)) (S.nu (U u) (V v)) (S.xi (U u) (V v)) (ne_of_gt hdu)
  · simp only [Fields.QV, nullPullback, hV.deriv]
    simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
  · simp only [Fields.QU, nullPullback, hU.deriv]
    simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
  · simp only [Fields.AV, Fields.mu, nullPullback, hU.deriv, hV.deriv]; ring
  · simp only [Fields.phiV, nullPullback, hV.deriv]; ring
  · simp only [Fields.phiU, nullPullback, hU.deriv]; push_cast; ring
  · simp only [Fields.xiV, Fields.waveSource, Fields.mu, nullPullback, hU.deriv, hV.deriv]
    push_cast; ring
  · simp only [Fields.thetaU, Fields.waveSource, Fields.mu, nullPullback, hU.deriv, hV.deriv]
    push_cast; ring

/-- [internal]
Rescaling preserves the mass ratio (charged_SF_new_version.tex:L1964–L1988). -/
theorem rescaleFields_mu (S : Fields) (a u v : ℝ) (ha : 0 < a) :
    (rescaleFields S a).mu u v = S.mu (a * u) (a * v) := by
  dsimp [rescaleFields, Fields.mu]
  have ha0 := ne_of_gt ha
  field_simp

/-- [internal]
All nonlinear frozen equation right sides under length rescaling, with coupling `a*e`
(charged_SF_new_version.tex:L1964–L1988). The equations are evaluated on the pulled-back domain
`{p | (a*p.1, a*p.2) ∈ D}` whenever the original equations hold on `D`. -/
theorem rescaleFields_rhs (S : Fields) (a e u v : ℝ) (ha : 0 < a) :
    (rescaleFields S a).rUV u v = a * S.rUV (a * u) (a * v) ∧
    (rescaleFields S a).mV u v = S.mV (a * u) (a * v) ∧
    (rescaleFields S a).mU u v = S.mU (a * u) (a * v) ∧
    (rescaleFields S a).QV (a * e) u v = S.QV e (a * u) (a * v) ∧
    (rescaleFields S a).QU (a * e) u v = S.QU e (a * u) (a * v) ∧
    (rescaleFields S a).AV u v = a * S.AV (a * u) (a * v) ∧
    (rescaleFields S a).phiV u v = a * S.phiV (a * u) (a * v) ∧
    (rescaleFields S a).phiU (a * e) u v = a * S.phiU e (a * u) (a * v) ∧
    (rescaleFields S a).xiV (a * e) u v = a * S.xiV e (a * u) (a * v) ∧
    (rescaleFields S a).thetaU (a * e) u v = a * S.thetaU e (a * u) (a * v) := by
  have ha0 := ne_of_gt ha
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Fields.rUV, Fields.mu, rescaleFields]
    field_simp
  · simp only [Fields.mV, Fields.mu, rescaleFields]
    field_simp
  · simp only [Fields.mU, Fields.mu, rescaleFields]
    field_simp
  · simp only [Fields.QV, rescaleFields]; field_simp
  · simp only [Fields.QU, rescaleFields]; field_simp
  · simp only [Fields.AV, Fields.mu, rescaleFields]
    field_simp
  · simp only [Fields.phiV, rescaleFields]; push_cast; field_simp
  · simp only [Fields.phiU, rescaleFields]; push_cast; field_simp
  · simp only [Fields.xiV, Fields.waveSource, Fields.mu, rescaleFields]
    push_cast; field_simp
  · simp only [Fields.thetaU, Fields.waveSource, Fields.mu, rescaleFields]
    push_cast; field_simp

private theorem unit_gauge_product (g z w : ℂ) (hg : ‖g‖ = 1) :
    starRingEnd ℂ (g * z) * (g * w) = starRingEnd ℂ z * w := by
  have hgg : starRingEnd ℂ g * g = 1 := by rw [Complex.conj_mul', hg]; norm_num
  rw [map_mul]
  calc
    _ = (starRingEnd ℂ g * g) * (starRingEnd ℂ z * w) := by ring
    _ = _ := by rw [hgg, one_mul]

/-- [internal]
The mass ratio is gauge invariant (charged_SF_new_version.tex:L692–L699). -/
theorem gaugeFields_mu (e : ℝ) (S : Fields) (χ : ℝ → ℝ) (u v : ℝ) :
    (gaugeFields e S χ).mu u v = S.mu u v := rfl

/-- [internal]
All nonlinear frozen equation right sides under the residual incoming gauge
(charged_SF_new_version.tex:L692–L699, L1957–L1963). The two incoming complex equations include
exactly the derivative of the phase. No regular-axis gauge condition is asserted. -/
theorem gaugeFields_rhs (e : ℝ) (S : Fields) (χ : ℝ → ℝ) (u v d : ℝ)
    (hχ : HasDerivAt χ d u) :
    let g := Complex.exp (I * e * χ u)
    (gaugeFields e S χ).rUV u v = S.rUV u v ∧
    (gaugeFields e S χ).mV u v = S.mV u v ∧
    (gaugeFields e S χ).mU u v = S.mU u v ∧
    (gaugeFields e S χ).QV e u v = S.QV e u v ∧
    (gaugeFields e S χ).QU e u v = S.QU e u v ∧
    (gaugeFields e S χ).AV u v = S.AV u v ∧
    (gaugeFields e S χ).phiV u v = g * S.phiV u v ∧
    (gaugeFields e S χ).phiU e u v = g * S.phiU e u v + I * e * d * g * S.phi u v ∧
    (gaugeFields e S χ).xiV e u v = g * S.xiV e u v ∧
    (gaugeFields e S χ).thetaU e u v = g * S.thetaU e u v + I * e * d * g * S.theta u v := by
  have hg : ‖Complex.exp (I * e * χ u)‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  refine ⟨rfl, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · simp [Fields.mV, Fields.mu, gaugeFields, hg]
  · simp [Fields.mU, Fields.mu, gaugeFields, hg]
  · simp only [Fields.QV, gaugeFields, unit_gauge_product _ _ _ hg]
  · simp only [Fields.QU, gaugeFields, unit_gauge_product _ _ _ hg]
  · simp only [Fields.phiV, gaugeFields]; ring
  · simp only [Fields.phiU, gaugeFields, hχ.deriv]; push_cast; ring
  · simp only [Fields.xiV, Fields.waveSource, Fields.mu, gaugeFields]; ring
  · simp only [Fields.thetaU, Fields.waveSource, Fields.mu, gaugeFields, hχ.deriv]
    push_cast; ring

/-- [internal]
The thirteen frozen differential equations pull back under differentiable positive
null labels (charged_SF_new_version.tex:L3954–L4161, L4189–L4193). The assumptions are the
original equations at the image point, without any C² assumption on the labels. -/
theorem nullPullback_equations (S : Fields) (U V : ℝ → ℝ) (e u v du dv : ℝ)
    (hU : HasDerivAt U du u) (hV : HasDerivAt V dv v) (hdu : 0 < du) (hdv : 0 < dv)
    (hout : HasDerivAt (S.r (U u)) (S.lam (U u) (V v)) (V v) ∧
      HasDerivAt (S.nu (U u)) (S.rUV (U u) (V v)) (V v) ∧
      HasDerivAt (S.m (U u)) (S.mV (U u) (V v)) (V v) ∧
      HasDerivAt (S.Q (U u)) (S.QV e (U u) (V v)) (V v) ∧
      HasDerivAt (S.A (U u)) (S.AV (U u) (V v)) (V v) ∧
      HasDerivAt (S.phi (U u)) (S.phiV (U u) (V v)) (V v) ∧
      HasDerivAt (S.xi (U u)) (S.xiV e (U u) (V v)) (V v))
    (hin : HasDerivAt (fun x => S.r x (V v)) (S.nu (U u) (V v)) (U u) ∧
      HasDerivAt (fun x => S.lam x (V v)) (S.rUV (U u) (V v)) (U u) ∧
      HasDerivAt (fun x => S.m x (V v)) (S.mU (U u) (V v)) (U u) ∧
      HasDerivAt (fun x => S.Q x (V v)) (S.QU e (U u) (V v)) (U u) ∧
      HasDerivAt (fun x => S.phi x (V v)) (S.phiU e (U u) (V v)) (U u) ∧
      HasDerivAt (fun x => S.theta x (V v)) (S.thetaU e (U u) (V v)) (U u)) :
    let P := nullPullback S U V
    (HasDerivAt (P.r u) (P.lam u v) v ∧ HasDerivAt (P.nu u) (P.rUV u v) v ∧
      HasDerivAt (P.m u) (P.mV u v) v ∧ HasDerivAt (P.Q u) (P.QV e u v) v ∧
      HasDerivAt (P.A u) (P.AV u v) v ∧ HasDerivAt (P.phi u) (P.phiV u v) v ∧
      HasDerivAt (P.xi u) (P.xiV e u v) v) ∧
    (HasDerivAt (fun x => P.r x v) (P.nu u v) u ∧
      HasDerivAt (fun x => P.lam x v) (P.rUV u v) u ∧
      HasDerivAt (fun x => P.m x v) (P.mU u v) u ∧
      HasDerivAt (fun x => P.Q x v) (P.QU e u v) u ∧
      HasDerivAt (fun x => P.phi x v) (P.phiU e u v) u ∧
      HasDerivAt (fun x => P.theta x v) (P.thetaU e u v) u) := by
  rcases hout with ⟨hrv, hnuv, hmv, hQv, hAv, hphiv, hxiv⟩
  rcases hin with ⟨hru, hlamu, hmu, hQu, hphiu, hthetau⟩
  rcases nullPullback_rhs S U V e u v du dv hU hV hdu hdv with
    ⟨k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈, k₉, k₁₀⟩
  dsimp only
  rw [k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈, k₉, k₁₀]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  all_goals simp only [nullPullback, hU.deriv, hV.deriv]
  · simpa only [Function.comp_def, Complex.real_smul, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using hrv.comp v hV
  · simpa only [Function.comp_def, Complex.real_smul, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using (hnuv.comp v hV).const_mul du
  · simpa only [Function.comp_def, Complex.real_smul, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using hmv.comp v hV
  · simpa only [Function.comp_def, Complex.real_smul, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using hQv.comp v hV
  · simpa only [Function.comp_def, Complex.real_smul, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using (hAv.comp v hV).const_mul du
  · simpa only [Function.comp_def, Complex.real_smul, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using hphiv.scomp v hV
  · simpa only [Function.comp_def, Complex.real_smul, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using (hxiv.scomp v hV).const_mul (du : ℂ)
  · simpa only [Function.comp_def, Complex.real_smul, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using hru.comp u hU
  · simpa only [Function.comp_def, Complex.real_smul, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using (hlamu.comp u hU).const_mul dv
  · simpa only [Function.comp_def, Complex.real_smul, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using hmu.comp u hU
  · simpa only [Function.comp_def, Complex.real_smul, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using hQu.comp u hU
  · simpa only [Function.comp_def, Complex.real_smul, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using hphiu.scomp u hU
  · simpa only [Function.comp_def, Complex.real_smul, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using (hthetau.scomp u hU).const_mul (dv : ℂ)

/-- [internal]
All thirteen equations rescale on the exact inverse-image domain, with coupling `a*e`
(charged_SF_new_version.tex:L1964–L1988). No assertion about an axis in the normalized chart is
made. -/
theorem rescaleFields_equations (S : Fields) (D : Set (ℝ × ℝ)) (a e : ℝ) (ha : 0 < a)
    (hout : ∀ p ∈ D, HasDerivAt (S.r p.1) (S.lam p.1 p.2) p.2 ∧
      HasDerivAt (S.nu p.1) (S.rUV p.1 p.2) p.2 ∧
      HasDerivAt (S.m p.1) (S.mV p.1 p.2) p.2 ∧
      HasDerivAt (S.Q p.1) (S.QV e p.1 p.2) p.2 ∧
      HasDerivAt (S.A p.1) (S.AV p.1 p.2) p.2 ∧
      HasDerivAt (S.phi p.1) (S.phiV p.1 p.2) p.2 ∧
      HasDerivAt (S.xi p.1) (S.xiV e p.1 p.2) p.2)
    (hin : ∀ p ∈ D, HasDerivAt (fun x => S.r x p.2) (S.nu p.1 p.2) p.1 ∧
      HasDerivAt (fun x => S.lam x p.2) (S.rUV p.1 p.2) p.1 ∧
      HasDerivAt (fun x => S.m x p.2) (S.mU p.1 p.2) p.1 ∧
      HasDerivAt (fun x => S.Q x p.2) (S.QU e p.1 p.2) p.1 ∧
      HasDerivAt (fun x => S.phi x p.2) (S.phiU e p.1 p.2) p.1 ∧
      HasDerivAt (fun x => S.theta x p.2) (S.thetaU e p.1 p.2) p.1) :
    ∀ p ∈ {p : ℝ × ℝ | (a * p.1, a * p.2) ∈ D}, let P := rescaleFields S a
    (HasDerivAt (P.r p.1) (P.lam p.1 p.2) p.2 ∧
      HasDerivAt (P.nu p.1) (P.rUV p.1 p.2) p.2 ∧
      HasDerivAt (P.m p.1) (P.mV p.1 p.2) p.2 ∧
      HasDerivAt (P.Q p.1) (P.QV (a * e) p.1 p.2) p.2 ∧
      HasDerivAt (P.A p.1) (P.AV p.1 p.2) p.2 ∧
      HasDerivAt (P.phi p.1) (P.phiV p.1 p.2) p.2 ∧
      HasDerivAt (P.xi p.1) (P.xiV (a * e) p.1 p.2) p.2) ∧
    (HasDerivAt (fun x => P.r x p.2) (P.nu p.1 p.2) p.1 ∧
      HasDerivAt (fun x => P.lam x p.2) (P.rUV p.1 p.2) p.1 ∧
      HasDerivAt (fun x => P.m x p.2) (P.mU p.1 p.2) p.1 ∧
      HasDerivAt (fun x => P.Q x p.2) (P.QU (a * e) p.1 p.2) p.1 ∧
      HasDerivAt (fun x => P.phi x p.2) (P.phiU (a * e) p.1 p.2) p.1 ∧
      HasDerivAt (fun x => P.theta x p.2) (P.thetaU (a * e) p.1 p.2) p.1) := by
  rintro ⟨u, v⟩ hp
  rcases hout (a * u, a * v) hp with ⟨hrv, hnuv, hmv, hQv, hAv, hphiv, hxiv⟩
  rcases hin (a * u, a * v) hp with ⟨hru, hlamu, hmu, hQu, hphiu, hthetau⟩
  have hlin (x : ℝ) : HasDerivAt (fun t => a * t) a x := by
    simpa using (hasDerivAt_id x).const_mul a
  rcases rescaleFields_rhs S a e u v ha with ⟨k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈, k₉, k₁₀⟩
  dsimp only
  rw [k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈, k₉, k₁₀]
  have ha0 := ne_of_gt ha
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  all_goals simp only [rescaleFields]
  · simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc, ha0] using!
      (hrv.comp v (hlin v)).div_const a
  · simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc, ha0] using!
      hnuv.comp v (hlin v)
  · simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc, ha0] using!
      (hmv.comp v (hlin v)).div_const a
  · simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc, ha0] using!
      (hQv.comp v (hlin v)).div_const a
  · simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc, ha0] using!
      hAv.comp v (hlin v)
  · simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc, ha0] using!
      hphiv.scomp v (hlin v)
  · simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc, ha0] using!
      hxiv.scomp v (hlin v)
  · simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc, ha0] using!
      (hru.comp u (hlin u)).div_const a
  · simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc, ha0] using!
      hlamu.comp u (hlin u)
  · simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc, ha0] using!
      (hmu.comp u (hlin u)).div_const a
  · simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc, ha0] using!
      (hQu.comp u (hlin u)).div_const a
  · simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc, ha0] using!
      hphiu.scomp u (hlin u)
  · simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc, ha0] using!
      hthetau.scomp u (hlin u)

/-- [internal]
The thirteen frozen equations in the residual incoming gauge
(charged_SF_new_version.tex:L692–L699, L1957–L1963). Only one derivative of `χ` is needed. -/
theorem gaugeFields_equations (e : ℝ) (S : Fields) (χ : ℝ → ℝ) (u v d : ℝ)
    (hχ : HasDerivAt χ d u)
    (hout : HasDerivAt (S.r u) (S.lam u v) v ∧ HasDerivAt (S.nu u) (S.rUV u v) v ∧
      HasDerivAt (S.m u) (S.mV u v) v ∧ HasDerivAt (S.Q u) (S.QV e u v) v ∧
      HasDerivAt (S.A u) (S.AV u v) v ∧ HasDerivAt (S.phi u) (S.phiV u v) v ∧
      HasDerivAt (S.xi u) (S.xiV e u v) v)
    (hin : HasDerivAt (fun x => S.r x v) (S.nu u v) u ∧
      HasDerivAt (fun x => S.lam x v) (S.rUV u v) u ∧
      HasDerivAt (fun x => S.m x v) (S.mU u v) u ∧
      HasDerivAt (fun x => S.Q x v) (S.QU e u v) u ∧
      HasDerivAt (fun x => S.phi x v) (S.phiU e u v) u ∧
      HasDerivAt (fun x => S.theta x v) (S.thetaU e u v) u) :
    let P := gaugeFields e S χ
    (HasDerivAt (P.r u) (P.lam u v) v ∧ HasDerivAt (P.nu u) (P.rUV u v) v ∧
      HasDerivAt (P.m u) (P.mV u v) v ∧ HasDerivAt (P.Q u) (P.QV e u v) v ∧
      HasDerivAt (P.A u) (P.AV u v) v ∧ HasDerivAt (P.phi u) (P.phiV u v) v ∧
      HasDerivAt (P.xi u) (P.xiV e u v) v) ∧
    (HasDerivAt (fun x => P.r x v) (P.nu u v) u ∧
      HasDerivAt (fun x => P.lam x v) (P.rUV u v) u ∧
      HasDerivAt (fun x => P.m x v) (P.mU u v) u ∧
      HasDerivAt (fun x => P.Q x v) (P.QU e u v) u ∧
      HasDerivAt (fun x => P.phi x v) (P.phiU e u v) u ∧
      HasDerivAt (fun x => P.theta x v) (P.thetaU e u v) u) := by
  rcases hout with ⟨hrv, hnuv, hmv, hQv, hAv, hphiv, hxiv⟩
  rcases hin with ⟨hru, hlamu, hmu, hQu, hphiu, hthetau⟩
  have hphase : HasDerivAt (fun x => Complex.exp (I * e * χ x))
      (I * e * d * Complex.exp (I * e * χ u)) u := by
    convert (hχ.ofReal_comp.const_mul (I * e)).cexp using 1
    ring
  rcases gaugeFields_rhs e S χ u v d hχ with ⟨k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈, k₉, k₁₀⟩
  dsimp only
  rw [k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈, k₉, k₁₀]
  refine ⟨⟨hrv, hnuv, hmv, hQv, ?_, ?_, ?_⟩,
    ⟨hru, hlamu, hmu, hQu, ?_, ?_⟩⟩
  · simpa only [gaugeFields, sub_zero] using hAv.sub_const (deriv χ u)
  · exact hphiv.const_mul _
  · exact hxiv.const_mul _
  · simpa only [gaugeFields, Pi.mul_def, add_comm, mul_comm, mul_left_comm, mul_assoc] using!
      hphase.mul hphiu
  · simpa only [gaugeFields, Pi.mul_def, add_comm, mul_comm, mul_left_comm, mul_assoc] using!
      hphase.mul hthetau

end EmcsfAcExtension.Global
