module

public import EmcsfAcExtension.Global.Observation.CylinderIdentity
public import EmcsfAcExtension.Global.Defs.Observation
import EmcsfAcExtension.Global.Calculus.CurveTrace
import EmcsfAcExtension.Infra.AC.Variation
import EmcsfAcExtension.Infra.AC.Quotient
import EmcsfAcExtension.Infra.Null.IntegralForm

/-! # Exact cylinder energy and covariant variation

The connection is represented by the specified unit complex parallel factor.
The derivative of a squared modulus has no connection contribution. These
calculations use the original AC class and its actual boundary clock.
Source: `charged_SF_new_version.tex:L1880`–`L1901` and approved internal project record. The energy
and
variation identities use the internal project record timelike chain rule to derive covariant
AC of the boundary normalized scalar from the frozen solution class.
-/

public section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal ComplexConjugate

namespace EmcsfAcExtension.Global

namespace Cylinder

/-- [node sec:charged-observation#cylinder-energy]
The specified cylinder energy is the source expression. It contains no
additional electric term and is distinct from electric charge. -/
theorem cylinder_energy (S : Fields) (b u v : ℝ) :
    cylinderEnergy S b u v = b / 2 *
      (‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 - Real.log (1 - S.mu u v)) := rfl

/-- [internal] Parallel transport preserves the modulus at every point,
independently of any differentiability or integrability assumption. -/
theorem norm_curveParallel (e : ℝ) (S : Fields) (f : ℝ → ℝ → ℂ)
    (U V : ℝ → ℝ) (s x : ℝ) :
    ‖curveParallel e S f U V s x‖ = ‖f (U x) (V x)‖ := by
  simp [curveParallel, Complex.norm_exp, Complex.mul_re]

private theorem phase_ac {q : ℝ → ℝ} {s t : ℝ} (e : ℝ)
    (hq : IntervalIntegrable q volume s t) :
    AbsolutelyContinuousOnInterval
      (fun x => Complex.exp (I * e * ∫ y in s..x, q y)) s t := by
  have h := ((hq.absolutelyContinuousOnInterval_intervalIntegral_normed
    left_mem_uIcc).const_mul e).unit_phase
  simpa only [Complex.ofReal_mul, mul_assoc] using h

/-- [internal] Covariant AC and ordinary AC on a curve are equivalent when
the pulled-back potential is integrable. No stronger derivative trace is
assumed. -/
theorem curveParallel_ac_iff {e : ℝ} {S : Fields} {f : ℝ → ℝ → ℂ}
    {U V : ℝ → ℝ} {s t : ℝ}
    (hq : IntervalIntegrable (fun x => S.A (U x) (V x) * deriv U x) volume s t) :
    AbsolutelyContinuousOnInterval (curveParallel e S f U V s) s t ↔
      AbsolutelyContinuousOnInterval (fun x => f (U x) (V x)) s t := by
  constructor
  · intro hf
    apply ((phase_ac (-e) hq).mul_normed_ring hf).congr
    intro x hx
    simp only [curveParallel, ← mul_assoc, ← Complex.exp_add, Complex.ofReal_neg]
    have he : I * -(e : ℂ) * (∫ y in s..x, S.A (U y) (V y) * deriv U y : ℝ) +
        I * e * (∫ y in s..x, S.A (U y) (V y) * deriv U y : ℝ) = 0 := by ring
    rw [he, Complex.exp_zero, one_mul]
  · exact fun hf => (phase_ac e hq).mul_normed_ring hf

/-- [internal] The derivative of the specified parallel representative equals
the parallel factor times the covariant derivative, on a common clock null
set. The density may be merely integrable. -/
theorem ae_deriv_curveParallel {e : ℝ} {S : Fields} {f : ℝ → ℝ → ℂ}
    {U V : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hq : IntervalIntegrable (fun x => S.A (U x) (V x) * deriv U x) volume s t)
    (hf : AbsolutelyContinuousOnInterval (curveParallel e S f U V s) s t) :
    ∀ᵐ x ∂volume.restrict (Icc s t),
      deriv (curveParallel e S f U V s) x =
        Complex.exp (I * e * ∫ y in s..x, S.A (U y) (V y) * deriv U y) *
          (deriv (fun x => f (U x) (V x)) x +
            I * e * S.A (U x) (V x) * deriv U x * f (U x) (V x)) := by
  have ha := (curveParallel_ac_iff hq).mp hf
  filter_upwards [ae_restrict_of_ae hq.ae_hasDerivAt_integral,
    ae_restrict_of_ae ha.ae_differentiableAt_of_mem_uIcc,
    ae_restrict_mem measurableSet_Icc] with x hx hfx hmem
  have hu : x ∈ uIcc s t := by rwa [uIcc_of_le hst]
  have hp := (((hx hu s left_mem_uIcc).ofReal_comp.const_mul (I * (e : ℂ))).cexp)
  have hd := hp.mul (hfx hu).hasDerivAt
  change deriv (fun x => Complex.exp (I * e * ∫ y in s..x,
    S.A (U y) (V y) * deriv U y) * f (U x) (V x)) x = _
  simp only [Pi.mul_def] at hd
  rw [hd.deriv]
  push_cast
  ring

/-- [internal] Covariant variation equals the integral of the covariant speed
on any curve with integrable pulled-back potential. Constants: none. -/
theorem curve_covariant_variation {e : ℝ} {S : Fields} {f : ℝ → ℝ → ℂ}
    {U V : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hq : IntervalIntegrable (fun x => S.A (U x) (V x) * deriv U x) volume s t)
    (hf : AbsolutelyContinuousOnInterval (curveParallel e S f U V s) s t) :
    curveCovVar e S f U V s t = ENNReal.ofReal
      (∫ x in s..t, ‖deriv (fun x => f (U x) (V x)) x +
        I * e * S.A (U x) (V x) * deriv U x * f (U x) (V x)‖) := by
  rw [curveCovVar, hf.eVariationOn_eq_integral_norm_deriv hst]
  congr 1
  apply intervalIntegral.integral_congr_ae
  have he := (ae_restrict_iff' measurableSet_Icc).mp (ae_deriv_curveParallel hst hq hf)
  filter_upwards [he] with x hx hmem
  rw [hx (by simpa only [uIcc_of_le hst] using uIoc_subset_uIcc hmem), norm_mul]
  have hp : ‖Complex.exp (I * e * ∫ y in s..x,
      S.A (U y) (V y) * deriv U y)‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re]
  rw [hp, one_mul]

/-- [internal] The pulled-back potential of a clock cylinder is integrable.
The pointwise `deriv U` at endpoints is immaterial: on the open interval
it is the continuous reciprocal clock density. -/
theorem intervalIntegrable_potential_clock {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    {b s t : ℝ} (hS : IsSolution e S D) (γ : ClockCylinder S D b s t) (hst : s ≤ t) :
    IntervalIntegrable (fun x => S.A (γ.U x) (γ.V x) * deriv γ.U x) volume s t := by
  have hc : ContinuousOn (fun x => S.A (γ.U x) (γ.V x) *
      (-S.nu (γ.U x) (γ.V x))⁻¹) (Icc s t) :=
    (γ.continuousOn_trace hS.cont_A).mul
      ((γ.continuousOn_trace hS.cont_nu).neg.inv₀
        (fun x hx => neg_ne_zero.mpr (hS.nu_neg _ (γ.mem x hx)).ne))
  have he : (fun x => S.A (γ.U x) (γ.V x) * (-S.nu (γ.U x) (γ.V x))⁻¹) =ᵐ[
      volume.restrict (Icc s t)] (fun x => S.A (γ.U x) (γ.V x) * deriv γ.U x) := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [(γ.hasDerivAt_U hx).deriv]
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hst).mpr
  exact ((intervalIntegrable_iff_integrableOn_Icc_of_le hst).mp
    (hc.intervalIntegrable_of_Icc hst)).congr he

/-- [internal] The normalized scalar has an ordinary AC cylinder trace.
The fixed-density timelike chain rule supplies AC from the frozen solution;
all four bi-Lipschitz constants are derived locally from the clock rates.
Constants: none in the conclusion; no uniform endpoint bound is required. -/
theorem ac_a {e ui b s t : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (γ : ClockCylinder S (origDomain ui) b s t)
    (hb : 0 < b) (hst : s ≤ t) :
    AbsolutelyContinuousOnInterval (fun x => S.a (γ.U x) (γ.V x)) s t := by
  rcases hst.eq_or_lt with rfl | hst
  · exact .refl _ _
  obtain ⟨KU, KV, LU, LV, hU, hV, hUa, hVa⟩ := γ.exists_biLipschitz_labels hS
  have hproper : ∀ x ∈ Icc s t, γ.U x < γ.V x := by
    intro x hx
    have hp := γ.mem x hx
    refine lt_of_le_of_ne hp.2.2.1 ?_
    intro heq
    have ha := (hS.axis (γ.U x) (by simpa only [← heq] using hp)).1
    have hr := γ.radius x hx
    rw [← heq, ha] at hr
    exact (ne_of_gt hb) hr.symm
  have hUa' : AntilipschitzWith LU ((uIcc s t).domRestrict γ.U) := by
    intro x y
    exact hUa ⟨x, by simpa only [uIcc_of_le hst.le] using x.property⟩
      ⟨y, by simpa only [uIcc_of_le hst.le] using y.property⟩
  have hVa' : AntilipschitzWith LV ((uIcc s t).domRestrict γ.V) := by
    intro x y
    exact hVa ⟨x, by simpa only [uIcc_of_le hst.le] using x.property⟩
      ⟨y, by simpa only [uIcc_of_le hst.le] using y.property⟩
  have hc := Calculus.timelike_ac_chain_rule hS (U := γ.U) (V := γ.V)
    (KU := KU) (KV := KV) hst
    (by simpa only [uIcc_of_le hst.le] using hU)
    (by simpa only [uIcc_of_le hst.le] using hV)
    (by simpa only [uIcc_of_le hst.le] using (γ.strictMonoOn_U hS).monotoneOn)
    (by simpa only [uIcc_of_le hst.le] using (γ.strictMonoOn_V hS).monotoneOn)
    hUa' hVa'
    (by simpa only [uIcc_of_le hst.le] using γ.mem)
    (by simpa only [uIcc_of_le hst.le] using hproper)
  exact hc.1

/-- [internal] The normalized scalar has the specified covariant AC trace on
every proper positive-radius cylinder of the frozen solution. The potential
is integrable by the clock rates; the ordinary AC trace comes from internal project record.
Constants: none; arbitrary coupling and data size. -/
theorem ac_curveParallel_a {e ui b s t : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (γ : ClockCylinder S (origDomain ui) b s t)
    (hb : 0 < b) (hst : s ≤ t) :
    AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V s) s t :=
  (curveParallel_ac_iff (intervalIntegrable_potential_clock hS γ hst)).mpr
    (ac_a hS γ hb hst)

/-- [internal]
Conditional representation for `sec:charged-observation#cylinder-covariant-variation`.
The boundary covariant variation of `α/λ` is exactly the integral of its
covariant speed (`charged_SF_new_version.tex:L1898`). Its value is finite by the AC
variation theorem. Constants: none. -/
theorem cylinder_covariant_variation_of_covariant_ac {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    {b s t : ℝ} (hS : IsSolution e S D) (γ : ClockCylinder S D b s t) (hst : s ≤ t)
    (hac : AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V s) s t) :
    curveCovVar e S S.a γ.U γ.V s t = ENNReal.ofReal
      (∫ x in s..t, ‖deriv (fun x => S.a (γ.U x) (γ.V x)) x +
        I * e * S.A (γ.U x) (γ.V x) * deriv γ.U x * S.a (γ.U x) (γ.V x)‖) :=
  curve_covariant_variation hst (intervalIntegrable_potential_clock hS γ hst) hac

/-- [node sec:charged-observation#cylinder-covariant-variation]
The cylinder variation of the normalized scalar equals the integral of its
covariant speed (`charged_SF_new_version.tex:L1898`–`L1901`). Its covariant AC trace is
derived from the frozen solution via internal project record. Constants: none. -/
theorem cylinder_covariant_variation {e ui b s t : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (γ : ClockCylinder S (origDomain ui) b s t)
    (hb : 0 < b) (hst : s ≤ t) :
    curveCovVar e S S.a γ.U γ.V s t = ENNReal.ofReal
      (∫ x in s..t, ‖deriv (fun x => S.a (γ.U x) (γ.V x)) x +
        I * e * S.A (γ.U x) (γ.V x) * deriv γ.U x * S.a (γ.U x) (γ.V x)‖) :=
  cylinder_covariant_variation_of_covariant_ac hS γ hst (ac_curveParallel_a hS γ hb hst)

private theorem energy_algebra {b μ μ' c : ℝ} {a φ a' φ' y z : ℂ}
    (hb : b ≠ 0) (hg : 1 - μ ≠ 0) (hy : y = a - φ)
    (hp : (b : ℂ) * (φ' + I * c * φ) = y - z)
    (hm : b * μ' = (1 - μ) * (‖y‖ ^ 2 - ‖z‖ ^ 2)) :
    b / 2 * (2 * (conj y * (a' - φ')).re + μ' / (1 - μ)) +
        1 / 2 * ‖y - z‖ ^ 2 = b * (conj y * (a' + I * c * a)).re := by
  have ha : a = y + φ := (sub_eq_iff_eq_add).mp hy.symm
  have hp' : φ' = (y - z) / (b : ℂ) - I * c * φ := by
    apply eq_sub_of_add_eq
    apply (eq_div_iff (Complex.ofReal_ne_zero.mpr hb)).mpr
    simpa only [mul_comm] using hp
  have hm' : μ' = (1 - μ) * (‖y‖ ^ 2 - ‖z‖ ^ 2) / b := by
    apply (eq_div_iff hb).mpr
    simpa only [mul_comm] using hm
  rw [hp', hm', ha]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im, Complex.div_ofReal_re, Complex.div_ofReal_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  field_simp [hb, hg]
  ring

/-- [internal] At each interior clock point where the boundary datum has an
ordinary derivative, its cylinder energy has the exact derivative. The a.e.
consumer below obtains this derivative from the covariant AC hypothesis. -/
theorem hasDerivAt_energy_of_deriv_a {e ui b s t τ : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (γ : ClockCylinder S (origDomain ui) b s t)
    (hb : 0 < b) (hτ : τ ∈ Ioo s t) {a' : ℂ}
    (ha : HasDerivAt (fun x => S.a (γ.U x) (γ.V x)) a' τ) :
    HasDerivAt (fun x => cylinderEnergy S b (γ.U x) (γ.V x))
      (b * (conj (S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)) *
          (a' + I * e * S.A (γ.U τ) (γ.V τ) * deriv γ.U τ * S.a (γ.U τ) (γ.V τ))).re -
        1 / 2 * ‖S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ) -
          S.xi (γ.U τ) (γ.V τ) / (S.nu (γ.U τ) (γ.V τ) : ℂ)‖ ^ 2) τ := by
  let y := S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)
  let z := S.xi (γ.U τ) (γ.V τ) / (S.nu (γ.U τ) (γ.V τ) : ℂ)
  let φ' := deriv (fun x => S.phi (γ.U x) (γ.V x)) τ
  let μ' := deriv (fun x => S.mu (γ.U x) (γ.V x)) τ
  have hφ : HasDerivAt (fun x => S.phi (γ.U x) (γ.V x)) φ' τ :=
    (hasDerivAt_phi hS γ hb hτ).differentiableAt.hasDerivAt
  have hμ : HasDerivAt (fun x => S.mu (γ.U x) (γ.V x)) μ' τ :=
    (hasDerivAt_mu_flux hS γ hb hτ).differentiableAt.hasDerivAt
  have hy : HasDerivAt (fun x => S.theta (γ.U x) (γ.V x) /
      (S.lam (γ.U x) (γ.V x) : ℂ)) (a' - φ') τ := by
    convert ha.sub hφ using 1
    funext x
    simp only [Pi.sub_apply, Fields.a, add_sub_cancel_left]
  have hsq : HasDerivAt (fun x => ‖S.theta (γ.U x) (γ.V x) /
      (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2) (2 * (conj y * (a' - φ')).re) τ := by
    simpa only [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply',
      RCLike.re_to_complex, y] using hy.norm_sq
  have hgap := (hS.one_sub_mu_pos _ (γ.mem τ (Ioo_subset_Icc_self hτ))).ne'
  have hlog := ((hasDerivAt_const τ (1 : ℝ)).sub hμ).log hgap
  have hd := (hsq.sub hlog).const_mul (b / 2)
  have hp : (b : ℂ) * (φ' + I * (e * S.A (γ.U τ) (γ.V τ) * deriv γ.U τ : ℝ) *
      S.phi (γ.U τ) (γ.V τ)) = y - z := by
    dsimp [φ']
    rw [(hasDerivAt_scalar_flux hS γ hb hτ).deriv, (γ.hasDerivAt_U hτ).deriv]
    push_cast
    dsimp [y, z]
    field_simp [Complex.ofReal_ne_zero.mpr hb.ne']
    ring
  have hm : b * μ' = (1 - S.mu (γ.U τ) (γ.V τ)) * (‖y‖ ^ 2 - ‖z‖ ^ 2) := by
    dsimp [μ']
    rw [(hasDerivAt_mu_flux hS γ hb hτ).deriv]
    exact mul_div_cancel₀ _ hb.ne'
  have he := energy_algebra (a' := a') hb.ne' hgap
    (show y = S.a (γ.U τ) (γ.V τ) - S.phi (γ.U τ) (γ.V τ) by
      simp only [Fields.a, add_sub_cancel_left, y]) hp hm
  simp only [Pi.sub_apply] at hd
  apply hd.congr_deriv
  simpa only [zero_sub, neg_div, sub_neg_eq_add, Complex.ofReal_mul, mul_assoc, y, z] using
    (eq_sub_of_add_eq he)


/-- [internal] The exact cylinder energy is AC on every proper closed clock
interval under precisely the covariant AC premise used in observation and
cooling. The compact lower gap bound is derived from the original class. -/
theorem ac_energy {e ui b s t : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (γ : ClockCylinder S (origDomain ui) b s t)
    (hb : 0 < b) (hst : s ≤ t)
    (hac : AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V s) s t) :
    AbsolutelyContinuousOnInterval (fun x => cylinderEnergy S b (γ.U x) (γ.V x)) s t := by
  have ha := (curveParallel_ac_iff (intervalIntegrable_potential_clock hS γ hst)).mp hac
  obtain ⟨hφ, hμ⟩ := ac_scalar_mu hS γ hb hst
  have hy : AbsolutelyContinuousOnInterval (fun x => S.theta (γ.U x) (γ.V x) /
      (S.lam (γ.U x) (γ.V x) : ℂ)) s t := (ha.sub hφ).congr (fun x _ => by
    simp only [Pi.sub_apply, Fields.a, add_sub_cancel_left])
  have hn := lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval hy
  have hg : ContinuousOn (fun x => 1 - S.mu (γ.U x) (γ.V x)) (Icc s t) :=
    continuousOn_const.sub (continuousOn_normalized_traces hS γ).2.2
  obtain ⟨c, hc, hcl⟩ := isCompact_Icc.exists_forall_le' hg
    (fun x hx => hS.one_sub_mu_pos _ (γ.mem x hx))
  have h1 : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) s t :=
    (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hl := (h1.sub hμ).log_of_pos_le hc (by simpa only [uIcc_of_le hst, Pi.sub_apply] using hcl)
  simpa only [cylinderEnergy, pow_two, Pi.mul_apply, Pi.sub_apply, Function.comp_def] using
    ((hn.mul hn).sub hl).const_mul (b / 2)

end Cylinder

/-- [internal]
Conditional proof of `eq:co-exact-energy`.
Exact charged cylinder energy balance (`charged_SF_new_version.tex:L1885`), a.e. in the
actual boundary clock, with covariant AC of `α/λ` supplied explicitly. The
unconditional theorem below discharges this premise using the internal project record
timelike chain rule. All scalar and mass chain rules are derived from the
frozen `IsSolution`. Constants: none; arbitrary coupling and data size. -/
theorem co_exact_energy_of_covariant_ac {e ui b s t : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (γ : ClockCylinder S (origDomain ui) b s t)
    (hb : 0 < b) (hst : s ≤ t)
    (hac : AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V s) s t) :
    ∀ᵐ τ ∂volume.restrict (Icc s t),
      deriv (fun x => cylinderEnergy S b (γ.U x) (γ.V x)) τ +
        1 / 2 * ‖S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ) -
          S.xi (γ.U τ) (γ.V τ) / (S.nu (γ.U τ) (γ.V τ) : ℂ)‖ ^ 2 =
        b * (conj (S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)) *
          (deriv (fun x => S.a (γ.U x) (γ.V x)) τ + I * e * S.A (γ.U τ) (γ.V τ) *
            deriv γ.U τ * S.a (γ.U τ) (γ.V τ))).re := by
  have ha := (Cylinder.curveParallel_ac_iff
    (Cylinder.intervalIntegrable_potential_clock hS γ hst)).mp hac
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [ae_restrict_of_ae ha.ae_differentiableAt_of_mem_uIcc,
    ae_restrict_mem measurableSet_Ioo] with τ hda hτ
  have hd := Cylinder.hasDerivAt_energy_of_deriv_a hS γ hb hτ
    (hda (by simpa only [uIcc_of_le hst] using Ioo_subset_Icc_self hτ)).hasDerivAt
  exact eq_sub_iff_add_eq.mp hd.deriv

/-- [node eq:co-exact-energy]
Exact charged cylinder energy balance (`charged_SF_new_version.tex:L1885`–`L1896`), a.e.
in the boundary clock. Covariant AC is derived from the frozen solution,
with no electric error. Constants: none; arbitrary coupling and data size. -/
theorem co_exact_energy {e ui b s t : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (γ : ClockCylinder S (origDomain ui) b s t)
    (hb : 0 < b) (hst : s ≤ t) :
    ∀ᵐ τ ∂volume.restrict (Icc s t),
      deriv (fun x => cylinderEnergy S b (γ.U x) (γ.V x)) τ +
        1 / 2 * ‖S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ) -
          S.xi (γ.U τ) (γ.V τ) / (S.nu (γ.U τ) (γ.V τ) : ℂ)‖ ^ 2 =
        b * (conj (S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)) *
          (deriv (fun x => S.a (γ.U x) (γ.V x)) τ + I * e * S.A (γ.U τ) (γ.V τ) *
            deriv γ.U τ * S.a (γ.U τ) (γ.V τ))).re :=
  co_exact_energy_of_covariant_ac hS γ hb hst (Cylinder.ac_curveParallel_a hS γ hb hst)

end EmcsfAcExtension.Global
