module

public import EmcsfAcExtension.Global.Api.Definitions
public import EmcsfAcExtension.Frozen.IntegralForm
import EmcsfAcExtension.Global.Observation.Scaling
import EmcsfAcExtension.Global.Observation.Gauge

/-! # Integral equations in the observation null chart

Increasing C¹ null maps transport the integral equations with their exact
Jacobians. The chart diagonal is not asserted to be a regular axis.
Source: charged_SF_new_version.tex:L1980–2021; internal project record (N).
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global

/-- [internal]
An integral equation transports through an increasing C¹ map. The source
density need only be integrable: the monotone substitution theorem supplies
both the new integrability and the exact signed integral identity. -/
theorem Observation.integralForm_comp_c1
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {U : ℝ → ℝ} {a b : ℝ}
    (hU : ContDiff ℝ 1 U) (hpos : ∀ x, 0 ≤ deriv U x)
    (h : IntegralForm f g (U a) (U b)) :
    IntegralForm (fun x => f (U x)) (fun x => deriv U x • g (U x)) a b := by
  have hc := contDiff_one_iff_deriv.mp hU
  have hd (x : ℝ) : HasDerivAt U (deriv U x) x := (hc.1 x).hasDerivAt
  have hi := (intervalIntegral.integrable_deriv_smul_comp_iff_of_deriv_nonneg
    hU.continuous.continuousOn (fun x _ => hd x) (fun x _ => hpos x)).mpr h.1
  refine ⟨by simpa only [Function.comp_apply] using! hi, ?_⟩
  rw [show (∫ x in a..b, deriv U x • g (U x)) = ∫ x in U a..U b, g x from
    intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
      hU.continuous.continuousOn (fun x _ => hd x) (fun x _ => hpos x)]
  exact h.2

/-- [internal]
All seven outgoing equations transport through the two null maps, with
only their original integral equations as inputs. This helper composes
with positive scaling and residual gauge transport; it introduces no
solution or axis predicate on the chart. -/
theorem Observation.null_out_integral_forms_of_integral_forms
    (S : Fields) (U V : ℝ → ℝ) (e u a b : ℝ)
    (hU : ContDiff ℝ 1 U) (hV : ContDiff ℝ 1 V)
    (hUp : ∀ x, 0 < deriv U x) (hVp : ∀ x, 0 < deriv V x)
    (hout : IntegralForm (S.r (U u)) (S.lam (U u)) (V a) (V b) ∧
      IntegralForm (S.nu (U u)) (S.rUV (U u)) (V a) (V b) ∧
      IntegralForm (S.m (U u)) (S.mV (U u)) (V a) (V b) ∧
      IntegralForm (S.Q (U u)) (S.QV e (U u)) (V a) (V b) ∧
      IntegralForm (S.A (U u)) (S.AV (U u)) (V a) (V b) ∧
      IntegralForm (S.phi (U u)) (S.phiV (U u)) (V a) (V b) ∧
      IntegralForm (S.xi (U u)) (S.xiV e (U u)) (V a) (V b)) :
    let P := nullPullback S U V
    IntegralForm (P.r u) (P.lam u) a b ∧
      IntegralForm (P.nu u) (P.rUV u) a b ∧
      IntegralForm (P.m u) (P.mV u) a b ∧
      IntegralForm (P.Q u) (P.QV e u) a b ∧
      IntegralForm (P.A u) (P.AV u) a b ∧
      IntegralForm (P.phi u) (P.phiV u) a b ∧
      IntegralForm (P.xi u) (P.xiV e u) a b := by
  have hdU (x : ℝ) := ((contDiff_one_iff_deriv.mp hU).1 x).hasDerivAt
  have hdV (x : ℝ) := ((contDiff_one_iff_deriv.mp hV).1 x).hasDerivAt
  have hk (v : ℝ) := nullPullback_rhs S U V e u v (deriv U u) (deriv V v)
    (hdU u) (hdV v) (hUp u) (hVp v)
  have k₁ := funext (fun v => (hk v).1)
  have k₂ := funext (fun v => (hk v).2.1)
  have k₄ := funext (fun v => (hk v).2.2.2.1)
  have k₆ := funext (fun v => (hk v).2.2.2.2.2.1)
  have k₇ := funext (fun v => (hk v).2.2.2.2.2.2.1)
  have k₉ := funext (fun v => (hk v).2.2.2.2.2.2.2.2.1)
  rcases hout with ⟨hr, hn, hm, hQ, hA, hφ, hξ⟩
  dsimp only
  rw [k₁, k₂, k₄, k₆, k₇, k₉]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [nullPullback, smul_eq_mul] using!
      Observation.integralForm_comp_c1 hV (fun x => (hVp x).le) hr
  · simpa only [nullPullback, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using!
      Observation.integralForm_mul_const
        (Observation.integralForm_comp_c1 hV (fun x => (hVp x).le) hn) (deriv U u)
  · simpa only [nullPullback, smul_eq_mul] using!
      Observation.integralForm_comp_c1 hV (fun x => (hVp x).le) hm
  · simpa only [nullPullback, smul_eq_mul] using!
      Observation.integralForm_comp_c1 hV (fun x => (hVp x).le) hQ
  · simpa only [nullPullback, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using!
      Observation.integralForm_mul_const
        (Observation.integralForm_comp_c1 hV (fun x => (hVp x).le) hA) (deriv U u)
  · simpa only [nullPullback, real_smul] using!
      Observation.integralForm_comp_c1 hV (fun x => (hVp x).le) hφ
  · simpa only [nullPullback, real_smul, Complex.ofReal_mul,
      mul_comm, mul_left_comm, mul_assoc] using!
      Observation.integralForm_mul_const
        (Observation.integralForm_comp_c1 hV (fun x => (hVp x).le) hξ) ((deriv U u : ℝ) : ℂ)

/-- [internal]
All six incoming equations transport through the chart with the exact
incoming Jacobian. The same hypotheses and helper accept the rescaled or
gauged integral equations; no regular-axis condition is required. -/
theorem Observation.null_in_integral_forms_of_integral_forms
    (S : Fields) (U V : ℝ → ℝ) (e a b v : ℝ)
    (hU : ContDiff ℝ 1 U) (hV : ContDiff ℝ 1 V)
    (hUp : ∀ x, 0 < deriv U x) (hVp : ∀ x, 0 < deriv V x)
    (hin : IntegralForm (fun u => S.r u (V v)) (fun u => S.nu u (V v)) (U a) (U b) ∧
      IntegralForm (fun u => S.lam u (V v)) (fun u => S.rUV u (V v)) (U a) (U b) ∧
      IntegralForm (fun u => S.m u (V v)) (fun u => S.mU u (V v)) (U a) (U b) ∧
      IntegralForm (fun u => S.Q u (V v)) (fun u => S.QU e u (V v)) (U a) (U b) ∧
      IntegralForm (fun u => S.phi u (V v)) (fun u => S.phiU e u (V v)) (U a) (U b) ∧
      IntegralForm (fun u => S.theta u (V v)) (fun u => S.thetaU e u (V v)) (U a) (U b)) :
    let P := nullPullback S U V
    IntegralForm (fun u => P.r u v) (fun u => P.nu u v) a b ∧
      IntegralForm (fun u => P.lam u v) (fun u => P.rUV u v) a b ∧
      IntegralForm (fun u => P.m u v) (fun u => P.mU u v) a b ∧
      IntegralForm (fun u => P.Q u v) (fun u => P.QU e u v) a b ∧
      IntegralForm (fun u => P.phi u v) (fun u => P.phiU e u v) a b ∧
      IntegralForm (fun u => P.theta u v) (fun u => P.thetaU e u v) a b := by
  have hdU (x : ℝ) := ((contDiff_one_iff_deriv.mp hU).1 x).hasDerivAt
  have hdV (x : ℝ) := ((contDiff_one_iff_deriv.mp hV).1 x).hasDerivAt
  have hk (u : ℝ) := nullPullback_rhs S U V e u v (deriv U u) (deriv V v)
    (hdU u) (hdV v) (hUp u) (hVp v)
  have k₁ := funext (fun u => (hk u).1)
  have k₃ := funext (fun u => (hk u).2.2.1)
  have k₅ := funext (fun u => (hk u).2.2.2.2.1)
  have k₈ := funext (fun u => (hk u).2.2.2.2.2.2.2.1)
  have k₁₀ := funext (fun u => (hk u).2.2.2.2.2.2.2.2.2)
  rcases hin with ⟨hr, hlam, hm, hQ, hφ, hθ⟩
  dsimp only
  rw [k₁, k₃, k₅, k₈, k₁₀]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [nullPullback, smul_eq_mul] using!
      Observation.integralForm_comp_c1 hU (fun x => (hUp x).le) hr
  · simpa only [nullPullback, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using!
      Observation.integralForm_mul_const
        (Observation.integralForm_comp_c1 hU (fun x => (hUp x).le) hlam) (deriv V v)
  · simpa only [nullPullback, smul_eq_mul] using!
      Observation.integralForm_comp_c1 hU (fun x => (hUp x).le) hm
  · simpa only [nullPullback, smul_eq_mul] using!
      Observation.integralForm_comp_c1 hU (fun x => (hUp x).le) hQ
  · simpa only [nullPullback, real_smul] using!
      Observation.integralForm_comp_c1 hU (fun x => (hUp x).le) hφ
  · simpa only [nullPullback, real_smul, Complex.ofReal_mul,
      mul_comm, mul_left_comm, mul_assoc] using!
      Observation.integralForm_mul_const
        (Observation.integralForm_comp_c1 hU (fun x => (hUp x).le) hθ) ((deriv V v : ℝ) : ℂ)

/-- [node prop:charged-observation#boundary-null-normalization]
The original frozen solution discharges every integral-equation input to
outgoing chart transport. The original labels, domain and proper section
are explicit, and the chart diagonal need not be the original axis. -/
theorem Observation.null_out_integral_forms
    {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)} (hS : IsSolution e S D)
    (U V : ℝ → ℝ) (hU : ContDiff ℝ 1 U) (hV : ContDiff ℝ 1 V)
    (hUp : ∀ x, 0 < deriv U x) (hVp : ∀ x, 0 < deriv V x)
    {u a b : ℝ} (hab : a ≤ b) (hproper : U u < V a)
    (hseg : outSeg (U u) (V a) (V b) ⊆ D) :
    let P := nullPullback S U V
    IntegralForm (P.r u) (P.lam u) a b ∧
      IntegralForm (P.nu u) (P.rUV u) a b ∧
      IntegralForm (P.m u) (P.mV u) a b ∧
      IntegralForm (P.Q u) (P.QV e u) a b ∧
      IntegralForm (P.A u) (P.AV u) a b ∧
      IntegralForm (P.phi u) (P.phiV u) a b ∧
      IntegralForm (P.xi u) (P.xiV e u) a b := by
  have hm : Monotone V := (strictMono_of_hasDerivAt_pos
    (fun x => ((contDiff_one_iff_deriv.mp hV).1 x).hasDerivAt) hVp).monotone
  exact Observation.null_out_integral_forms_of_integral_forms S U V e u a b
    hU hV hUp hVp (hS.eq_out _ _ _ hproper (hm hab) hseg)

/-- [node prop:charged-observation#boundary-null-normalization]
The original solution likewise discharges all six incoming transport
inputs. No comparison between the chart labels and the original regular
axis is required beyond the displayed proper original section. -/
theorem Observation.null_in_integral_forms
    {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)} (hS : IsSolution e S D)
    (U V : ℝ → ℝ) (hU : ContDiff ℝ 1 U) (hV : ContDiff ℝ 1 V)
    (hUp : ∀ x, 0 < deriv U x) (hVp : ∀ x, 0 < deriv V x)
    {a b v : ℝ} (hab : a ≤ b) (hproper : U b < V v)
    (hseg : inSeg (U a) (U b) (V v) ⊆ D) :
    let P := nullPullback S U V
    IntegralForm (fun u => P.r u v) (fun u => P.nu u v) a b ∧
      IntegralForm (fun u => P.lam u v) (fun u => P.rUV u v) a b ∧
      IntegralForm (fun u => P.m u v) (fun u => P.mU u v) a b ∧
      IntegralForm (fun u => P.Q u v) (fun u => P.QU e u v) a b ∧
      IntegralForm (fun u => P.phi u v) (fun u => P.phiU e u v) a b ∧
      IntegralForm (fun u => P.theta u v) (fun u => P.thetaU e u v) a b := by
  have hm : Monotone U := (strictMono_of_hasDerivAt_pos
    (fun x => ((contDiff_one_iff_deriv.mp hU).1 x).hasDerivAt) hUp).monotone
  exact Observation.null_in_integral_forms_of_integral_forms S U V e a b v
    hU hV hUp hVp (hS.eq_in _ _ _ (hm hab) hproper hseg)

/-- [node prop:charged-observation#boundary-null-normalization]
All outgoing equations hold in the complete gauged, rescaled observation
chart. Every intermediate integral-form premise is discharged from the
original solution; no transformed `IsSolution` is assumed or asserted. -/
theorem Observation.observation_out_integral_forms
    {e s : ℝ} {S : Fields} {D : Set (ℝ × ℝ)} (hS : IsSolution e S D) (hs : 0 < s)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 1 χ) (U V : ℝ → ℝ)
    (hU : ContDiff ℝ 1 U) (hV : ContDiff ℝ 1 V)
    (hUp : ∀ x, 0 < deriv U x) (hVp : ∀ x, 0 < deriv V x)
    {u a b : ℝ} (hab : a ≤ b) (hproper : U u < V a)
    (hseg : outSeg (s * U u) (s * V a) (s * V b) ⊆ D) :
    let P := nullPullback (rescaleFields (gaugeFields e S χ) s) U V
    IntegralForm (P.r u) (P.lam u) a b ∧
      IntegralForm (P.nu u) (P.rUV u) a b ∧
      IntegralForm (P.m u) (P.mV u) a b ∧
      IntegralForm (P.Q u) (P.QV (s * e) u) a b ∧
      IntegralForm (P.A u) (P.AV u) a b ∧
      IntegralForm (P.phi u) (P.phiV u) a b ∧
      IntegralForm (P.xi u) (P.xiV (s * e) u) a b := by
  have hm : Monotone V := (strictMono_of_hasDerivAt_pos
    (fun x => ((contDiff_one_iff_deriv.mp hV).1 x).hasDerivAt) hVp).monotone
  have hg := Observation.gauged_out_integral_forms hS χ hχ
    (mul_lt_mul_of_pos_left hproper hs)
    (mul_le_mul_of_nonneg_left (hm hab) hs.le) hseg
  have hr := Observation.rescaled_out_integral_forms_of_integral_forms
    (gaugeFields e S χ) s e (U u) (V a) (V b) hs hg
  exact Observation.null_out_integral_forms_of_integral_forms
    (rescaleFields (gaugeFields e S χ) s) U V (s * e) u a b hU hV hUp hVp hr

/-- [node prop:charged-observation#boundary-null-normalization]
The same complete chart transports all six incoming integral equations.
The source section is stated in original physical coordinates, so this
theorem also applies when the chart diagonal is the outer cylinder. -/
theorem Observation.observation_in_integral_forms
    {e s : ℝ} {S : Fields} {D : Set (ℝ × ℝ)} (hS : IsSolution e S D) (hs : 0 < s)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 1 χ) (U V : ℝ → ℝ)
    (hU : ContDiff ℝ 1 U) (hV : ContDiff ℝ 1 V)
    (hUp : ∀ x, 0 < deriv U x) (hVp : ∀ x, 0 < deriv V x)
    {a b v : ℝ} (hab : a ≤ b) (hproper : U b < V v)
    (hseg : inSeg (s * U a) (s * U b) (s * V v) ⊆ D) :
    let P := nullPullback (rescaleFields (gaugeFields e S χ) s) U V
    IntegralForm (fun u => P.r u v) (fun u => P.nu u v) a b ∧
      IntegralForm (fun u => P.lam u v) (fun u => P.rUV u v) a b ∧
      IntegralForm (fun u => P.m u v) (fun u => P.mU u v) a b ∧
      IntegralForm (fun u => P.Q u v) (fun u => P.QU (s * e) u v) a b ∧
      IntegralForm (fun u => P.phi u v) (fun u => P.phiU (s * e) u v) a b ∧
      IntegralForm (fun u => P.theta u v) (fun u => P.thetaU (s * e) u v) a b := by
  have hm : Monotone U := (strictMono_of_hasDerivAt_pos
    (fun x => ((contDiff_one_iff_deriv.mp hU).1 x).hasDerivAt) hUp).monotone
  have hg := Observation.gauged_in_integral_forms hS χ hχ
    (mul_le_mul_of_nonneg_left (hm hab) hs.le)
    (mul_lt_mul_of_pos_left hproper hs) hseg
  have hr := Observation.rescaled_in_integral_forms_of_integral_forms
    (gaugeFields e S χ) s e (U a) (U b) (V v) hs hg
  exact Observation.null_in_integral_forms_of_integral_forms
    (rescaleFields (gaugeFields e S χ) s) U V (s * e) a b v hU hV hUp hVp hr

end EmcsfAcExtension.Global
