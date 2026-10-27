module

public import EmcsfAcExtension.Local.Defs.C1Class
public import EmcsfAcExtension.Frozen.IntegralForm
import EmcsfAcExtension.Infra.Calculus.PartialsC1
import EmcsfAcExtension.Infra.Calculus.SectionalC1

/-! # Within-domain partials and normalized classical fields

The sectional formulas use the literal partials of internal project record.
Restriction requires unique differentiation on the smaller domain.
-/

public section

open Set Filter Topology Complex

namespace EmcsfAcExtension.Local

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {D D' : Set (ℝ × ℝ)} {f g : ℝ → ℝ → E} {u v : ℝ}

/-- The incoming derivative of a classical field along any contained section. -/
theorem hasDerivWithinAt_pdU (hf : ContDiffOn ℝ 1 (Function.uncurry f) D)
    (hp : (u, v) ∈ D) {s : Set ℝ} (hs : MapsTo (fun x => (x, v)) s D) :
    HasDerivWithinAt (fun x => f x v) (pdU D f u v) s u :=
  hasDerivWithinAt_section_u hf hp hs

/-- The outgoing derivative of a classical field along any contained section. -/
theorem hasDerivWithinAt_pdV (hf : ContDiffOn ℝ 1 (Function.uncurry f) D)
    (hp : (u, v) ∈ D) {s : Set ℝ} (hs : MapsTo (fun x => (u, x)) s D) :
    HasDerivWithinAt (f u) (pdV D f u v) s v :=
  hasDerivWithinAt_section_v hf hp hs

/-- The ordinary incoming derivative agrees with `pdU` at section interiors. -/
theorem deriv_eq_pdU (hf : ContDiffOn ℝ 1 (Function.uncurry f) D)
    (hp : (u, v) ∈ D) {s : Set ℝ} (hs : MapsTo (fun x => (x, v)) s D)
    (hu : s ∈ 𝓝 u) : deriv (fun x => f x v) u = pdU D f u v :=
  deriv_section_u hf hp hs hu

/-- The ordinary outgoing derivative agrees with `pdV` at section interiors. -/
theorem deriv_eq_pdV (hf : ContDiffOn ℝ 1 (Function.uncurry f) D)
    (hp : (u, v) ∈ D) {s : Set ℝ} (hs : MapsTo (fun x => (u, x)) s D)
    (hv : s ∈ 𝓝 v) : deriv (f u) v = pdV D f u v :=
  deriv_section_v hf hp hs hv

/-- The incoming partial is continuous on a unique-differentiation domain. -/
theorem continuousOn_pdU (hf : ContDiffOn ℝ 1 (Function.uncurry f) D)
    (hD : UniqueDiffOn ℝ D) : ContinuousOn (Function.uncurry (pdU D f)) D :=
  continuousOn_partial_u hf hD

/-- The outgoing partial is continuous on a unique-differentiation domain. -/
theorem continuousOn_pdV (hf : ContDiffOn ℝ 1 (Function.uncurry f) D)
    (hD : UniqueDiffOn ℝ D) : ContinuousOn (Function.uncurry (pdV D f)) D :=
  continuousOn_partial_v hf hD

/-- Restricting to a domain with unique derivatives preserves `pdU`. -/
theorem pdU_mono (hf : ContDiffOn ℝ 1 (Function.uncurry f) D)
    (hsub : D' ⊆ D) (hD' : UniqueDiffOn ℝ D') (hp : (u, v) ∈ D') :
    pdU D' f u v = pdU D f u v := by
  exact congrArg (fun L => L (1, 0)) (fderivWithin_eq_of_subset hf hsub hD' hp)

/-- Restricting to a domain with unique derivatives preserves `pdV`. -/
theorem pdV_mono (hf : ContDiffOn ℝ 1 (Function.uncurry f) D)
    (hsub : D' ⊆ D) (hD' : UniqueDiffOn ℝ D') (hp : (u, v) ∈ D') :
    pdV D' f u v = pdV D f u v := by
  exact congrArg (fun L => L (0, 1)) (fderivWithin_eq_of_subset hf hsub hD' hp)

/-- Incoming partials depend only on field values on the domain. -/
theorem pdU_congr (hfg : EqOn (Function.uncurry f) (Function.uncurry g) D)
    (hp : (u, v) ∈ D) : pdU D f u v = pdU D g u v := by
  exact congrArg (fun L => L (1, 0)) (fderivWithin_eq_of_eqOn hfg hp)

/-- The outgoing partial integrates to the field increment on any contained segment. -/
theorem integralForm_pdV [CompleteSpace E]
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) D) (hD : UniqueDiffOn ℝ D)
    {a b : ℝ} (hab : a ≤ b) (hs : MapsTo (fun x => (u, x)) (Icc a b) D) :
    IntegralForm (f u) (pdV D f u) a b := by
  have hc := hf.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hs
  have hd := (continuousOn_pdV hf hD).comp
    (continuous_const.prodMk continuous_id).continuousOn hs
  have hi := hd.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hab
  exact ⟨hi, (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hc
    (fun x hx => (hasDerivWithinAt_pdV hf (hs ⟨hx.1.le, hx.2.le⟩) hs).hasDerivAt
      (Icc_mem_nhds hx.1 hx.2)) hi).symm⟩

/-- The incoming partial integrates to the field increment on any contained segment. -/
theorem integralForm_pdU [CompleteSpace E]
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) D) (hD : UniqueDiffOn ℝ D)
    {a b : ℝ} (hab : a ≤ b) (hs : MapsTo (fun x => (x, v)) (Icc a b) D) :
    IntegralForm (fun x => f x v) (fun x => pdU D f x v) a b := by
  have hc := hf.continuousOn.comp
    (continuous_id.prodMk continuous_const).continuousOn hs
  have hd := (continuousOn_pdU hf hD).comp
    (continuous_id.prodMk continuous_const).continuousOn hs
  have hi := hd.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hab
  exact ⟨hi, (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hc
    (fun x hx => (hasDerivWithinAt_pdU hf (hs ⟨hx.1.le, hx.2.le⟩) hs).hasDerivAt
      (Icc_mem_nhds hx.1 hx.2)) hi).symm⟩

variable {e : ℝ} {S : Fields}

/-- The normalized outgoing scalar is C¹; positivity of `λ` supplies its denominator. -/
theorem IsC1Solution.c1_a (hS : IsC1Solution e S D) :
    ContDiffOn ℝ 1 (Function.uncurry S.a) D := by
  simpa only [div_eq_mul_inv] using!
    hS.c1_phi.add (hS.c1_theta.mul
      ((Complex.ofRealCLM.contDiff.comp_contDiffOn hS.c1_lam).inv
        (fun p hp => Complex.ofReal_ne_zero.mpr (ne_of_gt (hS.lam_pos p hp)))))

/-- The normalized incoming scalar is C¹; negativity of `ν` supplies its denominator. -/
theorem IsC1Solution.c1_b (hS : IsC1Solution e S D) :
    ContDiffOn ℝ 1 (Function.uncurry S.b) D := by
  simpa only [div_eq_mul_inv] using!
    hS.c1_phi.add (hS.c1_xi.mul
      ((Complex.ofRealCLM.contDiff.comp_contDiffOn hS.c1_nu).inv
        (fun p hp => Complex.ofReal_ne_zero.mpr (ne_of_lt (hS.nu_neg p hp)))))

end EmcsfAcExtension.Local
