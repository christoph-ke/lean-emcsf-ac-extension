module

public import EmcsfAcExtension.Frozen.CovVarIn
public import EmcsfAcExtension.Frozen.Fields.NormalizedIn
public import EmcsfAcExtension.Infra.AC.Quotient
public import EmcsfAcExtension.Infra.AC.Complex
public import EmcsfAcExtension.Infra.AC.Variation

/-! # The actual incoming parallel representative of an AC scalar section

The parallel factor uses each solution's own connection, with reference
label zero. All identities hold sectionwise almost everywhere.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

/-- The unit incoming parallel factor in the fixed gauge, based at zero. -/
@[expose] noncomputable def incomingParallel (e : ℝ) (A : ℝ → ℝ → ℝ) (u v : ℝ) : ℂ :=
  Complex.exp (I * e * ∫ s in (0 : ℝ)..u, A s v)

/-- The ordinary incoming section derivative plus its own connection term. -/
@[expose] noncomputable def incomingCovDeriv (e : ℝ) (S : Fields) (u v : ℝ) : ℂ :=
  deriv (fun u => S.b u v) u + I * e * S.A u v * S.b u v

/-- Each incoming parallel factor has norm one, uniformly in the connection,
coupling and labels; no integral-finiteness premise is needed for this identity. -/
theorem norm_incomingParallel (e : ℝ) (A : ℝ → ℝ → ℝ) (u v : ℝ) :
    ‖incomingParallel e A u v‖ = 1 := by
  simpa only [incomingParallel, ← Complex.ofReal_mul, mul_assoc] using
    Complex.norm_exp_I_mul_ofReal (e * ∫ s in (0 : ℝ)..u, A s v)

/-- A continuous incoming potential has an AC parallel factor on its whole
section, independently of whether that potential has an incoming derivative. -/
theorem incomingParallel_ac_of_continuous {e v : ℝ} {A : ℝ → ℝ → ℝ}
    (hv : 0 ≤ v) (hA : ContinuousOn (fun u => A u v) (Icc 0 v)) :
    AbsolutelyContinuousOnInterval (fun u => incomingParallel e A u v) 0 v := by
  have hi : IntervalIntegrable (fun u => A u v) volume 0 v := hA.intervalIntegrable_of_Icc hv
  have hangle := (hi.absolutelyContinuousOnInterval_intervalIntegral_normed left_mem_uIcc).const_mul
      e
  simpa only [incomingParallel, Complex.ofReal_mul, mul_assoc] using hangle.unit_phase

/-- AC of the incoming normalized field and continuity of its own potential
make the transported field AC, with the expected covariant derivative a.e.
No incoming derivative of the potential is required. -/
theorem incoming_parallel_ac_deriv_of_ac {e v : ℝ} {S : Fields}
    (hv : 0 ≤ v) (hA : ContinuousOn (fun u => S.A u v) (Icc 0 v))
    (hb : AbsolutelyContinuousOnInterval (fun u => S.b u v) 0 v) :
    AbsolutelyContinuousOnInterval (fun u => incomingParallel e S.A u v * S.b u v) 0 v ∧
    deriv (fun u => incomingParallel e S.A u v * S.b u v) =ᵐ[volume.restrict (Icc 0 v)]
      (fun u => incomingParallel e S.A u v * incomingCovDeriv e S u v) := by
  have hi : IntervalIntegrable (fun u => S.A u v) volume 0 v := hA.intervalIntegrable_of_Icc hv
  have hangle := (hi.absolutelyContinuousOnInterval_intervalIntegral_normed left_mem_uIcc).const_mul
      e
  have hP : AbsolutelyContinuousOnInterval (fun u => incomingParallel e S.A u v) 0 v := by
    simpa only [incomingParallel, Complex.ofReal_mul, mul_assoc] using hangle.unit_phase
  refine ⟨hP.mul_normed_ring hb, ?_⟩
  filter_upwards [ae_restrict_of_ae hi.ae_hasDerivAt_integral,
    ae_restrict_of_ae hb.ae_differentiableAt_of_mem_uIcc,
    ae_restrict_mem measurableSet_Icc] with u hu hbu humem
  have hum : u ∈ uIcc 0 v := by rwa [uIcc_of_le hv]
  have hd := (((hu hum 0 left_mem_uIcc).ofReal_comp.const_mul (I * (e : ℂ))).cexp).mul
    (hbu hum).hasDerivAt
  simpa only [incomingParallel, incomingCovDeriv, Pi.mul_def, mul_add, mul_assoc,
    add_comm] using hd.deriv

/-- The incoming covariant derivative is integrable and its norm integral
is exactly the frozen covariant variation. The coefficient is one, uniformly
in all parameters and sections. -/
theorem incoming_covDeriv_integral_of_ac {e v : ℝ} {S : Fields}
    (hv : 0 ≤ v) (hA : ContinuousOn (fun u => S.A u v) (Icc 0 v))
    (hb : AbsolutelyContinuousOnInterval (fun u => S.b u v) 0 v) :
    IntervalIntegrable (incomingCovDeriv e S · v) volume 0 v ∧
    (∫ u in (0 : ℝ)..v, ‖incomingCovDeriv e S u v‖) = (covVarIn e S.A S.b 0 v v).toReal := by
  obtain ⟨hac, heq⟩ := incoming_parallel_ac_deriv_of_ac hv hA hb
  have hn : (fun u => ‖incomingCovDeriv e S u v‖) =ᵐ[volume.restrict (Icc 0 v)]
      (fun u => ‖deriv (fun u => incomingParallel e S.A u v * S.b u v) u‖) := by
    filter_upwards [heq] with u hu
    rw [hu, norm_mul, norm_incomingParallel, one_mul]
  have hi : IntervalIntegrable (incomingCovDeriv e S · v) volume 0 v := by
    have hbc : ContinuousOn (fun u => S.b u v) (Icc 0 v) := by
      simpa only [uIcc_of_le hv] using hb.continuousOn
    have hc : ContinuousOn (fun u => I * e * S.A u v * S.b u v) (Icc 0 v) :=
      ((continuousOn_const (c := I * (e : ℂ))).mul
        (Complex.continuous_ofReal.comp_continuousOn hA)).mul hbc
    exact hb.intervalIntegrable_deriv_complex.add (hc.intervalIntegrable_of_Icc hv)
  refine ⟨hi, ?_⟩
  have hh := hac.toReal_eVariationOn_eq_integral_norm_deriv hv
  change (∫ u in (0 : ℝ)..v, ‖incomingCovDeriv e S u v‖) =
    (eVariationOn (fun u => incomingParallel e S.A u v * S.b u v) (Icc 0 v)).toReal
  rw [hh]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le hv]
  exact ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hn

end EmcsfAcExtension.Local
