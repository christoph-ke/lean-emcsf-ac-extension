module

public import EmcsfAcExtension.Local.Defs.Limit
public import EmcsfAcExtension.Local.Defs.Envelope
import EmcsfAcExtension.Local.Limit.UIEnvelope

/-! # Real L¹ envelopes of the limiting frozen derivatives

The real-valued form of internal project record's `#limit-renormalized-envelope-bound`.
Finite extended envelopes have nonnegative measurable real representatives;
the two integrals retain the same single numerical constant.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

/-- [internal]
Realize nonnegative real L¹ envelopes for the actual frozen derivatives.
The constant `C` is inherited unchanged from the smooth bound, fixed before
coupling, time, data and approximants. No new constant or threshold is selected. -/
theorem Null.limit_renormalized_real_envelope_bound_of_strongLimit
    {C e T ε : ℝ} {εn : ℕ → ℝ} {Sn : ℕ → Fields} {S : Fields}
    (hC : 0 ≤ C) (hε0 : 0 ≤ ε)
    (hT : 0 < T) (hS : ∀ n, IsC1Solution e (Sn n) (triangle 0 T))
    (hlim : StrongLimit e T Sn S) (hε : Tendsto εn atTop (𝓝 ε))
    (hbound : ∀ᶠ n in atTop,
      (∫⁻ v in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) (Sn n)) v) +
        (∫⁻ u in Icc 0 T, inEnv T (kC1 e (triangle 0 T) (Sn n)) u) ≤
          ENNReal.ofReal (C * εn n)) :
    ∃ J K : ℝ → ℝ, Measurable J ∧ Measurable K ∧
      (∀ x, 0 ≤ J x) ∧ (∀ x, 0 ≤ K x) ∧
      IntegrableOn J (Icc 0 T) ∧ IntegrableOn K (Icc 0 T) ∧
      (∀ u ∈ Icc 0 T, ∀ᵐ v ∂volume.restrict (Icc u T), ‖jOut S u v‖ ≤ J v) ∧
      (∀ v ∈ Icc 0 T, ∀ᵐ u ∂volume.restrict (Icc 0 v), ‖kIn e S u v‖ ≤ K u) ∧
      (∫ v in Icc 0 T, J v) + (∫ u in Icc 0 T, K u) ≤ C * ε := by
  obtain ⟨J, K, hJ, hK, hJfin, hKfin, hjdom, hkdom, hmass⟩ :=
    Null.limit_renormalized_envelope_bound_of_strongLimit hT hS hlim hε hbound
  have hJtop : ∀ᵐ v ∂volume.restrict (Icc 0 T), J v < ⊤ := ae_lt_top hJ hJfin.ne
  have hKtop : ∀ᵐ u ∂volume.restrict (Icc 0 T), K u < ⊤ := ae_lt_top hK hKfin.ne
  refine ⟨fun v => (J v).toReal, fun u => (K u).toReal,
    hJ.ennreal_toReal, hK.ennreal_toReal, fun _ => ENNReal.toReal_nonneg,
    fun _ => ENNReal.toReal_nonneg,
    integrable_toReal_of_lintegral_ne_top hJ.aemeasurable hJfin.ne,
    integrable_toReal_of_lintegral_ne_top hK.aemeasurable hKfin.ne, ?_, ?_, ?_⟩
  · intro u hu
    have hh := ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc hu.1 le_rfl) hJtop
    filter_upwards [hjdom u hu, hh] with v hv hfin
    simpa only [toReal_enorm] using ENNReal.toReal_mono hfin.ne hv
  · intro v hv
    have hh := ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc le_rfl hv.2) hKtop
    filter_upwards [hkdom v hv, hh] with u hu hfin
    simpa only [toReal_enorm] using ENNReal.toReal_mono hfin.ne hu
  · rw [integral_toReal hJ.aemeasurable hJtop, integral_toReal hK.aemeasurable hKtop,
      ← ENNReal.toReal_add hJfin.ne hKfin.ne]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass).trans_eq
      (ENNReal.toReal_ofReal (mul_nonneg hC hε0))

end EmcsfAcExtension.Local
