module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Frozen.CovVarIn
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseNorms
import EmcsfAcExtension.Local.Apriori.BootstrapVariationAux
import EmcsfAcExtension.Local.Apriori.BootstrapCovariant
import EmcsfAcExtension.Local.Apriori.Hardy
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Calculus.Partials

/-! # Localized scalar variation and Hardy clauses for smooth bounds

The real absorptions are converted back to finite nonnegative variations.
All four complete-section estimates keep the localized envelope integral
required by internal project record, without a global replacement of its right side.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local

/-- All localized scalar variation and Hardy bounds hold with universal
coefficient three when `ε ≤ 1/8`. The coefficient depends only on the fixed
box and is uniform in all fields and higher initial derivatives. The two
incoming estimates retain the frozen covariant representative. -/
theorem localized_scalar_budgets {e T ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) (hε : ε ≤ 1 / 8)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    eVariationOn (S.a u) (Icc u v) ≤
        ENNReal.ofReal (3 * ∫ x in u..v, (outEnv 0 (jC1 (triangle 0 T) S) x).toReal) ∧
    covVarIn e S.A S.b u v v ≤
        ENNReal.ofReal (3 * ∫ x in u..v, (inEnv T (kC1 e (triangle 0 T) S) x).toReal) ∧
    (∫⁻ x in Icc u v, ENNReal.ofReal (S.lam u x / S.r u x *
        ‖S.theta u x / S.lam u x‖)) ≤
        ENNReal.ofReal (3 * ∫ x in u..v, (outEnv 0 (jC1 (triangle 0 T) S) x).toReal) ∧
    (∫⁻ x in Icc u v, ENNReal.ofReal (-S.nu x v / S.r x v *
        ‖S.xi x v / S.nu x v‖)) ≤
        ENNReal.ofReal (3 * ∫ x in u..v, (inEnv T (kC1 e (triangle 0 T) S) x).toReal) := by
  have hv := characteristic_variation_budgets hset hε hu huv hvT
  have ho := bv_hardy_out_integrated hset.c1 hu huv hvT
  have hi := bv_hardy_in_integrated hset.c1 hu huv hvT
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [variation_out_eq_integral_partial hset.c1.c1_a hu huv hvT,
      ← bv_variation_out hset.c1 hu huv hvT]
    exact ENNReal.ofReal_le_ofReal hv.1
  · rw [← ENNReal.ofReal_toReal (covariant_variation_ne_top hset.c1 hu huv hvT),
      bv_variation_in hset.c1 hu huv hvT]
    exact ENNReal.ofReal_le_ofReal hv.2
  · rw [← ofReal_integral_eq_lintegral_ofReal
      ((intervalIntegrable_iff_integrableOn_Icc_of_le huv).mp ho.1)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        have hp : (u, x) ∈ triangle 0 T := ⟨hu, hx.1, hx.2.trans hvT⟩
        exact mul_nonneg (div_nonneg (hset.c1.lam_pos (u, x) hp).le
          (hset.radius_nonneg hp)) (norm_nonneg _)),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le huv]
    exact ENNReal.ofReal_le_ofReal (ho.2.trans hv.1)
  · rw [← ofReal_integral_eq_lintegral_ofReal
      ((intervalIntegrable_iff_integrableOn_Icc_of_le huv).mp hi.1)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        have hp : (x, v) ∈ triangle 0 T := ⟨hu.trans hx.1, hx.2, hvT⟩
        exact mul_nonneg (div_nonneg (neg_pos.mpr (hset.c1.nu_neg (x, v) hp)).le
          (hset.radius_nonneg hp)) (norm_nonneg _)),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le huv]
    exact ENNReal.ofReal_le_ofReal (hi.2.trans hv.2)

end EmcsfAcExtension.Local
