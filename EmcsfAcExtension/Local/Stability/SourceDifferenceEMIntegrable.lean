module

public import EmcsfAcExtension.Local.Stability.SourceDifferenceEMPrimitives
import EmcsfAcExtension.Local.Calculus.AxisRatio

/-! # Continuity and integrability of the charged primitive integrands

The regular-center extension of `Q/r` has value zero at the axis. Writing
the quadratic charge term with that ratio proves literal continuity.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local.Stab

/-- Both literal charged primitive integrands are continuous on the closed
triangle. The zero value of `Q/r` at the axis follows from Maxwell regularity,
so no arbitrary extension or extra regularity hypothesis is used. -/
theorem emPrimitive_continuousOn {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hs : StabSetting e T ε M A S h) :
    ContinuousOn (Function.uncurry (emPrimitiveOut e S)) (triangle 0 T) ∧
    ContinuousOn (Function.uncurry (emPrimitiveIn e S)) (triangle 0 T) := by
  obtain ⟨q, cq, hq, hqaxis⟩ := exists_continuous_charge_ratio_aux hs.pos hs.c1
  have hQr : ContinuousOn (fun p => S.Q p.1 p.2 / S.r p.1 p.2) (triangle 0 T) := by
    apply cq.congr
    rintro ⟨u, v⟩ hp
    change S.Q u v / S.r u v = q (u, v)
    rcases hp.2.1.eq_or_lt with heq | hlt
    · change u = v at heq
      subst v
      rw [(hs.c1.axis u hp).1, div_zero, hqaxis u ⟨hp.1, hp.2.2⟩]
    · exact (hq u v hp hlt).symm
  have hl := Complex.continuous_ofReal.comp_continuousOn hs.c1.c1_lam.continuousOn
  have hn := Complex.continuous_ofReal.comp_continuousOn hs.c1.c1_nu.continuousOn
  have hQ := Complex.continuous_ofReal.comp_continuousOn hs.c1.c1_Q.continuousOn
  have hQc := Complex.continuous_ofReal.comp_continuousOn hQr
  have hφ := hs.c1.c1_phi.continuousOn
  have hx := hs.c1.c1_theta.continuousOn
  have hy := hs.c1.c1_xi.continuousOn
  have hcontₒ : ContinuousOn (fun p => (S.lam p.1 p.2 : ℂ) *
      (((S.Q p.1 p.2 / S.r p.1 p.2 : ℝ) : ℂ) ^ 2) -
        I * e * S.Q p.1 p.2 * S.theta p.1 p.2 * starRingEnd ℂ (S.phi p.1 p.2))
      (triangle 0 T) := by fun_prop
  have hcontᵢ : ContinuousOn (fun p => (S.nu p.1 p.2 : ℂ) *
      (((S.Q p.1 p.2 / S.r p.1 p.2 : ℝ) : ℂ) ^ 2) +
        I * e * S.Q p.1 p.2 * S.xi p.1 p.2 * starRingEnd ℂ (S.phi p.1 p.2))
      (triangle 0 T) := by fun_prop
  constructor
  · apply hcontₒ.congr
    intro p hp
    dsimp only [Function.uncurry_def, emPrimitiveOut]
    push_cast
    rw [div_pow]
    ring
  · apply hcontᵢ.congr
    intro p hp
    dsimp only [Function.uncurry_def, emPrimitiveIn]
    push_cast
    rw [div_pow]
    ring

/-- Both literal charged primitive integrands are integrable along any
continuous compact path in the triangle. Both characteristic orientations
and their axis endpoints are covered without a lower radius cutoff. -/
theorem emPrimitive_integrable_along {e T ε M A a b : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hs : StabSetting e T ε M A S h) {p : ℝ → ℝ × ℝ}
    (hp : ContinuousOn p (Icc a b)) (hmap : MapsTo p (Icc a b) (triangle 0 T)) :
    IntegrableOn (fun w => emPrimitiveOut e S (p w).1 (p w).2) (Icc a b) ∧
    IntegrableOn (fun w => emPrimitiveIn e S (p w).1 (p w).2) (Icc a b) := by
  have hc := emPrimitive_continuousOn hs
  exact ⟨(hc.1.comp hp hmap).integrableOn_Icc, (hc.2.comp hp hmap).integrableOn_Icc⟩

end EmcsfAcExtension.Local.Stab
