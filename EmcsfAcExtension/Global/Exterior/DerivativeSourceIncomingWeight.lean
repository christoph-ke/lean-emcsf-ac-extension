module

public import EmcsfAcExtension.Global.Exterior.DerivativeSourceIncomingSup
public import EmcsfAcExtension.Global.Exterior.FrontierIncomingTails

/-! # The literal two-term incoming radius weight

The weight contains the actual field supremum and the scalar-charge term,
without replacing them by a larger forcing in the exported bound. The
forcing is used only to prove its integrability. Source:
`charged_SF_new_version.tex:L1356–L1360`, L1405–L1408; internal project record (I1).
-/

public section

open Set MeasureTheory Filter Topology

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
The exact two-term radius majorant in the cylinder incoming-tail contract. -/
@[expose] noncomputable def incomingRadiusWeight (e : ℝ) (M ell L SF : ℝ → ℝ) (R : ℝ) : ℝ :=
  M R / ell R ^ 2 * SF R + |e| * L R * Real.sqrt (M R / ell R)

/-- [internal]
The literal incoming radius weight is nonnegative. No constants occur. -/
theorem incomingRadiusWeight_nonneg {e R : ℝ} {M ell L SF : ℝ → ℝ}
    (hM : 0 ≤ M R) (hSF : 0 ≤ SF R) (hL : 0 ≤ L R) :
    0 ≤ incomingRadiusWeight e M ell L SF R := by
  dsimp only [incomingRadiusWeight]
  positivity

/-- [internal]
The exact two-term radius majorant is integrable whenever its actual
supremum is continuous and uniformly bounded by `B`. This uses the
already proved `A,G` integrability, but does not alter the exported
majorant. The bound `B` is fixed before every radius. -/
theorem incomingRadiusWeight_integrable {e Rc B : ℝ} {M ell L SF : ℝ → ℝ}
    (hMc : ContinuousOn M (Ioc 0 Rc)) (hec : ContinuousOn ell (Ioc 0 Rc))
    (hLc : ContinuousOn L (Ioc 0 Rc)) (hSFc : ContinuousOn SF (Ioc 0 Rc))
    (hM : ∀ R ∈ Ioc 0 Rc, 0 ≤ M R) (he : ∀ R ∈ Ioc 0 Rc, 0 < ell R)
    (hL : ∀ R ∈ Ioc 0 Rc, 0 ≤ L R)
    (hSF : ∀ R ∈ Ioc 0 Rc, 0 ≤ SF R ∧ SF R ≤ B)
    (hAi : IntegrableOn (fun R => M R / ell R ^ 2) (Ioc 0 Rc))
    (hGi : IntegrableOn (exteriorForcing e M ell L) (Ioc 0 Rc)) :
    IntegrableOn (incomingRadiusWeight e M ell L SF) (Ioc 0 Rc) := by
  have cA := hMc.div (hec.pow 2) (fun R hR => pow_ne_zero _ (he R hR).ne')
  have cX := hMc.div hec (fun R hR => (he R hR).ne')
  have cT : ContinuousOn (incomingRadiusWeight e M ell L SF) (Ioc 0 Rc) :=
    (cA.mul hSFc).add ((hLc.const_mul |e|).mul cX.sqrt)
  have hi := (hAi.const_mul B).add hGi
  apply Integrable.mono' hi (cT.aestronglyMeasurable measurableSet_Ioc)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with R hR
  rw [Real.norm_eq_abs, abs_of_nonneg
    (incomingRadiusWeight_nonneg (hM R hR) (hSF R hR).1 (hL R hR))]
  have hfirst := mul_le_mul_of_nonneg_left (hSF R hR).2
    (div_nonneg (hM R hR) (sq_nonneg (ell R)))
  have hsecond := scalar_charge_weight_le_forcing (e := e)
    (hM R hR) (he R hR) (hL R hR)
  simpa only [incomingRadiusWeight, Pi.add_apply, mul_comm] using add_le_add hfirst hsecond

end EmcsfAcExtension.Global.Exterior
