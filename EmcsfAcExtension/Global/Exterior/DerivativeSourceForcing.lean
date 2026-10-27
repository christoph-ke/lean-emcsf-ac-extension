module

public import EmcsfAcExtension.Global.Exterior.RadiiProfile
public import EmcsfAcExtension.Global.Exterior.ScalarEnergy
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-! # Integrable radius forcing for the exterior derivative equation

The forcing is the literal sum of the five terms in internal project record (O8).
Its estimates have no outgoing-variation premise. Constants in the
majorants may depend only on the fixed coupling, logarithmic envelope
and initial radius, uniformly in the terminal integration endpoint.
Source: `charged_SF_new_version.tex:L1322–L1335`.
-/

public section

open Set MeasureTheory Filter Topology

namespace EmcsfAcExtension.Global.Exterior

/-- [def-node c:exterior#forcing-integrability]
The nonnegative radius forcing of approved internal project record (O8), with exactly
the five terms of `charged_SF_new_version.tex:L1300–L1310`. -/
@[expose] noncomputable def exteriorForcing (e : ℝ) (M ell L : ℝ → ℝ) (R : ℝ) : ℝ :=
  M R / ell R ^ 2 * Real.sqrt (M R / ell R) +
  |e| * L R * (M R / ell R) * Real.sqrt (M R / ell R) +
  |e| * (M R / ell R) + |e| * L R * Real.sqrt (M R / ell R) +
  e ^ 2 * L R ^ 2 * Real.sqrt (M R * R)

/-- [internal]
The logarithmic envelope is continuous at every positive radius. -/
theorem logarithmic_envelope_continuousOn {Ri C Rc : ℝ} (hRi : 0 < Ri) :
    ContinuousOn (fun R => C * (1 + Real.sqrt (Real.log (Ri / R)))) (Ioc 0 Rc) := by
  exact continuousOn_const.mul (continuousOn_const.add
    (((continuousOn_const.div continuousOn_id (fun R hR => hR.1.ne')).log
      (fun R hR => div_ne_zero hRi.ne' hR.1.ne')).sqrt))

/-- [internal]
The square of a logarithmic scalar envelope is integrable all the way
to zero. The envelope coefficient and reference radius are fixed before
the variable integration endpoint; no solution-dependent premise occurs. -/
theorem logarithmic_envelope_sq_integrable {Ri C Rc : ℝ} (hRi : 0 < Ri)
    (hRc : 0 < Rc) :
    IntegrableOn (fun R => (C * (1 + Real.sqrt (Real.log (Ri / R)))) ^ 2)
      (Ioc 0 Rc) := by
  have hlog : IntegrableOn (fun R : ℝ => |Real.log R|) (Ioc 0 Rc) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hRc.le).1
      (intervalIntegral.intervalIntegrable_log' (a := 0) (b := Rc))).abs
  have hc : IntegrableOn (fun _ : ℝ => 1 + |Real.log Ri|) (Ioc 0 Rc) :=
    integrableOn_const (measure_Ioc_lt_top.ne)
  have hmajor := (hc.add hlog).const_mul (2 * C ^ 2)
  have hmeas : AEStronglyMeasurable
      (fun R => (C * (1 + Real.sqrt (Real.log (Ri / R)))) ^ 2)
      (volume.restrict (Ioc 0 Rc)) :=
    ((logarithmic_envelope_continuousOn (C := C) (Rc := Rc) hRi).pow 2).aestronglyMeasurable
      measurableSet_Ioc
  apply Integrable.mono' hmajor hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with R hR
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hdiv : Real.log (Ri / R) = Real.log Ri - Real.log R :=
    Real.log_div hRi.ne' hR.1.ne'
  have hs : Real.sqrt (Real.log (Ri / R)) ^ 2 ≤ |Real.log (Ri / R)| := by
    rw [Real.sq_sqrt']; exact max_le (le_abs_self _) (abs_nonneg _)
  have hb := abs_sub (Real.log Ri) (Real.log R)
  rw [← hdiv] at hb
  have hyoung := sq_nonneg (1 - Real.sqrt (Real.log (Ri / R)))
  have hs' : (1 + Real.sqrt (Real.log (Ri / R))) ^ 2 ≤
      2 * (1 + |Real.log Ri| + |Real.log R|) := by nlinarith only [hs, hb, hyoung]
  have hh := mul_le_mul_of_nonneg_left hs' (sq_nonneg C)
  dsimp only [Pi.add_apply] at hh ⊢
  nlinarith only [hh]

/-- [internal]
A logarithmic scalar envelope is integrable near zero. Constants depend
only on its coefficient and reference radius, uniformly in the cutoff. -/
theorem logarithmic_envelope_integrable {Ri C Rc : ℝ} (hRi : 0 < Ri)
    (hRc : 0 < Rc) :
    IntegrableOn (fun R => C * (1 + Real.sqrt (Real.log (Ri / R)))) (Ioc 0 Rc) := by
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 0 Rc) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hi := hconst.add (logarithmic_envelope_sq_integrable (C := C) hRi hRc)
  apply Integrable.mono' hi
    ((logarithmic_envelope_continuousOn hRi).aestronglyMeasurable measurableSet_Ioc)
  filter_upwards with R
  dsimp only [Pi.add_apply]
  rw [Real.norm_eq_abs]
  nlinarith only [sq_nonneg (|C * (1 + Real.sqrt (Real.log (Ri / R)))| - 1),
    sq_abs (C * (1 + Real.sqrt (Real.log (Ri / R))))]

/-- [internal]
An explicit integrable majorant for the forcing. The auxiliary bound `K`
controls `L ell`, and is derived from the logarithmic envelope in the
terminal consumer. The estimate is uniform in every radius in the interval. -/
theorem exteriorForcing_le_of_profiles {e R M ell L K Rc : ℝ}
    (hR : 0 < R) (hRR : R ≤ Rc) (hM : 0 ≤ M) (hMR : M ≤ R)
    (he : 0 < ell) (hX : M / ell ≤ 1) (hL : 0 ≤ L) (hK : L * ell ≤ K) :
    M / ell ^ 2 * Real.sqrt (M / ell) +
      |e| * L * (M / ell) * Real.sqrt (M / ell) + |e| * (M / ell) +
      |e| * L * Real.sqrt (M / ell) + e ^ 2 * L ^ 2 * Real.sqrt (M * R) ≤
    (1 + |e| * K) * (M / ell ^ 2) + |e| + |e| * L + e ^ 2 * Rc * L ^ 2 := by
  have hA := div_nonneg hM (sq_nonneg ell)
  have hx0 := div_nonneg hM he.le
  have hs := Real.sqrt_nonneg (M / ell)
  have hs1 : Real.sqrt (M / ell) ≤ 1 := by
    exact (Real.sqrt_le_iff).2 ⟨by norm_num, by simpa using hX⟩
  have hroot : Real.sqrt (M * R) ≤ Rc := by
    refine (Real.sqrt_le_iff).2 ⟨hR.le.trans hRR, ?_⟩
    nlinarith [mul_le_mul_of_nonneg_right hMR hR.le,
      pow_le_pow_left₀ hR.le hRR 2]
  have hterm1 := mul_le_mul_of_nonneg_left hs1 hA
  have hterm2 : |e| * L * (M / ell) * Real.sqrt (M / ell) ≤ |e| * K * (M / ell ^ 2) := by
    have hfirst := mul_le_mul_of_nonneg_left hs1 (by positivity : 0 ≤ |e| * L * (M / ell))
    have hsecond := mul_le_mul_of_nonneg_left hK (mul_nonneg (abs_nonneg e) hA)
    have heq : |e| * L * (M / ell) = (|e| * (M / ell ^ 2)) * (L * ell) := by
      field_simp
    calc
      _ ≤ |e| * L * (M / ell) := by simpa only [mul_one] using hfirst
      _ = (|e| * (M / ell ^ 2)) * (L * ell) := heq
      _ ≤ (|e| * (M / ell ^ 2)) * K := hsecond
      _ = _ := by ring
  have hterm3 := mul_le_mul_of_nonneg_left hX (abs_nonneg e)
  have hterm4 := mul_le_mul_of_nonneg_left hs1 (mul_nonneg (abs_nonneg e) hL)
  have hterm5 := mul_le_mul_of_nonneg_left hroot (mul_nonneg (sq_nonneg e) (sq_nonneg L))
  nlinarith only [hterm1, hterm2, hterm3, hterm4, hterm5]

/-- [internal]
Analytic forcing integrability from the adaptive mass weight, scalar
integrability and its square. No forcing integral or tail is assumed.
The bound `K` is uniform over the entire fixed radius interval. -/
theorem exteriorForcing_integrable_of_profiles {e Rc K : ℝ} {M ell L : ℝ → ℝ}
    (_hRc : 0 < Rc)
    (hMc : ContinuousOn M (Ioc 0 Rc)) (hec : ContinuousOn ell (Ioc 0 Rc))
    (hLc : ContinuousOn L (Ioc 0 Rc))
    (hA : IntegrableOn (fun R => M R / ell R ^ 2) (Ioc 0 Rc))
    (hL1 : IntegrableOn L (Ioc 0 Rc))
    (hL2 : IntegrableOn (fun R => L R ^ 2) (Ioc 0 Rc))
    (hM : ∀ R ∈ Ioc 0 Rc, 0 ≤ M R ∧ M R ≤ R)
    (he : ∀ R ∈ Ioc 0 Rc, 0 < ell R)
    (hX : ∀ R ∈ Ioc 0 Rc, M R / ell R ≤ 1)
    (hL : ∀ R ∈ Ioc 0 Rc, 0 ≤ L R)
    (hK : ∀ R ∈ Ioc 0 Rc, L R * ell R ≤ K) :
    IntegrableOn (exteriorForcing e M ell L) (Ioc 0 Rc) := by
  have cx := hMc.div hec (fun R hR => (he R hR).ne')
  have ca := hMc.div (hec.pow 2) (fun R hR => pow_ne_zero _ (he R hR).ne')
  have hc : ContinuousOn (exteriorForcing e M ell L) (Ioc 0 Rc) := by
    exact ((((ca.mul cx.sqrt).add (((hLc.const_mul |e|).mul cx).mul cx.sqrt)).add
      (cx.const_mul |e|)).add ((hLc.const_mul |e|).mul cx.sqrt)).add
      (((hLc.pow 2).const_mul (e ^ 2)).mul (hMc.mul continuousOn_id).sqrt)
  have hi := (((hA.const_mul (1 + |e| * K)).add
    (integrableOn_const (s := Ioc 0 Rc) (μ := volume) (C := |e|) measure_Ioc_lt_top.ne)).add
    (hL1.const_mul |e|)).add (hL2.const_mul (e ^ 2 * Rc))
  apply Integrable.mono' hi (hc.aestronglyMeasurable measurableSet_Ioc)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with R hR
  have hnonneg : 0 ≤ exteriorForcing e M ell L R := by
    dsimp [exteriorForcing]
    have hm := (hM R hR).1
    have hel := (he R hR).le
    have hl := hL R hR
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  dsimp only [Pi.add_apply]
  exact exteriorForcing_le_of_profiles hR.1 hR.2 (hM R hR).1 (hM R hR).2
    (he R hR) (hX R hR) (hL R hR) (hK R hR)

end EmcsfAcExtension.Global.Exterior
