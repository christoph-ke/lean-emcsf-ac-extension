module

public import EmcsfAcExtension.Global.Observation.Static.CutoffFamily
import Mathlib

/-! # Radial fields of each stopped inner static reference

The common coefficient bound supplies a positive common gap and the
scalar and mass-factor bounds on each member's own stopped annulus.
Source: charged_SF_new_version.tex:L2230–2239, L2652–2735; approved internal project record.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
The stopped inverse-radius reference supplies every radial static input
of the inner comparison interface. The gap `1/(C+1)`, scalar bound `C`
and mass-factor bound `1+2C²` are uniform in the member, its stopping
radius, amplitude, charge and outer scale. Only the checked stopped ODE
and its uniform coefficient bound are supplied as inputs; no radial
reference equation or estimate is assumed. -/
theorem inner_radial_reference_of_stopped_solution
    {a rho C q : ℝ} {P : ℂ} (_ha : 0 < a) (hrho : 0 < rho)
    (_hrhoa : rho ≤ a⁻¹) (hC : 0 < C) (z : ℝ → ℝ × ℝ × ℂ)
    (hz : IsIntegralCurveOn z (staticInvRadiusRHS P q) (Icc a rho⁻¹))
    (hbox : ∀ x ∈ Icc a rho⁻¹, 0 < (z x).2.1 ∧ 0 < 1 - 2 * x * (z x).1 ∧
      ‖(x, z x)‖ + |(z x).2.1⁻¹| + |(1 - 2 * x * (z x).1)⁻¹| +
        ‖(P / ((2 * (z x).2.1 : ℝ) : ℂ)) * x‖ +
        |(2 * x * (z x).1 - q ^ 2 * x ^ 2) / (1 - 2 * x * (z x).1)| ≤ C) :
    let m := fun r : ℝ => (z r⁻¹).1
    let y := fun r : ℝ => -P / ((2 * r * (z r⁻¹).2.1 : ℝ) : ℂ)
    ContinuousOn y (Icc rho a⁻¹) ∧ ContinuousOn m (Icc rho a⁻¹) ∧
      (∀ r ∈ Icc rho a⁻¹, ‖y r‖ ≤ C ∧ 1 / (C + 1) ≤ 1 - 2 * m r / r ∧
        |1 - 2 * m r / r| ≤ 1 + 2 * C ^ 2) ∧
      ∀ r ∈ Ioo rho a⁻¹,
        let k := (2 * m r / r - q ^ 2 / r ^ 2) / (1 - 2 * m r / r)
        HasDerivAt y (((-(1 + k) / r : ℝ) : ℂ) * y r) r ∧
        HasDerivAt m ((1 - 2 * m r / r) * ‖y r‖ ^ 2 / 2 + q ^ 2 / (2 * r ^ 2)) r := by
  let m := fun r : ℝ => (z r⁻¹).1
  let y := fun r : ℝ => -P / ((2 * r * (z r⁻¹).2.1 : ℝ) : ℂ)
  have hpos (r : ℝ) (hr : r ∈ Icc rho a⁻¹) : 0 < r := hrho.trans_le hr.1
  have hinv (r : ℝ) (hr : r ∈ Icc rho a⁻¹) : r⁻¹ ∈ Icc a rho⁻¹ := by
    have hh := one_div_le_one_div_of_le (hpos r hr) hr.2
    have hh' := one_div_le_one_div_of_le hrho hr.1
    simpa only [one_div, inv_inv, mem_Icc] using And.intro hh hh'
  have cinv : ContinuousOn (fun r : ℝ => r⁻¹) (Icc rho a⁻¹) :=
    continuousOn_id.inv₀ (fun r hr => (hpos r hr).ne')
  have cz := hz.continuousOn.comp cinv hinv
  have cm : ContinuousOn m (Icc rho a⁻¹) := cz.fst
  have cl : ContinuousOn (fun r : ℝ => (z r⁻¹).2.1) (Icc rho a⁻¹) := cz.snd.fst
  have cy : ContinuousOn y (Icc rho a⁻¹) :=
    continuousOn_const.div
      (Complex.continuous_ofReal.comp_continuousOn
        ((continuousOn_const.mul continuousOn_id).mul cl))
      (fun r hr => Complex.ofReal_ne_zero.mpr
        (mul_ne_zero (mul_ne_zero (by norm_num) (hpos r hr).ne') (hbox _ (hinv r hr)).1.ne'))
  have hyid (r : ℝ) : y r = -((P / ((2 * (z r⁻¹).2.1 : ℝ) : ℂ)) * (r⁻¹ : ℝ)) := by
    simp [y, div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm]
  refine ⟨cy, cm, ?_, ?_⟩
  · intro r hr
    let x := r⁻¹
    have hh := hbox x (hinv r hr)
    have hn := norm_nonneg (x, z x)
    have hl := abs_nonneg (z x).2.1⁻¹
    have hg := abs_nonneg (1 - 2 * x * (z x).1)⁻¹
    have hy := norm_nonneg ((P / ((2 * (z x).2.1 : ℝ) : ℂ)) * x)
    have hk := abs_nonneg ((2 * x * (z x).1 - q ^ 2 * x ^ 2) / (1 - 2 * x * (z x).1))
    have hnorm : ‖(x, z x)‖ ≤ C := by linarith only [hh.2.2, hl, hg, hy, hk]
    have hxm : |x| ≤ C ∧ |(z x).1| ≤ C :=
      ⟨(norm_fst_le (x, z x)).trans hnorm,
        (norm_fst_le (z x)).trans ((norm_snd_le (x, z x)).trans hnorm)⟩
    have hginv : (1 - 2 * x * (z x).1)⁻¹ ≤ C :=
      (le_abs_self _).trans (by linarith only [hh.2.2, hn, hl, hy, hk])
    have hprod : 1 ≤ C * (1 - 2 * x * (z x).1) :=
      (div_le_iff₀ hh.2.1).mp (by simpa only [one_div] using hginv)
    have hgap : 1 / (C + 1) ≤ 1 - 2 * m r / r := by
      apply (div_le_iff₀ (by positivity : 0 < C + 1)).mpr
      have hid : 1 - 2 * m r / r = 1 - 2 * x * (z x).1 := by dsimp only [m, x]; ring
      rw [hid]
      nlinarith only [hprod, hh.2.1]
    have hmassfactor : |1 - 2 * m r / r| ≤ 1 + 2 * C ^ 2 := by
      calc
        _ = |1 - 2 * x * (z x).1| := by dsimp only [m, x]; congr 1; ring
        _ ≤ |1| + |2 * x * (z x).1| := abs_sub _ _
        _ = 1 + 2 * |x| * |(z x).1| := by rw [abs_mul, abs_mul]; norm_num
        _ ≤ 1 + 2 * C ^ 2 := by
          have hm := mul_le_mul hxm.1 hxm.2 (abs_nonneg _) hC.le
          nlinarith only [hm]
    refine ⟨?_, hgap, hmassfactor⟩
    change ‖y r‖ ≤ C
    rw [hyid, norm_neg]
    exact (show ‖(P / ((2 * (z x).2.1 : ℝ) : ℂ)) * x‖ ≤ C by
      linarith only [hh.2.2, hn, hl, hg, hk])
  · intro r hr
    have hr' := Ioo_subset_Icc_self hr
    have hri : r⁻¹ ∈ Ioo a rho⁻¹ := by
      have hleft := one_div_lt_one_div_of_lt (hpos r hr') hr.2
      have hright := one_div_lt_one_div_of_lt hrho hr.1
      simpa only [one_div, inv_inv, mem_Ioo] using And.intro hleft hright
    have hd := (hz _ (hinv r hr')).hasDerivAt (Icc_mem_nhds hri.1 hri.2)
    have hh := hbox _ (hinv r hr')
    have hradial := static_radial_equations_of_solution (hpos r hr') hd hh.1 hh.2.1
    exact ⟨hradial.2.2.1, hradial.2.1⟩

end EmcsfAcExtension.Global.Observation
