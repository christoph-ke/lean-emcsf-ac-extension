module

public import EmcsfAcExtension.Local.Defs.Setting

/-! # Borel extension of the common geometric source

Each continuous classical field is first extended by zero outside the
triangle. The literal totalized source of these extensions is zero there,
so it is a pointwise measurable representative on the full label plane.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The actual common geometric source, extended by zero, is Borel.
No source integrability, derivative supremum, estimate constant or
smallness condition is assumed.
-/
theorem stab_geomSource_borel_c1 {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) :
    Measurable ((triangle 0 T).indicator (Function.uncurry (geomSource S))) := by
  classical
  let D := triangle 0 T
  let R := D.indicator (Function.uncurry S.r)
  let L := D.indicator (Function.uncurry S.lam)
  let N := D.indicator (Function.uncurry S.nu)
  let m := D.indicator (Function.uncurry S.m)
  let Q := D.indicator (Function.uncurry S.Q)
  let X := D.indicator (Function.uncurry S.theta)
  let Y := D.indicator (Function.uncurry S.xi)
  have hR : Measurable R :=
    hset.c1.c1_r.continuousOn.measurable_piecewise continuousOn_const
      (measurableSet_triangle 0 T)
  have hL : Measurable L :=
    hset.c1.c1_lam.continuousOn.measurable_piecewise continuousOn_const
      (measurableSet_triangle 0 T)
  have hN : Measurable N :=
    hset.c1.c1_nu.continuousOn.measurable_piecewise continuousOn_const
      (measurableSet_triangle 0 T)
  have hm : Measurable m :=
    hset.c1.c1_m.continuousOn.measurable_piecewise continuousOn_const
      (measurableSet_triangle 0 T)
  have hQ : Measurable Q :=
    hset.c1.c1_Q.continuousOn.measurable_piecewise continuousOn_const
      (measurableSet_triangle 0 T)
  have hX : Measurable X :=
    hset.c1.c1_theta.continuousOn.measurable_piecewise continuousOn_const
      (measurableSet_triangle 0 T)
  have hY : Measurable Y :=
    hset.c1.c1_xi.continuousOn.measurable_piecewise continuousOn_const
      (measurableSet_triangle 0 T)
  let U := fun p : ℝ × ℝ => 2 * m p / R p
  let C := fun p : ℝ × ℝ => (U p : ℂ) + ((1 - U p : ℝ) : ℂ) * X p *
    starRingEnd ℂ (Y p) / ((L p * N p : ℝ) : ℂ)
  let Z := fun p : ℝ × ℝ => -(2 * N p * L p / ((1 - U p) * R p ^ 2)) *
    ((C p).re - 2 * (Q p ^ 2 / R p ^ 2))
  have hZ : Measurable Z := by
    dsimp only [Z, C, U]
    fun_prop
  convert hZ using 1
  funext p
  symm
  by_cases hp : p ∈ D
  · change p ∈ triangle 0 T at hp
    simp only [Z, C, U, R, L, N, m, Q, X, Y, D, indicator_of_mem hp,
      geomSource, curv, Fields.mu, Function.uncurry_def, Complex.ofReal_mul,
      Complex.ofReal_sub, Complex.ofReal_one]
  · have hz : Z p = 0 := by
      simp only [Z, R, L, N, Q, indicator_of_notMem hp,
        zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0), div_zero,
        neg_zero]
    rw [hz]
    exact (indicator_of_notMem hp _).symm

end EmcsfAcExtension.Local
