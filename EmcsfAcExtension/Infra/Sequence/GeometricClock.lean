/- Copyright (c) 2026. All rights reserved. -/

module

public import Mathlib.Analysis.SpecificLimits.Basic
import EmcsfAcExtension.Infra.Sequence.EnergyRecurrence
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Tactic

/-!
# Geometric cylinder and connector clocks

Numerical support for `sec:charged-closure#total-boundary-clock`
(`charged_SF_new_version.tex:L4074`–L4079), consumed by `Global/Closure/Clock`.
The radii are `rho ^ n * b`, the cylinder durations are `H * radius / a n`,
and incoming connectors cost the radius difference. These results establish
no geometric realization, field recurrence, or stage existence.
The coefficients `rho`, `chi`, and `H` precede all sequence and cutoff data.
Every bound has its explicit constant, uniformly in the variations and cutoff.
-/

public section

open Finset Filter
open scoped Topology

namespace EmcsfAcExtension.Global

/-- [internal] One cylinder clock is dominated by a geometric sequence.
The factor is exactly `H * b / a₀`, with ratio `rho / chi`; it is uniform in
the envelope value `a` and stage `n`. Consumed by
`sec:charged-closure#total-boundary-clock`. -/
theorem stage_clock_le_of_geometric_le {rho chi H b a₀ a : ℝ}
    (hrho : 0 ≤ rho) (hchi : 0 < chi) (hH : 0 ≤ H) (hb : 0 ≤ b)
    (ha₀ : 0 < a₀) (n : ℕ) (ha : chi ^ n * a₀ ≤ a) :
    H * (rho ^ n * b) / a ≤ (H * b / a₀) * (rho / chi) ^ n := by
  calc
    _ ≤ H * (rho ^ n * b) / (chi ^ n * a₀) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) ha
    _ = _ := by
      rw [div_pow]
      field_simp

/-- [internal] Every finite collection of cylinder clocks has the source's
explicit bound. `rho`, `chi`, and `H` are fixed before `b`, `a₀`, `a`, and `N`.
The consumer supplies the geometric lower envelope, for example using
`geometric_le_of_le_recurrence`. Consumed by
`sec:charged-closure#total-boundary-clock`. -/
theorem sum_cylinder_clock_le_of_geometric_le {rho chi H : ℝ}
    (hrho : 0 ≤ rho) (hchi : 0 < chi) (hrc : rho < chi) (hH : 0 ≤ H)
    (b a₀ : ℝ) (a : ℕ → ℝ) (N : ℕ) (hb : 0 ≤ b) (ha₀ : 0 < a₀)
    (ha : ∀ n < N, chi ^ n * a₀ ≤ a n) :
    ∑ n ∈ range N, H * (rho ^ n * b) / a n ≤
      H * b / (a₀ * (1 - rho / chi)) := by
  have hratio : rho / chi < 1 := (div_lt_one hchi).mpr hrc
  have hgeom : ∑ n ∈ range N, (rho / chi) ^ n ≤ 1 / (1 - rho / chi) := by
    simpa only [Nat.Ico_zero_eq_range, pow_zero] using
      (geom_sum_Ico_le_of_lt_one (div_nonneg hrho hchi.le) hratio (m := 0) (n := N))
  calc
    _ ≤ ∑ n ∈ range N, (H * b / a₀) * (rho / chi) ^ n :=
      sum_le_sum fun n hn => stage_clock_le_of_geometric_le hrho hchi hH hb ha₀ n
        (ha n (mem_range.mp hn))
    _ = (H * b / a₀) * ∑ n ∈ range N, (rho / chi) ^ n := (mul_sum ..).symm
    _ ≤ (H * b / a₀) * (1 / (1 - rho / chi)) :=
      mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = _ := by rw [mul_one_div, div_div]

/-- [internal] Finite connector clocks telescope exactly, for any ratio and
initial radius. No constants are chosen. Consumed by
`sec:charged-closure#total-boundary-clock`. -/
theorem sum_connector_clock (rho b : ℝ) (N : ℕ) :
    ∑ n ∈ range N, (rho ^ n * b - rho ^ (n + 1) * b) = b - rho ^ N * b := by
  simpa only [pow_zero, one_mul] using sum_range_sub' (fun n => rho ^ n * b) N

/-- [internal] For a contracting nonnegative radius sequence, all connector
clocks sum to exactly the initial radius. No duration or energy parameter
enters this identity. Consumed by `sec:charged-closure#total-boundary-clock`. -/
theorem hasSum_connector_clock {rho : ℝ} (hrho : 0 ≤ rho) (hrho1 : rho < 1) (b : ℝ) :
    HasSum (fun n => rho ^ n * b - rho ^ (n + 1) * b) b := by
  have hg := summable_geometric_of_lt_one hrho hrho1
  have hs : Summable (fun n : ℕ => rho ^ n * b - rho ^ (n + 1) * b) := by
    simpa only [Function.comp_apply, Nat.succ_eq_add_one] using!
      (hg.mul_right b).sub ((hg.comp_injective Nat.succ_injective).mul_right b)
  have ht : Filter.Tendsto (fun N => ∑ n ∈ range N,
      (rho ^ n * b - rho ^ (n + 1) * b)) Filter.atTop (𝓝 b) := by
    simp_rw [sum_connector_clock]
    simpa only [zero_mul, sub_zero] using
      tendsto_const_nhds.sub ((tendsto_pow_atTop_nhds_zero_of_lt_one hrho hrho1).mul_const b)
  have heq := tendsto_nhds_unique hs.hasSum.tendsto_sum_nat ht
  simpa only [heq] using hs.hasSum

end EmcsfAcExtension.Global
