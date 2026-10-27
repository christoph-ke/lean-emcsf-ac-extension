/- Copyright (c) 2026. All rights reserved. -/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Finite energy recurrences and stage budgets

Numerical support for `eq:cc-recurrence` and `eq:cc-budget-sums`
(`charged_SF_new_version.tex:L3908`–L3929), to be consumed by `Global/Closure/StageSums`.
These results do not establish any field estimate or close a source node.
The recurrence and budget coefficients are fixed before the sequences and the
finite cutoff. All constants below are explicit; no choice of constants is used.
The hypotheses are needed only through the specified finite cutoff, so the
templates also apply to an unfinished last stage after its envelope is defined.
-/

public section

open Finset

namespace EmcsfAcExtension.Global

/-- [internal] A discrete subsolution with nonnegative terminal value has a
finite geometric budget, even for signed forcing and signed `q < 1`.
The coefficient `1 / (1 - q)` depends only on `q`, uniformly in both sequences
and the cutoff. Consumed by `eq:cc-budget-sums`. -/
theorem sum_le_of_le_recurrence {q : ℝ} (hq1 : q < 1)
    (a f : ℕ → ℝ) (N : ℕ) (ha : 0 ≤ a N)
    (hrec : ∀ n < N, a (n + 1) ≤ q * a n + f n) :
    ∑ n ∈ range N, a n ≤ (a 0 + ∑ n ∈ range N, f n) / (1 - q) := by
  have htel : ∑ n ∈ range N, (a (n + 1) - a n) = a N - a 0 :=
    sum_range_sub a N
  have hsum : a N - a 0 ≤
      (q - 1) * (∑ n ∈ range N, a n) + ∑ n ∈ range N, f n := by
    rw [← htel, mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro n hn
    have h := hrec n (mem_range.mp hn)
    linarith only [h]
  apply (le_div_iff₀ (sub_pos.mpr hq1)).mpr
  nlinarith only [hsum, ha]

/-- [internal] A nonnegative forcing preserves the geometric lower envelope.
There is no constant beyond the displayed power of `q`. Consumed by
`eq:cc-recurrence` and `sec:charged-closure#total-boundary-clock`. -/
theorem geometric_le_of_le_recurrence {q : ℝ} (hq : 0 ≤ q)
    (a : ℕ → ℝ) (N : ℕ)
    (hrec : ∀ n < N, q * a n ≤ a (n + 1)) :
    ∀ n ≤ N, q ^ n * a 0 ≤ a n := by
  intro n hn
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      q ^ (n + 1) * a 0 = q * (q ^ n * a 0) := by ring
      _ ≤ q * a n := mul_le_mul_of_nonneg_left (ih (by omega)) hq
      _ ≤ a (n + 1) := hrec n (by omega)

/-- [internal] Square roots turn quadratic forcing into linear forcing.
The constants are exactly `sqrt q` and `sqrt C`, independent of the values
`a`, `b`, and `s`. Consumed by the square-root half of `eq:cc-budget-sums`. -/
theorem sqrt_le_of_le_quadratic {q C a b s : ℝ} (hq : 0 ≤ q) (hC : 0 ≤ C)
    (ha : 0 ≤ a) (hs : 0 ≤ s) (hb : b ≤ q * a + C * s ^ 2) :
    Real.sqrt b ≤ Real.sqrt q * Real.sqrt a + Real.sqrt C * s := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hqa := Real.sq_sqrt hq
    have haa := Real.sq_sqrt ha
    have hCC := Real.sq_sqrt hC
    have hcross : 0 ≤ (Real.sqrt q * Real.sqrt a) * (Real.sqrt C * s) := by
      positivity
    nlinarith only [hb, hqa, haa, hCC, hcross]

/-- [internal] Explicit finite sum bounds for energy envelopes driven by squared
nonnegative variation. The denominators depend only on `q`; the forcing
coefficient is `C`, both fixed before `a`, `s`, and `N`.
Consumed by `eq:cc-budget-sums`, including its partial-stage application. -/
theorem energy_sums_le_of_le_recurrence {q C : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (hC : 0 ≤ C) (a s : ℕ → ℝ) (N : ℕ) (ha : ∀ n ≤ N, 0 ≤ a n)
    (hs : ∀ n < N, 0 ≤ s n)
    (hrec : ∀ n < N, a (n + 1) ≤ q * a n + C * s n ^ 2) :
    (∑ n ∈ range N, a n) ≤
        (a 0 + C * (∑ n ∈ range N, s n) ^ 2) / (1 - q) ∧
      (∑ n ∈ range N, Real.sqrt (a n)) ≤
        (Real.sqrt (a 0) + Real.sqrt C * (∑ n ∈ range N, s n)) /
          (1 - Real.sqrt q) := by
  constructor
  · have h := sum_le_of_le_recurrence hq1 a (fun n => C * s n ^ 2) N (ha N le_rfl) hrec
    rw [← mul_sum] at h
    exact h.trans (div_le_div_of_nonneg_right
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (sum_sq_le_sq_sum_of_nonneg (fun n hn => hs n (mem_range.mp hn))) hC))
      (sub_nonneg.mpr hq1.le))
  · have hroot : Real.sqrt q < 1 := by
      simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt hq hq1
    have h := sum_le_of_le_recurrence hroot
      (fun n => Real.sqrt (a n)) (fun n => Real.sqrt C * s n) N
      (Real.sqrt_nonneg _)
      (fun n hn => sqrt_le_of_le_quadratic hq hC (ha n (by omega)) (hs n hn) (hrec n hn))
    simpa only [← mul_sum] using h

/-- [internal] Explicit finite stage-budget bounds. `K`, `C`, and `q` are fixed
before every sequence and cutoff. A consumer supplies its cooling/connector
budgets `e n ≤ K * (a n + s n ^ 2)`. Consumed by `eq:cc-budget-sums`;
this abstract implication does not prove that field budgets satisfy the premise. -/
theorem budget_sums_le_of_le_recurrence {q C K : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (a s e : ℕ → ℝ) (N : ℕ)
    (ha : ∀ n ≤ N, 0 ≤ a n) (hs : ∀ n < N, 0 ≤ s n)
    (hrec : ∀ n < N, a (n + 1) ≤ q * a n + C * s n ^ 2)
    (he : ∀ n < N, e n ≤ K * (a n + s n ^ 2)) :
    (∑ n ∈ range N, e n) ≤ K *
        ((a 0 + C * (∑ n ∈ range N, s n) ^ 2) / (1 - q) +
          (∑ n ∈ range N, s n) ^ 2) ∧
      (∑ n ∈ range N, Real.sqrt (e n)) ≤ Real.sqrt K *
        ((Real.sqrt (a 0) + Real.sqrt C * (∑ n ∈ range N, s n)) /
          (1 - Real.sqrt q) + ∑ n ∈ range N, s n) := by
  obtain ⟨hea, her⟩ := energy_sums_le_of_le_recurrence hq hq1 hC a s N ha hs hrec
  have hsq : ∑ n ∈ range N, s n ^ 2 ≤ (∑ n ∈ range N, s n) ^ 2 :=
    sum_sq_le_sq_sum_of_nonneg (fun n hn => hs n (mem_range.mp hn))
  constructor
  · calc
      ∑ n ∈ range N, e n ≤ ∑ n ∈ range N, K * (a n + s n ^ 2) :=
        sum_le_sum fun n hn => he n (mem_range.mp hn)
      _ = K * ((∑ n ∈ range N, a n) + ∑ n ∈ range N, s n ^ 2) := by
        rw [← mul_sum, sum_add_distrib]
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hea hsq) hK
  · calc
      ∑ n ∈ range N, Real.sqrt (e n) ≤
          ∑ n ∈ range N, (Real.sqrt K * Real.sqrt (a n) + Real.sqrt K * s n) := by
        apply sum_le_sum
        intro n hn
        apply sqrt_le_of_le_quadratic hK hK (ha n (by have := mem_range.mp hn; omega))
          (hs n (mem_range.mp hn))
        simpa only [mul_add] using he n (mem_range.mp hn)
      _ = Real.sqrt K * ((∑ n ∈ range N, Real.sqrt (a n)) + ∑ n ∈ range N, s n) := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum, mul_add]
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add her le_rfl) (Real.sqrt_nonneg _)

/-- [internal] One positive budget constant, chosen before the variation
sequence, energy sequence, budgets, and cutoff. An explicit witness is
`1 + K * (1 + C) / (1 - q) + sqrt K * (1 + sqrt C) / (1 - sqrt q)`;
it depends only on the fixed coefficients `q`, `C`, and `K`.
Consumed by `eq:cc-budget-sums`. -/
theorem exists_budget_constant_of_lt_one {q C K : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (hC : 0 ≤ C) (hK : 0 ≤ K) :
    ∃ B > 0, ∀ (a s e : ℕ → ℝ) (N : ℕ),
      (∀ n ≤ N, 0 ≤ a n) → (∀ n < N, 0 ≤ s n) →
      (∀ n < N, a (n + 1) ≤ q * a n + C * s n ^ 2) →
      (∀ n < N, e n ≤ K * (a n + s n ^ 2)) →
      (∑ n ∈ range N, e n) ≤ B * (a 0 + (∑ n ∈ range N, s n) ^ 2) ∧
        (∑ n ∈ range N, Real.sqrt (e n)) ≤
          B * (Real.sqrt (a 0) + ∑ n ∈ range N, s n) := by
  let E := K * (1 + C) / (1 - q)
  let R := Real.sqrt K * (1 + Real.sqrt C) / (1 - Real.sqrt q)
  have hd : 0 < 1 - q := sub_pos.mpr hq1
  have hr : Real.sqrt q < 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt hq hq1
  have hdr : 0 < 1 - Real.sqrt q := sub_pos.mpr hr
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  refine ⟨1 + E + R, by positivity, ?_⟩
  intro a s e N ha hs hrec he
  obtain ⟨henergy, hroot⟩ := budget_sums_le_of_le_recurrence hq hq1 hC hK a s e N ha hs hrec he
  let S := ∑ n ∈ range N, s n
  have hS : 0 ≤ S := sum_nonneg fun n hn => hs n (mem_range.mp hn)
  have ha₀ := ha 0 (Nat.zero_le N)
  have hecoeff : (a 0 + C * S ^ 2) / (1 - q) + S ^ 2 ≤
      ((1 + C) / (1 - q)) * (a 0 + S ^ 2) := by
    apply (mul_le_mul_iff_of_pos_right hd).mp
    field_simp
    nlinarith only [mul_nonneg hC ha₀, mul_nonneg hq (sq_nonneg S)]
  have hrcoeff : (Real.sqrt (a 0) + Real.sqrt C * S) / (1 - Real.sqrt q) + S ≤
      ((1 + Real.sqrt C) / (1 - Real.sqrt q)) * (Real.sqrt (a 0) + S) := by
    apply (mul_le_mul_iff_of_pos_right hdr).mp
    field_simp
    nlinarith only [mul_nonneg (Real.sqrt_nonneg C) (Real.sqrt_nonneg (a 0)),
      mul_nonneg (Real.sqrt_nonneg q) hS]
  constructor
  · calc
      _ ≤ K * ((a 0 + C * S ^ 2) / (1 - q) + S ^ 2) := henergy
      _ ≤ E * (a 0 + S ^ 2) := by
        simpa only [E, div_eq_mul_inv, mul_assoc] using mul_le_mul_of_nonneg_left hecoeff hK
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hR]) (add_nonneg ha₀ (sq_nonneg S))
  · calc
      _ ≤ Real.sqrt K *
          ((Real.sqrt (a 0) + Real.sqrt C * S) / (1 - Real.sqrt q) + S) := hroot
      _ ≤ R * (Real.sqrt (a 0) + S) := by
        simpa only [R, div_eq_mul_inv, mul_assoc] using
          mul_le_mul_of_nonneg_left hrcoeff (Real.sqrt_nonneg K)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hE])
        (add_nonneg (Real.sqrt_nonneg _) hS)

end EmcsfAcExtension.Global
