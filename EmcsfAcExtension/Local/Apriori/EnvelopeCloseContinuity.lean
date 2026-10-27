module

public import Mathlib

/-! # Simultaneous continuity closure of two characteristic budgets

The growing-triangle argument in approved internal project record (20)–(22)
requires continuity in the apex coordinate. The elementary barrier lemma
below rules out crossing either bootstrap boundary simultaneously.
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- Continuous budgets that strictly improve both closed barriers cannot
cross either barrier. All thresholds are explicit parameters; the assertion
is uniform in the functions and in the length of the interval. -/
theorem coupled_bounds_of_strict_improvement {T A B : ℝ} {X Y : ℝ → ℝ}
    (hX : ContinuousOn X (Icc 0 T))
    (hY : ContinuousOn Y (Icc 0 T)) (hX0 : X 0 < A) (hY0 : Y 0 < B)
    (hstep : ∀ s ∈ Icc 0 T, X s ≤ A → Y s ≤ B → X s < A ∧ Y s < B) :
    ∀ s ∈ Icc 0 T, X s < A ∧ Y s < B := by
  let Z : ℝ → ℝ := fun s => max (X s - A) (Y s - B)
  have hZ : ContinuousOn Z (Icc 0 T) :=
    (hX.sub continuousOn_const).sup (hY.sub continuousOn_const)
  have hZ0 : Z 0 < 0 := max_lt (sub_neg.mpr hX0) (sub_neg.mpr hY0)
  intro s hs
  have hneg : Z s < 0 := by
    by_contra hn
    have hcross := intermediate_value_Icc hs.1
      (hZ.mono (Icc_subset_Icc le_rfl hs.2))
      (show (0 : ℝ) ∈ Icc (Z 0) (Z s) from ⟨hZ0.le, not_lt.mp hn⟩)
    obtain ⟨t, ht, hzero⟩ := hcross
    have htT : t ∈ Icc 0 T := ⟨ht.1, ht.2.trans hs.2⟩
    have hclosed : X t ≤ A ∧ Y t ≤ B := by
      have hz : max (X t - A) (Y t - B) ≤ 0 := le_of_eq hzero
      exact ⟨sub_nonpos.mp ((le_max_left _ _).trans hz),
        sub_nonpos.mp ((le_max_right _ _).trans hz)⟩
    obtain ⟨hx, hy⟩ := hstep t htT hclosed.1 hclosed.2
    have hz : Z t < 0 := max_lt (sub_neg.mpr hx) (sub_neg.mpr hy)
    exact (ne_of_lt hz) hzero
  exact ⟨sub_neg.mp ((le_max_left _ _).trans_lt hneg),
    sub_neg.mp ((le_max_right _ _).trans_lt hneg)⟩

/-- The two envelope inequalities strictly improve the simultaneous box
`X ≤ 2ε`, `Y ≤ 3ε` under explicit dimensionless smallness margins.
The coefficient `A` is arbitrary and is chosen before `ε`, `δ`, `X`, and `Y`.
This is the scalar algebra in approved internal project record (20)–(22), allowing
any enlarged area coefficient in place of its sample coefficient. -/
theorem coupled_envelope_improvement {A ε δ X Y : ℝ}
    (hA : 0 ≤ A) (hε : 0 < ε) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hsmall : A * ε ^ 2 ≤ 1 / 1000) (hcharged : A * δ ^ 2 ≤ 1 / 1000)
    (hXb : X ≤ 2 * ε) (hYb : Y ≤ 3 * ε)
    (hj : X ≤ Real.exp (A * ε * Y) *
      (ε + A * ε ^ 3 + A * ε * X * Y + A * δ ^ 2 * ε))
    (hk : Y ≤ X + A * ε * X * Y + A * δ ^ 2 * ε) :
    X ≤ 33 / 32 * ε ∧ Y ≤ 9 / 8 * ε := by
  have hε0 := hε.le
  have hexponent : A * ε * Y ≤ 3 / 1000 := by
    calc
      _ ≤ A * ε * (3 * ε) :=
        mul_le_mul_of_nonneg_left hYb (mul_nonneg hA hε0)
      _ = 3 * (A * ε ^ 2) := by ring
      _ ≤ _ := by linarith only [hsmall]
  have hexp : Real.exp (A * ε * Y) ≤ 1000 / 997 := by
    apply (Real.exp_le_exp.mpr hexponent).trans
    have he := Real.exp_bound_div_one_sub_of_interval
      (by norm_num : (0 : ℝ) ≤ 3 / 1000) (by norm_num : (3 : ℝ) / 1000 < 1)
    norm_num at he ⊢
    exact he
  have hcubic : A * ε ^ 3 ≤ 1 / 1000 * ε := by
    convert mul_le_mul_of_nonneg_right hsmall hε0 using 1
    ring
  have helectric : A * δ ^ 2 * ε ≤ 1 / 1000 * ε :=
    mul_le_mul_of_nonneg_right hcharged hε0
  have hcross : A * ε * X * Y ≤ 6 / 1000 * ε := by
    calc
      _ ≤ A * ε * (2 * ε) * (3 * ε) := by gcongr
      _ = 6 * (A * ε ^ 2) * ε := by ring
      _ ≤ _ := by
        have hi := mul_le_mul_of_nonneg_right hsmall hε0
        linarith only [hi]
  have hbracket : ε + A * ε ^ 3 + A * ε * X * Y + A * δ ^ 2 * ε ≤
      1008 / 1000 * ε := by
    linarith only [hcubic, hcross, helectric]
  have hXi : X ≤ 33 / 32 * ε := by
    apply hj.trans
    calc
      _ ≤ (1000 / 997) * (1008 / 1000 * ε) :=
        mul_le_mul hexp hbracket (by positivity) (by norm_num)
      _ ≤ _ := by linarith only [hε0]
  have hYi : Y ≤ 9 / 8 * ε := by
    linarith only [hk, hXi, hcross, helectric, hε0]
  exact ⟨hXi, hYi⟩

/-- Continuous finite budgets obeying the coupled characteristic inequalities
remain on their small branch, including zero variation. The coefficient `A`
is fixed before all data. This is an analytic helper; the field-level node
must supply continuity and both transport inequalities itself. -/
theorem coupled_envelopes_le_of_continuous {A ε δ T : ℝ} {X Y : ℝ → ℝ}
    (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (hsmall : A * ε ^ 2 ≤ 1 / 1000) (hcharged : A * δ ^ 2 ≤ 1 / 1000)
    (hX : ContinuousOn X (Icc 0 T)) (hY : ContinuousOn Y (Icc 0 T))
    (hX0 : X 0 = 0) (hY0 : Y 0 = 0)
    (hXn : ∀ s ∈ Icc 0 T, 0 ≤ X s) (hYn : ∀ s ∈ Icc 0 T, 0 ≤ Y s)
    (hj : ∀ s ∈ Icc 0 T, X s ≤ Real.exp (A * ε * Y s) *
      (ε + A * ε ^ 3 + A * ε * X s * Y s + A * δ ^ 2 * ε))
    (hk : ∀ s ∈ Icc 0 T, Y s ≤ X s + A * ε * X s * Y s + A * δ ^ 2 * ε) :
    ∀ s ∈ Icc 0 T, X s ≤ 9 / 8 * ε ∧ Y s ≤ 9 / 8 * ε := by
  rcases eq_or_lt_of_le hε with hzero | hpos
  · subst ε
    intro s hs
    have hx : X s ≤ 0 := by simpa using hj s hs
    have hy : Y s ≤ X s := by simpa using hk s hs
    constructor <;> simp only [mul_zero] <;> linarith only [hx, hy]
  · have hbar := coupled_bounds_of_strict_improvement hX hY
      (by rw [hX0]; positivity : X 0 < 2 * ε)
      (by rw [hY0]; positivity : Y 0 < 3 * ε) (fun s hs hxb hyb => by
        have hi := coupled_envelope_improvement hA hpos (hXn s hs) (hYn s hs)
          hsmall hcharged hxb hyb (hj s hs) (hk s hs)
        constructor <;> linarith only [hi.1, hi.2, hpos])
    intro s hs
    have hi := coupled_envelope_improvement hA hpos (hXn s hs) (hYn s hs)
      hsmall hcharged (hbar s hs).1.le (hbar s hs).2.le (hj s hs) (hk s hs)
    exact ⟨hi.1.trans (by linarith only [hε]), hi.2⟩

end EmcsfAcExtension.Local
