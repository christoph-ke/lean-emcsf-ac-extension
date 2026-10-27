module

public import EmcsfAcExtension.Frozen.IntegralForm
public import EmcsfAcExtension.Local.Broad.AxisUniquenessSmallness

/-! # Uniqueness for a two-direction characteristic integral system

An exponential weight closes the finite rectangle comparison directly.
This is the ordinary bounded-coefficient Volterra argument used away
from the axis; it does not assume a scalar subsystem is closed.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local.Broad

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An exponential majorant integrates with cost `K/k`. All constants
are explicit and uniform in the trace and interval. -/
theorem norm_integral_le_exponential_of_bound {a x y k K B : ℝ} {f : ℝ → E}
    (hax : a ≤ x) (hk : 0 < k) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hf : ∀ z ∈ Ioc a x, ‖f z‖ ≤ K * B * Real.exp (k * (z - a + y))) :
    ‖∫ z in a..x, f z‖ ≤ (K / k) * B * Real.exp (k * (x - a + y)) := by
  have cp : Continuous (fun z : ℝ => Real.exp (k * (z - a + y))) := by fun_prop
  have hd z : HasDerivAt (fun z : ℝ => Real.exp (k * (z - a + y)) / k)
      (Real.exp (k * (z - a + y))) z := by
    apply (((((hasDerivAt_id z).sub_const a).add_const y).const_mul k).exp.div_const k).congr_deriv
    simp only [id_eq, mul_one]
    field_simp [hk.ne']
  have hprimitive := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hax
    (cp.div_const k).continuousOn (fun z _ => hd z) (cp.intervalIntegrable a x)
  have hi : (∫ z in a..x, Real.exp (k * (z - a + y))) ≤
      Real.exp (k * (x - a + y)) / k := by
    rw [hprimitive]
    exact sub_le_self _ (div_nonneg (Real.exp_pos _).le hk.le)
  have hm := intervalIntegral.norm_integral_le_of_norm_le (f := f)
    (g := fun z => K * B * Real.exp (k * (z - a + y))) hax
    (Filter.Eventually.of_forall (fun z hz => hf z hz))
    ((cp.intervalIntegrable (μ := volume) a x).const_mul (K * B))
  refine hm.trans ?_
  rw [intervalIntegral.integral_const_mul]
  exact (mul_le_mul_of_nonneg_left hi (mul_nonneg hK hB)).trans_eq (by ring)

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

/-- A continuous full characteristic state is unique on a finite rectangle
when both directional source differences are bounded by `K` times the
full state difference and the entering components agree. The coefficient
`K` is fixed before the interval and traces; no small rectangle is needed. -/
theorem rectangle_integral_uniqueness_of_source_bound
    {a b c d K : ℝ} {f₁ f₂ : ℝ × ℝ → X × Y}
    {g₁ g₂ : ℝ × ℝ → X} {h₁ h₂ : ℝ × ℝ → Y}
    (hab : a ≤ b) (hcd : c ≤ d) (hK : 0 ≤ K)
    (cf₁ : ContinuousOn f₁ (Icc a b ×ˢ Icc c d))
    (cf₂ : ContinuousOn f₂ (Icc a b ×ˢ Icc c d))
    (hi₁ : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      IntegralForm (fun x => (f₁ (x, v)).1) (fun x => g₁ (x, v)) a u)
    (hi₂ : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      IntegralForm (fun x => (f₂ (x, v)).1) (fun x => g₂ (x, v)) a u)
    (ho₁ : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      IntegralForm (fun y => (f₁ (u, y)).2) (fun y => h₁ (u, y)) c v)
    (ho₂ : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      IntegralForm (fun y => (f₂ (u, y)).2) (fun y => h₂ (u, y)) c v)
    (hg : ∀ p ∈ Icc a b ×ˢ Icc c d, ‖g₁ p - g₂ p‖ ≤ K * ‖f₁ p - f₂ p‖)
    (hh : ∀ p ∈ Icc a b ×ˢ Icc c d, ‖h₁ p - h₂ p‖ ≤ K * ‖f₁ p - f₂ p‖)
    (he₁ : ∀ v ∈ Icc c d, (f₁ (a, v)).1 = (f₂ (a, v)).1)
    (he₂ : ∀ u ∈ Icc a b, (f₁ (u, c)).2 = (f₂ (u, c)).2) :
    Set.EqOn f₁ f₂ (Icc a b ×ˢ Icc c d) := by
  let k := 2 * K + 1
  have hk : 0 < k := by dsimp [k]; linarith
  let w := fun p : ℝ × ℝ => Real.exp (-(k * (p.1 - a + (p.2 - c)))) * ‖f₁ p - f₂ p‖
  have cw : ContinuousOn w (Icc a b ×ˢ Icc c d) := by
    apply ContinuousOn.mul _ (cf₁.sub cf₂).norm
    exact (by fun_prop : Continuous (fun p : ℝ × ℝ =>
      Real.exp (-(k * (p.1 - a + (p.2 - c)))))).continuousOn
  obtain ⟨p₀, hp₀, hmax⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn
    ⟨(a, c), ⟨le_rfl, hab⟩, le_rfl, hcd⟩ cw
  let B := w p₀
  have hB : 0 ≤ B := mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  have hbound p (hp : p ∈ Icc a b ×ˢ Icc c d) :
      ‖f₁ p - f₂ p‖ ≤ B * Real.exp (k * (p.1 - a + (p.2 - c))) := by
    have hm := hmax hp
    change Real.exp (-(k * (p.1 - a + (p.2 - c)))) * ‖f₁ p - f₂ p‖ ≤ B at hm
    rw [Real.exp_neg] at hm
    apply (div_le_iff₀ (Real.exp_pos _)).mp
    simpa only [div_eq_mul_inv, mul_comm] using hm
  have hb₁ u (hu : u ∈ Icc a b) v (hv : v ∈ Icc c d) :
      ‖(f₁ (u, v)).1 - (f₂ (u, v)).1‖ ≤
        (K / k) * B * Real.exp (k * (u - a + (v - c))) := by
    have heq : (f₁ (u, v)).1 - (f₂ (u, v)).1 =
        ∫ x in a..u, g₁ (x, v) - g₂ (x, v) := by
      rw [intervalIntegral.integral_sub (hi₁ u hu v hv).1 (hi₂ u hu v hv).1,
        ← (hi₁ u hu v hv).2, ← (hi₂ u hu v hv).2]
      change _ = ((f₁ (u, v)).1 - (f₁ (a, v)).1) -
        ((f₂ (u, v)).1 - (f₂ (a, v)).1)
      rw [he₁ v hv]
      abel
    rw [heq]
    apply norm_integral_le_exponential_of_bound hu.1 hk hK hB
    intro x hx
    have hp : (x, v) ∈ Icc a b ×ˢ Icc c d := ⟨⟨hx.1.le, hx.2.trans hu.2⟩, hv⟩
    exact (hg (x, v) hp).trans
      ((mul_le_mul_of_nonneg_left (hbound (x, v) hp) hK).trans_eq (by ring))
  have hb₂ u (hu : u ∈ Icc a b) v (hv : v ∈ Icc c d) :
      ‖(f₁ (u, v)).2 - (f₂ (u, v)).2‖ ≤
        (K / k) * B * Real.exp (k * (u - a + (v - c))) := by
    have heq : (f₁ (u, v)).2 - (f₂ (u, v)).2 =
        ∫ y in c..v, h₁ (u, y) - h₂ (u, y) := by
      rw [intervalIntegral.integral_sub (ho₁ u hu v hv).1 (ho₂ u hu v hv).1,
        ← (ho₁ u hu v hv).2, ← (ho₂ u hu v hv).2]
      change _ = ((f₁ (u, v)).2 - (f₁ (u, c)).2) -
        ((f₂ (u, v)).2 - (f₂ (u, c)).2)
      rw [he₂ u hu]
      abel
    rw [heq]
    have hb := norm_integral_le_exponential_of_bound hv.1 hk hK hB (y := u - a)
      (f := fun y => h₁ (u, y) - h₂ (u, y)) (fun y hy => by
        have hp : (u, y) ∈ Icc a b ×ˢ Icc c d := ⟨hu, hy.1.le, hy.2.trans hv.2⟩
        apply (hh (u, y) hp).trans
        rw [show y - c + (u - a) = u - a + (y - c) by ring]
        exact (mul_le_mul_of_nonneg_left (hbound (u, y) hp) hK).trans_eq (by ring))
    rw [show v - c + (u - a) = u - a + (v - c) by ring] at hb
    exact hb
  have hfull : ‖f₁ p₀ - f₂ p₀‖ ≤
      (K / k) * B * Real.exp (k * (p₀.1 - a + (p₀.2 - c))) :=
    max_le (hb₁ p₀.1 hp₀.1 p₀.2 hp₀.2) (hb₂ p₀.1 hp₀.1 p₀.2 hp₀.2)
  have hself : B ≤ (K / k) * B := by
    have hm := mul_le_mul_of_nonneg_left hfull
      (Real.exp_pos (-(k * (p₀.1 - a + (p₀.2 - c))))).le
    apply hm.trans_eq
    rw [Real.exp_neg]
    field_simp
  have hratio : K / k < 1 := (div_lt_one hk).mpr (by dsimp [k]; linarith)
  have hB0 := eq_zero_of_strict_self_contraction hB hratio hself
  intro p hp
  have hh := hbound p hp
  rw [hB0, zero_mul] at hh
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))

end EmcsfAcExtension.Local.Broad
