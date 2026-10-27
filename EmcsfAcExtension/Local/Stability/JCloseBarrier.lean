module

public import Mathlib

/-! # A damped real barrier with a possibly singular axis coefficient

The coefficient need not be integrable at the initial endpoint. Continuity
there and the ordinary interior equation suffice for the uniform barrier.
-/

public section

open Set

namespace EmcsfAcExtension.Local.Stab

/-- A real damped transport preserves an upper barrier, with exact constant
one. The nonnegative coefficient may be singular at the initial endpoint;
no integrability, derivative supremum, or positive lower cutoff is assumed. -/
theorem real_transport_le_barrier {T B : ℝ} {f p q : ℝ → ℝ} (hT : 0 < T)
    (hf : ContinuousOn f (Icc 0 T)) (h₀ : f 0 ≤ B)
    (hd : ∀ x ∈ Ioo 0 T, HasDerivAt f (-p x * f x + q x) x)
    (hp : ∀ x ∈ Ioo 0 T, 0 ≤ p x)
    (hq : ∀ x ∈ Ioo 0 T, q x ≤ p x * B) : ∀ t ∈ Icc 0 T, f t ≤ B := by
  intro t ht
  rcases ht.1.eq_or_lt with ht₀ | ht₀
  · simpa only [← ht₀] using h₀
  apply le_of_forall_pos_le_add
  intro ζ hζ
  let δ := ζ / (T + 1)
  have hδ : 0 < δ := div_pos hζ (by linarith only [hT])
  obtain ⟨r, hr, hfr⟩ := Metric.continuousWithinAt_iff.mp
    (hf 0 ⟨le_rfl, hT.le⟩) δ hδ
  let a := min (t / 2) (r / 2)
  have ha : 0 < a := lt_min (by linarith only [ht₀]) (by linarith only [hr])
  have hat : a < t := (min_le_left _ _).trans_lt (by linarith only [ht₀])
  have har : a < r := (min_le_right _ _).trans_lt (by linarith only [hr])
  have haf : f a < B + δ := by
    have h := hfr ⟨ha.le, hat.le.trans ht.2⟩
      (by simpa only [Real.dist_eq, sub_zero, abs_of_pos ha] using har)
    rw [Real.dist_eq] at h
    have hupper := (abs_lt.mp h).2
    linarith only [hupper, h₀]
  have hstart : f a ≤ B + δ * (a + 1) := by
    have hprod := mul_nonneg hδ.le ha.le
    nlinarith only [haf, hprod]
  have hbd (x : ℝ) : HasDerivAt (fun y => B + δ * (y + 1)) δ x := by
    simpa only [id_eq, mul_one] using!
      (((hasDerivAt_id x).add_const 1).const_mul δ).const_add B
  have hbound := image_le_of_deriv_right_lt_deriv_boundary
    (hf.mono (Icc_subset_Icc ha.le le_rfl))
    (fun x hx => (hd x ⟨ha.trans_le hx.1, hx.2⟩).hasDerivWithinAt)
    hstart hbd (fun x hx hxeq => by
      have hpx := hp x ⟨ha.trans_le hx.1, hx.2⟩
      have hqx := hq x ⟨ha.trans_le hx.1, hx.2⟩
      have hx0 : 0 ≤ x := ha.le.trans hx.1
      have hnonneg : 0 ≤ δ * (x + 1) := by positivity
      have hterm := mul_nonneg hpx hnonneg
      rw [hxeq]
      nlinarith only [hqx, hterm, hδ])
  have hft := hbound (x := t) ⟨hat.le, ht.2⟩
  have hδT : δ * (T + 1) = ζ := by dsimp only [δ]; field_simp
  have hinc := mul_le_mul_of_nonneg_left (add_le_add_right ht.2 1) hδ.le
  linarith only [hft, hinc, hδT]

/-- Two-sided real damped transport barrier with exact constant one.
It follows by applying the one-sided estimate to the function and its negative. -/
theorem abs_real_transport_le_barrier {T B : ℝ} {f p q : ℝ → ℝ} (hT : 0 < T)
    (hf : ContinuousOn f (Icc 0 T)) (h₀ : |f 0| ≤ B)
    (hd : ∀ x ∈ Ioo 0 T, HasDerivAt f (-p x * f x + q x) x)
    (hp : ∀ x ∈ Ioo 0 T, 0 ≤ p x)
    (hq : ∀ x ∈ Ioo 0 T, |q x| ≤ p x * B) : ∀ t ∈ Icc 0 T, |f t| ≤ B := by
  have hupper := real_transport_le_barrier hT hf (le_abs_self _ |>.trans h₀)
    hd hp (fun x hx => (le_abs_self _).trans (hq x hx))
  have hlower := real_transport_le_barrier (f := fun x => -f x) (q := fun x => -q x)
    hT hf.neg ((neg_le_abs _).trans h₀)
    (fun x hx => by convert (hd x hx).neg using 1; ring)
    hp (fun x hx => (neg_le_abs _).trans (hq x hx))
  intro t ht
  exact abs_le.mpr ⟨by linarith only [hlower t ht], hupper t ht⟩

end EmcsfAcExtension.Local.Stab
