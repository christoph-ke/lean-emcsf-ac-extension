module

public import Mathlib
import EmcsfAcExtension.Local.Broad.RectangleVolterra

/-! # Uniform first-jet comparison for continuation strips

The transverse Volterra equations are compared to the old lower edge.
The estimates involve the old first-jet bound and a modulus of the
fixed entering datum, with no old second derivative.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

section Volterra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- A continuous Volterra inequality has an explicit exponential bound.
`K,ε` precede the interval and functions; the coefficient is uniform in
all contained endpoints. The density needs only the displayed bound. -/
theorem norm_le_of_volterra_integral_bound
    {a b K ε : ℝ} {w g : ℝ → E} (hab : a ≤ b) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hw : ContinuousOn w (Icc a b))
    (hineq : ∀ x ∈ Icc a b, ‖w x‖ ≤ ε + ‖∫ s in a..x, g s‖)
    (hg : ∀ x ∈ Icc a b, ‖g x‖ ≤ K * ‖w x‖) :
    ∀ x ∈ Icc a b, ‖w x‖ ≤ 2*ε*Real.exp ((2*(K+1))*(x-a)) := by
  let k := 2*(K+1)
  have hk : 0 < k := by dsimp [k]; linarith
  let q := fun x : ℝ => Real.exp (-(k*(x-a)))*‖w x‖
  have hq : ContinuousOn q (Icc a b) :=
    (by fun_prop : Continuous (fun x : ℝ => Real.exp (-(k*(x-a))))).continuousOn.mul hw.norm
  obtain ⟨x₀, hx₀, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨a, le_rfl, hab⟩ hq
  let M := q x₀
  have hM : 0 ≤ M := mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  have hbound x (hx : x ∈ Icc a b) : ‖w x‖ ≤ M*Real.exp (k*(x-a)) := by
    have hm := hmax hx
    change Real.exp (-(k*(x-a)))*‖w x‖ ≤ M at hm
    rw [Real.exp_neg] at hm
    apply (div_le_iff₀ (Real.exp_pos _)).mp
    simpa only [div_eq_mul_inv, mul_comm] using hm
  have hint x (hx : x ∈ Icc a b) :
      ‖∫ s in a..x, g s‖ ≤ (K/k)*M*Real.exp (k*(x-a)) := by
    have he := Broad.norm_integral_le_exponential_of_bound hx.1 hk hK hM
      (y := 0) (f := g) (fun s hs => by
        have hs' : s ∈ Icc a b := ⟨hs.1.le, hs.2.trans hx.2⟩
        simp only [add_zero]
        exact (hg s hs').trans
          ((mul_le_mul_of_nonneg_left (hbound s hs') hK).trans_eq (by ring)))
    simpa only [add_zero] using he
  have hεexp x (hx : x ∈ Icc a b) : ε ≤ ε*Real.exp (k*(x-a)) := by
    simpa using mul_le_mul_of_nonneg_left
      (Real.one_le_exp (mul_nonneg hk.le (sub_nonneg.mpr hx.1))) hε
  have hself : M ≤ ε+(K/k)*M := by
    have h := (hineq x₀ hx₀).trans (add_le_add (hεexp x₀ hx₀) (hint x₀ hx₀))
    have hm := mul_le_mul_of_nonneg_left h (Real.exp_pos (-(k*(x₀-a)))).le
    apply hm.trans_eq
    dsimp only [M, q]
    rw [Real.exp_neg]
    field_simp
  have hratio : K/k ≤ 1/2 := (div_le_iff₀ hk).mpr (by dsimp [k]; linarith)
  have hMε : M ≤ 2*ε := by
    have := mul_le_mul_of_nonneg_right hratio hM
    linarith
  intro x hx
  exact (hbound x hx).trans (mul_le_mul_of_nonneg_right hMε (Real.exp_pos _).le)

omit [CompleteSpace E] in
/-- Compare two actual linear Volterra equations with different
coefficients and forcing. The old solution is bounded by `B`; neither
its derivative nor any second derivative is assumed. All displayed
constants precede both functions and the comparison endpoint. -/
theorem linear_volterra_difference_bound
    {a b K B α β ω : ℝ} {w w₀ f f₀ : ℝ → E}
    {A A₀ : ℝ → E →L[ℝ] E} {z z₀ : E}
    (hab : a ≤ b) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hω : 0 ≤ ω)
    (hw : ContinuousOn w (Icc a b)) (hw₀ : ContinuousOn w₀ (Icc a b))
    (hA : ContinuousOn A (Icc a b)) (hA₀ : ContinuousOn A₀ (Icc a b))
    (hf : ContinuousOn f (Icc a b)) (hf₀ : ContinuousOn f₀ (Icc a b))
    (heq : ∀ x ∈ Icc a b, w x = z + ∫ s in a..x, A s (w s) + f s)
    (heq₀ : ∀ x ∈ Icc a b, w₀ x = z₀ + ∫ s in a..x, A₀ s (w₀ s) + f₀ s)
    (hinit : ‖z - z₀‖ ≤ ω)
    (hsize : ∀ s ∈ Icc a b, ‖A s‖ ≤ K ∧ ‖w₀ s‖ ≤ B ∧
      ‖A s - A₀ s‖ ≤ α ∧ ‖f s - f₀ s‖ ≤ β) :
    ∀ x ∈ Icc a b,
      ‖w x-w₀ x‖ ≤ 2*(ω+(α*B+β)*(b-a))*Real.exp ((2*(K+1))*(x-a)) := by
  have hforce : ∀ s ∈ Icc a b,
      ‖(A s-A₀ s) (w₀ s)+(f s-f₀ s)‖ ≤ α*B+β := by
    intro s hs
    obtain ⟨_, hwB, hdiff, hfdiff⟩ := hsize s hs
    exact (norm_add_le _ _).trans (add_le_add
      ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul hdiff hwB (norm_nonneg _) hα)) hfdiff)
  have hcont : ContinuousOn (fun s => A s (w s-w₀ s)) (Icc a b) :=
    hA.clm_apply (hw.sub hw₀)
  have hcontF : ContinuousOn (fun s => (A s-A₀ s) (w₀ s)+(f s-f₀ s)) (Icc a b) :=
    ((hA.sub hA₀).clm_apply hw₀).add (hf.sub hf₀)
  apply norm_le_of_volterra_integral_bound hab hK (by positivity) (hw.sub hw₀) _
    (fun s hs => (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hsize s hs).1 (norm_nonneg _)))
  intro x hx
  have hsub : Icc a x ⊆ Icc a b := Icc_subset_Icc le_rfl hx.2
  have hi₁ := (((hA.clm_apply hw).add hf).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) hx.1
  have hi₂ := (((hA₀.clm_apply hw₀).add hf₀).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) hx.1
  have hi₃ := (hcont.mono hsub).intervalIntegrable_of_Icc (μ := volume) hx.1
  have hi₄ := (hcontF.mono hsub).intervalIntegrable_of_Icc (μ := volume) hx.1
  have he : w x-w₀ x = (z-z₀) +
      (∫ s in a..x, A s (w s-w₀ s)) +
      ∫ s in a..x, (A s-A₀ s) (w₀ s)+(f s-f₀ s) := by
    calc
      w x-w₀ x = (z-z₀) +
          ((∫ s in a..x, A s (w s)+f s) - ∫ s in a..x, A₀ s (w₀ s)+f₀ s) := by
        rw [heq x hx, heq₀ x hx]
        abel
      _ = (z-z₀) + ∫ s in a..x, (A s (w s)+f s)-(A₀ s (w₀ s)+f₀ s) := by
        congr 1
        simpa only [Pi.add_apply, Pi.sub_apply] using!
          (intervalIntegral.integral_sub hi₁ hi₂).symm
      _ = (z-z₀) + ∫ s in a..x,
          A s (w s-w₀ s)+((A s-A₀ s) (w₀ s)+(f s-f₀ s)) := by
        congr 1
        apply intervalIntegral.integral_congr
        intro s _hs
        simp only [sub_apply, map_sub]
        abel
      _ = _ := by
        have hsum := intervalIntegral.integral_add hi₃ hi₄
        rw [hsum]
        abel
  have hint : ‖∫ s in a..x, (A s-A₀ s) (w₀ s)+(f s-f₀ s)‖ ≤ (α*B+β)*(b-a) := by
    have hn := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := x) (C := α*B+β) (f := fun s => (A s-A₀ s) (w₀ s)+(f s-f₀ s))
      (fun s hs => by
        rw [uIoc_of_le hx.1] at hs
        exact hforce s ⟨hs.1.le, hs.2.trans hx.2⟩)
    rw [abs_of_nonneg (sub_nonneg.mpr hx.1)] at hn
    exact hn.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right hx.2 a) (by positivity))
  change ‖w x-w₀ x‖ ≤ ω+(α*B+β)*(b-a) +
    ‖∫ s in a..x, A s (w s-w₀ s)‖
  rw [he]
  exact (norm_add_le _ _).trans
    ((add_le_add ((norm_add_le _ _).trans (add_le_add hinit le_rfl)) hint).trans_eq (by ring))

end Volterra

end EmcsfAcExtension.Local
