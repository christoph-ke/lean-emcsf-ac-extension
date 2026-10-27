module

public import EmcsfAcExtension.Local.Broad.MassFluxCore

/-! # The undifferenced mass budget on one oriented radial section

The radius increases in this lemma. Incoming sections are reflected before
application. The scalar Hardy budget and the electric polynomial bound
are kept separate, so the variation budget need not be small.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local.Broad

/-- A positive radial mass reconstruction has a finite weighted integral.
The exact coefficients are one and one half, uniformly in the section,
radius, weight, scalar trace and electric coefficient. Reconstruction,
Hardy and moment premises are identities or budgets discharged by the
frozen-class callers in the two characteristic orientations. -/
theorem undifferenced_mass_budget_of_reconstruction
    {a b ε B H : ℝ} {w r f μ q : ℝ → ℝ}
    (hab : a ≤ b) (hε : 0 ≤ ε) (hB : 0 ≤ B)
    (cw : ContinuousOn w (Icc a b)) (cr : ContinuousOn r (Icc a b))
    (cf : ContinuousOn f (Icc a b))
    (hw : ∀ x ∈ Icc a b, 0 ≤ w x)
    (hr : ∀ x ∈ Icc a b, r x = ∫ y in a..x, w y)
    (hrpos : ∀ x ∈ Ioc a b, 0 < r x)
    (hf : ∀ x ∈ Icc a b, 0 ≤ f x ∧ f x ≤ ε)
    (hμ : ∀ x ∈ Icc a b, 0 ≤ μ x ∧ μ x ≤ 1)
    (hq : ∀ x ∈ Icc a b, 0 ≤ q x ∧ q x ≤ B * r x ^ 2)
    (hμmeas : AEStronglyMeasurable μ (volume.restrict (Icc a b)))
    (iF : IntervalIntegrable (fun x => w x * ((1 - μ x) * f x ^ 2 + q x)) volume a b)
    (hrec : ∀ x ∈ Icc a b, μ x = (r x)⁻¹ *
      ∫ y in a..x, w y * ((1 - μ y) * f y ^ 2 + q y))
    (iH : IntervalIntegrable (fun x => w x / r x * f x) volume a b)
    (hH : (∫ x in a..b, w x / r x * f x) ≤ H)
    (hmom : ∀ x ∈ Icc a b, (∫ y in a..x, w y * r y ^ 2) = r x ^ 3 / 3)
    (hmom₁ : (∫ x in a..b, w x * r x) = r b ^ 2 / 2) :
    IntervalIntegrable (fun x => w x / r x * μ x) volume a b ∧
      0 ≤ (∫ x in a..b, w x / r x * μ x) ∧
      (∫ x in a..b, w x / r x * μ x) ≤ ε * H + B * r b ^ 2 / 2 := by
  have hr0 x (hx : x ∈ Icc a b) : 0 ≤ r x := by
    rw [hr x hx]
    exact intervalIntegral.integral_nonneg hx.1
      (fun y hy => hw y ⟨hy.1, hy.2.trans hx.2⟩)
  have iε : IntervalIntegrable (fun x => w x / r x * (ε * f x)) volume a b := by
    simpa only [mul_left_comm, mul_assoc] using iH.const_mul ε
  have hbound x (hx : x ∈ Icc a b) :
      μ x ≤ (r x)⁻¹ * (∫ y in a..x, w y * (ε * f y)) + B * r x ^ 2 := by
    have hsub : uIcc a x ⊆ uIcc a b := uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc hx)
    have imaj : IntervalIntegrable
        (fun y => w y * (ε * f y) + B * (w y * r y ^ 2)) volume a x :=
      ContinuousOn.intervalIntegrable_of_Icc hx.1
        ((cw.mul (continuousOn_const.mul cf)).add
          (continuousOn_const.mul (cw.mul (cr.pow 2))) |>.mono
            (fun y hy => ⟨hy.1, hy.2.trans hx.2⟩))
    have hle := intervalIntegral.integral_mono_on hx.1 (iF.mono_set hsub) imaj
      (fun y hy => by
        have hy' : y ∈ Icc a b := ⟨hy.1, hy.2.trans hx.2⟩
        have hsq : (1 - μ y) * f y ^ 2 ≤ ε * f y := by
          calc
            _ ≤ f y ^ 2 := mul_le_of_le_one_left (sq_nonneg _) (by linarith [(hμ y hy').1])
            _ ≤ ε * f y := by nlinarith [(hf y hy').1, (hf y hy').2]
        calc
          _ ≤ w y * (ε * f y + B * r y ^ 2) :=
            mul_le_mul_of_nonneg_left (add_le_add hsq (hq y hy').2) (hw y hy')
          _ = _ := by ring)
    rw [intervalIntegral.integral_add
      (f := fun y => w y * (ε * f y)) (g := fun y => B * (w y * r y ^ 2))
      (ContinuousOn.intervalIntegrable_of_Icc hx.1
        ((cw.mul (continuousOn_const.mul cf)).mono (fun y hy => ⟨hy.1, hy.2.trans hx.2⟩)))
      ((ContinuousOn.intervalIntegrable_of_Icc hx.1
        ((cw.mul (cr.pow 2)).mono (fun y hy => ⟨hy.1, hy.2.trans hx.2⟩))).const_mul B),
      intervalIntegral.integral_const_mul, hmom x hx] at hle
    rw [hrec x hx]
    apply (mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr (hr0 x hx))).trans
    by_cases hx0 : r x = 0
    · simp [hx0]
    · have heq : (r x)⁻¹ * ((∫ y in a..x, w y * (ε * f y)) + B * (r x ^ 3 / 3)) =
          (r x)⁻¹ * (∫ y in a..x, w y * (ε * f y)) + B * r x ^ 2 / 3 := by
        generalize (∫ y in a..x, w y * (ε * f y)) = J
        field_simp [hx0]
      rw [heq]
      linarith [mul_nonneg hB (sq_nonneg (r x))]
  obtain ⟨ii, hi⟩ := weighted_integral_le_of_average_bound hab hB cw hw hr hrpos
    (continuousOn_const.mul cf) (fun x hx => mul_nonneg hε (hf x hx).1)
    iε hμmeas (fun x hx => (hμ x hx).1) hbound hmom₁
  refine ⟨ii, intervalIntegral.integral_nonneg hab (fun x hx =>
    mul_nonneg (div_nonneg (hw x hx) (hr0 x hx)) (hμ x hx).1), ?_⟩
  apply hi.trans
  change (∫ x in a..b, w x / r x * (ε * f x)) + B * r b ^ 2 / 2 ≤
    ε * H + B * r b ^ 2 / 2
  have heq : (∫ x in a..b, w x / r x * (ε * f x)) =
      ε * (∫ x in a..b, w x / r x * f x) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun x _ => by ring)
  rw [heq]
  exact add_le_add (mul_le_mul_of_nonneg_left hH hε) le_rfl

end EmcsfAcExtension.Local.Broad
