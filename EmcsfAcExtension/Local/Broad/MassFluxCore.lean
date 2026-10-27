module

public import EmcsfAcExtension.Local.Broad.MassKernel
public import EmcsfAcExtension.Local.Broad.MassComparison

/-! # Positive majorants for the weighted broad mass difference

These operator lemmas retain the weight and radius errors before applying
the matching Hardy kernel. They make no finiteness assumption on the
weighted quantity being estimated.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local.Broad

/-- The scalar mass-density difference with its linear Hardy majorant.
Every coefficient is exactly one, independent of all field values. -/
theorem scalar_mass_difference_le_linear {g₁ g₂ H X : ℝ} {f₁ f₂ : ℂ}
    (hg₁ : 0 ≤ g₁) (hg₁' : g₁ ≤ 1) (_hH : 0 ≤ H) (_hX : 0 ≤ X)
    (hδf : ‖f₁ - f₂‖ ≤ H) (hδg : |g₁ - g₂| ≤ X) :
    |g₁ * ‖f₁‖ ^ 2 - g₂ * ‖f₂‖ ^ 2| ≤
      H * (‖f₁‖ + ‖f₂‖) + X * ‖f₂‖ ^ 2 := by
  have heq : g₁ * ‖f₁‖ ^ 2 - g₂ * ‖f₂‖ ^ 2 =
      g₁ * ((‖f₁‖ - ‖f₂‖) * (‖f₁‖ + ‖f₂‖)) + (g₁ - g₂) * ‖f₂‖ ^ 2 := by ring
  rw [heq]
  calc
    _ ≤ |g₁ * ((‖f₁‖ - ‖f₂‖) * (‖f₁‖ + ‖f₂‖))| + |(g₁ - g₂) * ‖f₂‖ ^ 2| :=
      abs_add_le _ _
    _ = g₁ * (|‖f₁‖ - ‖f₂‖| * (‖f₁‖ + ‖f₂‖)) + |g₁ - g₂| * ‖f₂‖ ^ 2 := by
      simp only [abs_mul, abs_of_nonneg hg₁,
        abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)),
        abs_of_nonneg (sq_nonneg ‖f₂‖)]
    _ ≤ 1 * (H * (‖f₁‖ + ‖f₂‖)) + X * ‖f₂‖ ^ 2 := by
      gcongr
      exact (abs_norm_sub_norm_le _ _).trans hδf
    _ = _ := by ring

/-- Domination by a positive radial average proves weighted integrability
and its bound. The coefficients are exactly one and `1/2`, uniformly in
all weights and traces. The moment premise is the exact primitive moment,
discharged by the outgoing/incoming radius identities in applications. -/
theorem weighted_integral_le_of_average_bound {a b B : ℝ} {w r F P : ℝ → ℝ}
    (hab : a ≤ b) (_hB : 0 ≤ B) (hw : ContinuousOn w (Icc a b))
    (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x)
    (hr : ∀ x ∈ Icc a b, r x = ∫ y in a..x, w y)
    (hrpos : ∀ x ∈ Ioc a b, 0 < r x)
    (hF : ContinuousOn F (Icc a b)) (hF0 : ∀ x ∈ Icc a b, 0 ≤ F x)
    (hHardy : IntervalIntegrable (fun x => w x / r x * F x) volume a b)
    (hPmeas : AEStronglyMeasurable P (volume.restrict (Icc a b)))
    (hP0 : ∀ x ∈ Icc a b, 0 ≤ P x)
    (hbound : ∀ x ∈ Icc a b,
      P x ≤ (r x)⁻¹ * (∫ y in a..x, w y * F y) + B * r x ^ 2)
    (hmoment : (∫ x in a..b, w x * r x) = r b ^ 2 / 2) :
    IntervalIntegrable (fun x => w x / r x * P x) volume a b ∧
      (∫ x in a..b, w x / r x * P x) ≤
        (∫ x in a..b, w x / r x * F x) + B * r b ^ 2 / 2 := by
  have cr := continuous_radius_of_primitive hab hw hr
  have hr0 x (hx : x ∈ Icc a b) : 0 ≤ r x := by
    rw [hr x hx]
    exact intervalIntegral.integral_nonneg hx.1 (fun y hy => hw0 y ⟨hy.1, hy.2.trans hx.2⟩)
  obtain ⟨iA, hA⟩ := integral_mass_average_le_hardy hab hw hw0 hr hrpos hF hF0 hHardy
  let N := fun x => w x / r x ^ 2 * (∫ y in a..x, w y * F y) + B * (w x * r x)
  have iR : IntervalIntegrable (fun x => w x * r x) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab (hw.mul cr)
  have iN : IntervalIntegrable N volume a b := iA.add (iR.const_mul B)
  have hW x (hx : x ∈ Icc a b) : 0 ≤ w x / r x := div_nonneg (hw0 x hx) (hr0 x hx)
  have hmaj x (hx : x ∈ Icc a b) : w x / r x * P x ≤ N x := by
    apply (mul_le_mul_of_nonneg_left (hbound x hx) (hW x hx)).trans_eq
    dsimp [N]
    by_cases hx0 : r x = 0
    · simp [hx0]
    · field_simp [hx0]
  have iNP := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp iN
  have hWPmeas : AEStronglyMeasurable (fun x => w x / r x * P x)
      (volume.restrict (Icc a b)) := by
    exact ((hw.aestronglyMeasurable (μ := volume) measurableSet_Icc).div₀
      (cr.aestronglyMeasurable (μ := volume) measurableSet_Icc)).mul hPmeas
  have iP : IntegrableOn (fun x => w x / r x * P x) (Icc a b) := by
    apply iNP.mono' hWPmeas
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hW x hx) (hP0 x hx))]
    exact hmaj x hx
  have iP' := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr iP
  refine ⟨iP', ?_⟩
  calc
    _ ≤ ∫ x in a..b, N x := intervalIntegral.integral_mono_on hab iP' iN hmaj
    _ = (∫ x in a..b, w x / r x ^ 2 * ∫ y in a..x, w y * F y) +
        B * r b ^ 2 / 2 := by
      rw [intervalIntegral.integral_add iA (iR.const_mul B),
        intervalIntegral.integral_const_mul, hmoment]
      ring
    _ ≤ _ := add_le_add hA le_rfl

/-- Weighted comparison of two positive radial mass averages. All constants
are displayed: `c,k` are the fixed box parameters; `H,X,G` are the scalar,
mass-gap and geometric errors; `B,Bδ` are the electric density coefficients.
The two Hardy budgets use the first weight. This helper proves integrability
before estimating the real integral and uses no smallness of either budget. -/
theorem weighted_mass_difference_of_bounds
    {a b c k G H X B Bδ ε L₁ L₂ : ℝ}
    {w₁ w₂ r₁ r₂ f₁ f₂ F₁ F₂ μ₁ μ₂ : ℝ → ℝ}
    (hab : a ≤ b) (hc : 0 < c) (hk : 0 ≤ k)
    (hG : 0 ≤ G) (hH : 0 ≤ H) (hX : 0 ≤ X)
    (hB : 0 ≤ B) (hBδ : 0 ≤ Bδ) (hε : 0 ≤ ε)
    (cw₁ : ContinuousOn w₁ (Icc a b)) (cw₂ : ContinuousOn w₂ (Icc a b))
    (cf₁ : ContinuousOn f₁ (Icc a b)) (cf₂ : ContinuousOn f₂ (Icc a b))
    (hw₁ : ∀ x ∈ Icc a b, c ≤ w₁ x) (hw₂ : ∀ x ∈ Icc a b, c ≤ w₂ x)
    (hwratio : ∀ x ∈ Icc a b, w₁ x ≤ k * w₂ x ∧ w₂ x ≤ k * w₁ x)
    (hδw : ∀ x ∈ Icc a b, |w₁ x - w₂ x| ≤ G)
    (hr₁ : ∀ x ∈ Icc a b, r₁ x = ∫ y in a..x, w₁ y)
    (hr₂ : ∀ x ∈ Icc a b, r₂ x = ∫ y in a..x, w₂ y)
    (hr₁pos : ∀ x ∈ Ioc a b, 0 < r₁ x) (hr₂pos : ∀ x ∈ Ioc a b, 0 < r₂ x)
    (hrratio : ∀ x ∈ Icc a b, r₂ x ≤ k * r₁ x ∧ r₁ x ≤ k * r₂ x)
    (hδr : ∀ x ∈ Icc a b, |r₁ x - r₂ x| ≤ G * r₁ x)
    (hf₁ : ∀ x ∈ Icc a b, 0 ≤ f₁ x ∧ f₁ x ≤ ε)
    (hf₂ : ∀ x ∈ Icc a b, 0 ≤ f₂ x ∧ f₂ x ≤ ε)
    (hF₂ : ∀ x ∈ Icc a b, 0 ≤ F₂ x ∧ F₂ x ≤ f₂ x ^ 2 + B * r₂ x ^ 2)
    (hδF : ∀ x ∈ Icc a b, |F₁ x - F₂ x| ≤
      H * (f₁ x + f₂ x) + X * f₂ x ^ 2 + Bδ * r₁ x ^ 2)
    (i₁₁ : IntervalIntegrable (fun x => w₁ x * F₁ x) volume a b)
    (i₂₂ : IntervalIntegrable (fun x => w₂ x * F₂ x) volume a b)
    (hμ₁ : ∀ x ∈ Icc a b, μ₁ x = (r₁ x)⁻¹ * ∫ y in a..x, w₁ y * F₁ y)
    (hμ₂ : ∀ x ∈ Icc a b, μ₂ x = (r₂ x)⁻¹ * ∫ y in a..x, w₂ y * F₂ y)
    (im₁ : IntervalIntegrable (fun x => w₁ x / r₁ x * f₁ x) volume a b)
    (im₂ : IntervalIntegrable (fun x => w₁ x / r₁ x * f₂ x) volume a b)
    (hm₁ : (∫ x in a..b, w₁ x / r₁ x * f₁ x) ≤ L₁)
    (hm₂ : (∫ x in a..b, w₁ x / r₁ x * f₂ x) ≤ L₂)
    (hmoment₁ : (∫ x in a..b, w₁ x * r₁ x) = r₁ b ^ 2 / 2)
    (hmoment₂ : ∀ x ∈ Icc a b,
      (∫ y in a..x, w₁ y * r₁ y ^ 2) = r₁ x ^ 3 / 3) :
    let KT := k ^ 2 / c + 1
    IntervalIntegrable (fun x => w₁ x / r₁ x * |μ₁ x - μ₂ x|) volume a b ∧
      (∫ x in a..b, w₁ x / r₁ x * |μ₁ x - μ₂ x|) ≤
        H * (L₁ + L₂) + (X + KT * k ^ 2 * G) * ε * L₂ +
          (Bδ + KT * k ^ 4 * G * B) * r₁ b ^ 2 / 6 := by
  intro KT
  have hKT : 0 ≤ KT := by dsimp [KT]; positivity
  have hw₁0 x (hx : x ∈ Icc a b) := hc.le.trans (hw₁ x hx)
  have hw₂0 x (hx : x ∈ Icc a b) := hc.le.trans (hw₂ x hx)
  have cr₁ := continuous_radius_of_primitive hab cw₁ hr₁
  have cr₂ := continuous_radius_of_primitive hab cw₂ hr₂
  have hr₁0 x (hx : x ∈ Icc a b) : 0 ≤ r₁ x := by
    rw [hr₁ x hx]
    exact intervalIntegral.integral_nonneg hx.1 (fun y hy => hw₁0 y ⟨hy.1, hy.2.trans hx.2⟩)
  have hr₂0 x (hx : x ∈ Icc a b) : 0 ≤ r₂ x := by
    rw [hr₂ x hx]
    exact intervalIntegral.integral_nonneg hx.1 (fun y hy => hw₂0 y ⟨hy.1, hy.2.trans hx.2⟩)
  let V := X + KT * k ^ 2 * G
  let F := fun x => H * (f₁ x + f₂ x) + V * f₂ x ^ 2
  let Q := (Bδ + KT * k ^ 4 * G * B) / 3
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have cF : ContinuousOn F (Icc a b) :=
    (continuousOn_const.mul (cf₁.add cf₂)).add (continuousOn_const.mul (cf₂.pow 2))
  have hF x (hx : x ∈ Icc a b) : 0 ≤ F x := by
    dsimp [F]
    exact add_nonneg (mul_nonneg hH (add_nonneg (hf₁ x hx).1 (hf₂ x hx).1))
      (mul_nonneg hV (sq_nonneg _))
  have i₁₂ : IntervalIntegrable (fun x => w₁ x * F₂ x) volume a b := by
    have cRatio : ContinuousOn (fun x => w₁ x / w₂ x) (uIcc a b) := by
      rw [uIcc_of_le hab]
      exact cw₁.div cw₂ (fun x hx => (hc.trans_le (hw₂ x hx)).ne')
    apply (i₂₂.mul_continuousOn cRatio).congr
    intro x hx
    have hx' : x ∈ Icc a b := by simpa only [uIcc_of_le hab] using uIoc_subset_uIcc hx
    field_simp [(hc.trans_le (hw₂ x hx')).ne']
  have hpoint x (hx : x ∈ Icc a b) : |μ₁ x - μ₂ x| ≤
      (r₁ x)⁻¹ * (∫ y in a..x, w₁ y * F y) + Q * r₁ x ^ 2 := by
    rcases eq_or_lt_of_le hx.1 with hax | hax
    · subst x
      rw [hμ₁ a (left_mem_Icc.mpr hab), hμ₂ a (left_mem_Icc.mpr hab)]
      simp only [intervalIntegral.integral_same, mul_zero, sub_self, abs_zero, zero_add]
      positivity
    have hxsub : Icc a x ⊆ Icc a b := Icc_subset_Icc le_rfl hx.2
    have hxu : uIcc a x ⊆ uIcc a b := uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc hx)
    have ip₁ := i₁₁.mono_set hxu
    have ip₂ := i₂₂.mono_set hxu
    have ip₁₂ := i₁₂.mono_set hxu
    have is₂ : IntervalIntegrable (fun y => w₁ y * f₂ y ^ 2) volume a x :=
      ContinuousOn.intervalIntegrable_of_Icc hax.le (cw₁.mul (cf₂.pow 2) |>.mono hxsub)
    have ir₂ : IntervalIntegrable (fun y => w₁ y * r₁ y ^ 2) volume a x :=
      ContinuousOn.intervalIntegrable_of_Icc hax.le (cw₁.mul (cr₁.pow 2) |>.mono hxsub)
    have iF : IntervalIntegrable (fun y => w₁ y * F y) volume a x :=
      ContinuousOn.intervalIntegrable_of_Icc hax.le (cw₁.mul cF |>.mono hxsub)
    have icore := average_difference_le_of_bounds hax.le (hr₁pos x ⟨hax, hx.2⟩)
      (hr₂pos x ⟨hax, hx.2⟩) hc hk hG
      (fun y hy => hw₁ y (hxsub hy)) (fun y hy => hw₂0 y (hxsub hy))
      (fun y hy => (hF₂ y (hxsub hy)).1) (fun y hy => (hwratio y (hxsub hy)).1)
      (fun y hy => hδw y (hxsub hy)) (hrratio x hx).1 (hδr x hx) ip₁ ip₁₂ ip₂
    rw [← hμ₁ x hx, ← hμ₂ x hx] at icore
    have hmix : (r₂ x)⁻¹ * (∫ y in a..x, w₂ y * F₂ y) ≤
        k ^ 2 * ((r₁ x)⁻¹ * ∫ y in a..x, w₁ y * F₂ y) := by
      have hi := intervalIntegral.integral_mono_on hax.le ip₂ (ip₁₂.const_mul k)
        (fun y hy => by
          calc
            _ ≤ (k * w₁ y) * F₂ y := mul_le_mul_of_nonneg_right
              (hwratio y (hxsub hy)).2 (hF₂ y (hxsub hy)).1
            _ = _ := by ring)
      rw [intervalIntegral.integral_const_mul] at hi
      have hn := intervalIntegral.integral_nonneg (μ := volume) hax.le
        (fun y hy => mul_nonneg (hw₁0 y (hxsub hy)) (hF₂ y (hxsub hy)).1)
      calc
        _ ≤ (r₂ x)⁻¹ * (k * ∫ y in a..x, w₁ y * F₂ y) :=
          mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (hr₂pos x ⟨hax, hx.2⟩).le)
        _ = k * (r₁ x / r₂ x) * ((r₁ x)⁻¹ * ∫ y in a..x, w₁ y * F₂ y) := by
          field_simp [(hr₁pos x ⟨hax, hx.2⟩).ne', (hr₂pos x ⟨hax, hx.2⟩).ne']
        _ ≤ k * k * ((r₁ x)⁻¹ * ∫ y in a..x, w₁ y * F₂ y) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            ((div_le_iff₀ (hr₂pos x ⟨hax, hx.2⟩)).mpr (hrratio x hx).2) hk)
            (mul_nonneg (inv_nonneg.mpr (hr₁pos x ⟨hax, hx.2⟩).le) hn)
        _ = _ := by ring
    have iD : IntervalIntegrable (fun y => w₁ y * |F₁ y - F₂ y|) volume a x := by
      have hi : IntervalIntegrable (fun y => w₁ y * (F₁ y - F₂ y)) volume a x :=
        (ip₁.sub ip₁₂).congr (fun y _ => by ring)
      apply hi.norm.congr
      intro y hy
      have hy' : y ∈ Icc a x := by simpa only [uIcc_of_le hax.le] using uIoc_subset_uIcc hy
      change ‖w₁ y * (F₁ y - F₂ y)‖ = _
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw₁0 y (hxsub hy'))]
    have iMaj : IntervalIntegrable (fun y => w₁ y *
        (H * (f₁ y + f₂ y) + X * f₂ y ^ 2 + Bδ * r₁ y ^ 2)) volume a x :=
      ContinuousOn.intervalIntegrable_of_Icc hax.le
        (cw₁.mul ((continuousOn_const.mul (cf₁.add cf₂)).add
          (continuousOn_const.mul (cf₂.pow 2)) |>.add
            (continuousOn_const.mul (cr₁.pow 2))) |>.mono hxsub)
    have hD := intervalIntegral.integral_mono_on hax.le iD iMaj
      (fun y hy => mul_le_mul_of_nonneg_left (hδF y (hxsub hy)) (hw₁0 y (hxsub hy)))
    have iMaj₂ : IntervalIntegrable (fun y => w₁ y * (f₂ y ^ 2 + B * k ^ 2 * r₁ y ^ 2))
        volume a x := ContinuousOn.intervalIntegrable_of_Icc hax.le
          (cw₁.mul ((cf₂.pow 2).add (continuousOn_const.mul (cr₁.pow 2))) |>.mono hxsub)
    have h₂ := intervalIntegral.integral_mono_on hax.le ip₁₂ iMaj₂ (fun y hy => by
      apply mul_le_mul_of_nonneg_left _ (hw₁0 y (hxsub hy))
      apply (hF₂ y (hxsub hy)).2.trans
      have hrbound := (sq_le_sq₀ (hr₂0 y (hxsub hy))
        (mul_nonneg hk (hr₁0 y (hxsub hy)))).mpr (hrratio y (hxsub hy)).1
      calc
        _ ≤ f₂ y ^ 2 + B * (k * r₁ y) ^ 2 := by gcongr
        _ = _ := by ring)
    have hiSum : (∫ y in a..x, w₁ y *
        (H * (f₁ y + f₂ y) + X * f₂ y ^ 2 + Bδ * r₁ y ^ 2)) +
        KT * G * k ^ 2 * (∫ y in a..x, w₁ y * (f₂ y ^ 2 + B * k ^ 2 * r₁ y ^ 2)) =
        (∫ y in a..x, w₁ y * F y) +
          (Bδ + KT * k ^ 4 * G * B) * r₁ x ^ 3 / 3 := by
      rw [← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_add iMaj (iMaj₂.const_mul _)]
      have heq : (fun y => w₁ y *
          (H * (f₁ y + f₂ y) + X * f₂ y ^ 2 + Bδ * r₁ y ^ 2) +
          KT * G * k ^ 2 * (w₁ y * (f₂ y ^ 2 + B * k ^ 2 * r₁ y ^ 2))) =
          fun y => w₁ y * F y + (Bδ + KT * k ^ 4 * G * B) * (w₁ y * r₁ y ^ 2) := by
        funext y
        dsimp [F, V]
        ring
      rw [heq, intervalIntegral.integral_add iF (ir₂.const_mul _),
        intervalIntegral.integral_const_mul, hmoment₂ x hx]
      ring
    calc
      _ ≤ (r₁ x)⁻¹ * (∫ y in a..x, w₁ y * |F₁ y - F₂ y|) +
          KT * G * (k ^ 2 * ((r₁ x)⁻¹ * ∫ y in a..x, w₁ y * F₂ y)) :=
        icore.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
          ((hμ₂ x hx).trans_le hmix) (mul_nonneg hKT hG)))
      _ ≤ (r₁ x)⁻¹ * (∫ y in a..x, w₁ y *
          (H * (f₁ y + f₂ y) + X * f₂ y ^ 2 + Bδ * r₁ y ^ 2)) +
          KT * G * (k ^ 2 * ((r₁ x)⁻¹ *
            ∫ y in a..x, w₁ y * (f₂ y ^ 2 + B * k ^ 2 * r₁ y ^ 2))) := by
        have hiR : 0 ≤ (r₁ x)⁻¹ := (inv_pos.mpr (hr₁pos x ⟨hax, hx.2⟩)).le
        gcongr
      _ = (r₁ x)⁻¹ * ((∫ y in a..x, w₁ y *
          (H * (f₁ y + f₂ y) + X * f₂ y ^ 2 + Bδ * r₁ y ^ 2)) +
          KT * G * k ^ 2 * (∫ y in a..x, w₁ y * (f₂ y ^ 2 + B * k ^ 2 * r₁ y ^ 2))) := by ring
      _ = _ := by rw [hiSum]; dsimp [Q]; field_simp [(hr₁pos x ⟨hax, hx.2⟩).ne']
  have wmeas := cw₁.aestronglyMeasurable (μ := volume) measurableSet_Icc
  have rmeas := cr₁.aestronglyMeasurable (μ := volume) measurableSet_Icc
  have if₂sq : IntervalIntegrable (fun x => w₁ x / r₁ x * f₂ x ^ 2) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    apply (((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp im₂).mul_const ε).mono'
      ((wmeas.div₀ rmeas).mul ((cf₂.pow 2).aestronglyMeasurable (μ := volume) measurableSet_Icc))
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have hw := div_nonneg (hw₁0 x hx) (hr₁0 x hx)
    change ‖w₁ x / r₁ x * f₂ x ^ 2‖ ≤ w₁ x / r₁ x * f₂ x * ε
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw (sq_nonneg _))]
    calc
      _ ≤ w₁ x / r₁ x * (ε * f₂ x) := mul_le_mul_of_nonneg_left
        (by simpa only [pow_two] using mul_le_mul_of_nonneg_right (hf₂ x hx).2 (hf₂ x hx).1) hw
      _ = _ := by ring
  have iHardy : IntervalIntegrable (fun x => w₁ x / r₁ x * F x) volume a b :=
    (((im₁.add im₂).const_mul H).add (if₂sq.const_mul V)).congr (fun x _ => by dsimp [F]; ring)
  have hHardy : (∫ x in a..b, w₁ x / r₁ x * F x) ≤
      H * (L₁ + L₂) + V * ε * L₂ := by
    have hsquare := intervalIntegral.integral_mono_on hab if₂sq (im₂.const_mul ε) (fun x hx => by
      have hw := div_nonneg (hw₁0 x hx) (hr₁0 x hx)
      calc
        _ ≤ w₁ x / r₁ x * (ε * f₂ x) := mul_le_mul_of_nonneg_left
          (by simpa only [pow_two] using mul_le_mul_of_nonneg_right (hf₂ x hx).2 (hf₂ x hx).1) hw
        _ = _ := by ring)
    rw [intervalIntegral.integral_const_mul] at hsquare
    have heq : (fun x => w₁ x / r₁ x * F x) = fun x =>
        H * (w₁ x / r₁ x * f₁ x + w₁ x / r₁ x * f₂ x) + V * (w₁ x / r₁ x * f₂ x ^ 2) :=
      funext fun x => by dsimp [F]; ring
    rw [heq, intervalIntegral.integral_add ((im₁.add im₂).const_mul H) (if₂sq.const_mul V),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add im₁ im₂]
    calc
      _ ≤ H * (L₁ + L₂) + V * (ε * L₂) := add_le_add
        (mul_le_mul_of_nonneg_left (add_le_add hm₁ hm₂) hH)
        (mul_le_mul_of_nonneg_left
          (hsquare.trans (mul_le_mul_of_nonneg_left hm₂ hε)) hV)
      _ = _ := by ring
  have hmeasμ {w r μ F : ℝ → ℝ} (cr : ContinuousOn r (Icc a b))
      (ii : IntervalIntegrable (fun x => w x * F x) volume a b)
      (hμ : ∀ x ∈ Icc a b, μ x = (r x)⁻¹ * ∫ y in a..x, w y * F y) :
      AEStronglyMeasurable μ (volume.restrict (Icc a b)) := by
    have cp := ii.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc |>.continuousOn
    rw [uIcc_of_le hab] at cp
    apply ((cp.aestronglyMeasurable (μ := volume) measurableSet_Icc).div₀
      (cr.aestronglyMeasurable (μ := volume) measurableSet_Icc)).congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    change (∫ y in a..x, w y * F y) / r x = μ x
    rw [hμ x hx, div_eq_mul_inv, mul_comm]
  have hPmeas : AEStronglyMeasurable (fun x => |μ₁ x - μ₂ x|)
      (volume.restrict (Icc a b)) := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using!
      ((hmeasμ cr₁ i₁₁ hμ₁).sub (hmeasμ cr₂ i₂₂ hμ₂)).norm
  obtain ⟨iP, hP⟩ := weighted_integral_le_of_average_bound hab hQ cw₁ hw₁0 hr₁ hr₁pos
    cF hF iHardy hPmeas (fun _ _ => abs_nonneg _) hpoint hmoment₁
  refine ⟨iP, hP.trans ?_⟩
  calc
    _ ≤ (H * (L₁ + L₂) + V * ε * L₂) + Q * r₁ b ^ 2 / 2 := add_le_add hHardy le_rfl
    _ = _ := by dsimp [Q, V]; ring

end EmcsfAcExtension.Local.Broad
