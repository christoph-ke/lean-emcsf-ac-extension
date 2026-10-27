module

public import EmcsfAcExtension.Local.Broad.ContractionWeighted
public import EmcsfAcExtension.Local.Broad.ContractionKernel

/-! # Scalar comparison from finite weighted mass and electric budgets

This is the orientation-independent integral argument. The solution-level
callers supply the incoming or outgoing mass budget separately.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local.Broad

/-- Combining finite coefficient budgets preserves the factor `εL+σ`.
The positive constant depends only on `c,Qmax,W,KB,H0,KM,KQ,KD,KδQ`;
it precedes all smallness, distance, interval and trace parameters. -/
theorem scalar_source_integral_of_budgets
    (c Qmax W KB H0 KM KQ KD KδQ : ℝ) (hc : 0 < c)
    (hQmax : 0 ≤ Qmax) (hW : 0 ≤ W) (hKB : 0 ≤ KB) (hH0 : 0 ≤ H0)
    (hKM : 0 ≤ KM) (hKQ : 0 ≤ KQ) (hKD : 0 ≤ KD) (hKδQ : 0 ≤ KδQ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (a b ε σ L E G : ℝ) (d₁ d₂ μ₁ μ₂ q₁ q₂ : ℝ → ℝ)
      (z₁ z₂ : ℝ → ℂ), a ≤ b → 0 ≤ ε → ε ≤ 1 → 0 ≤ σ → 0 ≤ L → 0 ≤ E →
      0 ≤ G → ε * G ≤ E →
      AEStronglyMeasurable d₁ (volume.restrict (Icc a b)) →
      AEStronglyMeasurable μ₁ (volume.restrict (Icc a b)) →
      AEStronglyMeasurable μ₂ (volume.restrict (Icc a b)) →
      AEStronglyMeasurable q₁ (volume.restrict (Icc a b)) →
      AEStronglyMeasurable q₂ (volume.restrict (Icc a b)) →
      (∀ x ∈ Icc a b, 0 ≤ d₁ x ∧ d₁ x ≤ W * d₂ x) →
      (∀ x ∈ Icc a b, 0 ≤ μ₁ x ∧ 0 ≤ μ₂ x ∧ μ₂ x ≤ 1) →
      (∀ x ∈ Icc a b, 0 ≤ q₁ x ∧ 0 ≤ q₂ x ∧ q₂ x ≤ Qmax) →
      (∀ x ∈ Icc a b, c ≤ 1 - μ₁ x ∧ c ≤ 1 - μ₂ x) →
      (∀ x ∈ Icc a b, |d₁ x - d₂ x| ≤ KB * G * d₁ x) →
      (∀ x ∈ Icc a b, ‖z₂ x‖ ≤ ε ∧ ‖z₁ x - z₂ x‖ ≤ H0 * E) →
      IntervalIntegrable (fun x => d₁ x * μ₁ x) volume a b →
      IntervalIntegrable (fun x => d₂ x * μ₂ x) volume a b →
      IntervalIntegrable (fun x => d₁ x * |μ₁ x - μ₂ x|) volume a b →
      IntervalIntegrable (fun x => d₁ x * q₁ x) volume a b →
      IntervalIntegrable (fun x => d₁ x * q₂ x) volume a b →
      IntervalIntegrable (fun x => d₁ x * |q₁ x - q₂ x|) volume a b →
      (∫ x in a..b, d₁ x * μ₁ x) ≤ KM * (ε * L + σ * ε ^ 2) →
      (∫ x in a..b, d₂ x * μ₂ x) ≤ KM * (ε * L + σ * ε ^ 2) →
      (∫ x in a..b, d₁ x * |μ₁ x - μ₂ x|) ≤ KD * (L + σ * ε) * E →
      (∫ x in a..b, d₁ x * q₁ x) ≤ KQ * σ * ε ^ 2 →
      (∫ x in a..b, d₁ x * q₂ x) ≤ KQ * σ * ε ^ 2 →
      (∫ x in a..b, d₁ x * |q₁ x - q₂ x|) ≤ KδQ * σ * ε * E →
      let F₁ := fun x => (μ₁ x - q₁ x) / (1 - μ₁ x)
      let F₂ := fun x => (μ₂ x - q₂ x) / (1 - μ₂ x)
      AEStronglyMeasurable
        (fun x => (d₁ x : ℂ) * F₁ x * z₁ x - (d₂ x : ℂ) * F₂ x * z₂ x)
        (volume.restrict (Icc a b)) →
      IntervalIntegrable
        (fun x => (d₁ x : ℂ) * F₁ x * z₁ x - (d₂ x : ℂ) * F₂ x * z₂ x) volume a b ∧
      (∫ x in a..b, ‖(d₁ x : ℂ) * F₁ x * z₁ x - (d₂ x : ℂ) * F₂ x * z₂ x‖) ≤
        K * (ε * L + σ) * E := by
  let A := c⁻¹ * ((1 + W) * KM + KQ)
  let B := (c⁻¹ + (1 + Qmax) / c ^ 2) * (KD + KδQ)
  let K := (H0 + KB) * A + B + 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro a b ε σ L E G d₁ d₂ μ₁ μ₂ q₁ q₂ z₁ z₂ hab hε hε1 hσ hL hE hG hεG
    md mμ₁ mμ₂ mq₁ mq₂ hd hμ hq hgap hδd hz im₁ im₂ imd iq₁ iq₂ iqd
    hm₁ hm₂ hmd hq₁ hq₂ hqd F₁ F₂ ms
  obtain ⟨im₂', hm₂'⟩ := weighted_integral_of_weight_comparison hab hW md mμ₂
    (fun x hx => (hd x hx).1) (fun x hx => (hμ x hx).2.1)
    (fun x hx => (hd x hx).2) im₂ hm₂
  obtain ⟨i₁, hi₁⟩ := coefficient_integral_of_mass_electric_bounds hab hc md mμ₁ mq₁
    (fun x hx => (hd x hx).1) (fun x hx => (hμ x hx).1)
    (fun x hx => (hq x hx).1) (fun x hx => (hgap x hx).1) im₁ iq₁ hm₁ hq₁
  obtain ⟨i₂, hi₂⟩ := coefficient_integral_of_mass_electric_bounds hab hc md mμ₂ mq₂
    (fun x hx => (hd x hx).1) (fun x hx => (hμ x hx).2.1)
    (fun x hx => (hq x hx).2.1) (fun x hx => (hgap x hx).2) im₂' iq₂ hm₂' hq₂
  obtain ⟨id, hid⟩ := coefficient_difference_integral_of_bounds hab hc md mμ₁ mμ₂ mq₁ mq₂
    (fun x hx => (hd x hx).1) (fun x hx => (hμ x hx).2)
    (fun x hx => (hq x hx).2) hgap imd iqd hmd hqd
  have hbudget : 0 ≤ ε * L + σ * ε ^ 2 := by positivity
  have ha₁ : c⁻¹ * (KM * (ε * L + σ * ε ^ 2) + KQ * σ * ε ^ 2) ≤
      A * (ε * L + σ * ε ^ 2) := by
    have hq := mul_le_mul_of_nonneg_left
      (show σ * ε ^ 2 ≤ ε * L + σ * ε ^ 2 from le_add_of_nonneg_left (mul_nonneg hε hL)) hKQ
    have hm := mul_nonneg (mul_nonneg hW hKM) hbudget
    dsimp [A]
    apply (mul_le_mul_of_nonneg_left (show _ ≤ ((1 + W) * KM + KQ) *
      (ε * L + σ * ε ^ 2) by nlinarith only [hq, hm]) (inv_nonneg.mpr hc.le)).trans_eq
    ring
  have ha₂ : c⁻¹ * (W * (KM * (ε * L + σ * ε ^ 2)) + KQ * σ * ε ^ 2) ≤
      A * (ε * L + σ * ε ^ 2) := by
    have hq := mul_le_mul_of_nonneg_left
      (show σ * ε ^ 2 ≤ ε * L + σ * ε ^ 2 from le_add_of_nonneg_left (mul_nonneg hε hL)) hKQ
    have hm := mul_nonneg hKM hbudget
    dsimp [A]
    apply (mul_le_mul_of_nonneg_left (show _ ≤ ((1 + W) * KM + KQ) *
      (ε * L + σ * ε ^ 2) by nlinarith only [hq, hm]) (inv_nonneg.mpr hc.le)).trans_eq
    ring
  have hb : (c⁻¹ + (1 + Qmax) / c ^ 2) *
      (KD * (L + σ * ε) * E + KδQ * σ * ε * E) ≤ B * (L + σ * ε) * E := by
    have hh := mul_le_mul_of_nonneg_left (show σ * ε ≤ L + σ * ε from le_add_of_nonneg_left hL)
      (mul_nonneg hKδQ hE)
    dsimp [B]
    have hk : 0 ≤ c⁻¹ + (1 + Qmax) / c ^ 2 := by positivity
    apply (mul_le_mul_of_nonneg_left (show KD * (L + σ * ε) * E + KδQ * σ * ε * E ≤
      (KD + KδQ) * (L + σ * ε) * E by nlinarith only [hh]) hk).trans_eq
    ring
  obtain ⟨ii, hi⟩ := geometric_scalar_source_difference_of_bounds hab
    (mul_nonneg hH0 hE) hε hKB hG (fun x hx => (hd x hx).1) hδd
    (fun x hx => (hz x hx).1) (fun x hx => (hz x hx).2) ms i₁ i₂ id
    (hi₁.trans ha₁) (hi₂.trans ha₂) (hid.trans hb)
  refine ⟨ii, hi.trans ?_⟩
  have hsq : ε ^ 2 ≤ 1 := by simpa only [one_pow] using (sq_le_sq₀ hε zero_le_one).mpr hε1
  have hs : ε * L + σ * ε ^ 2 ≤ ε * L + σ :=
    add_le_add le_rfl (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hsq hσ)
  have hs' : ε * (L + σ * ε) ≤ ε * L + σ := by nlinarith only [mul_le_mul_of_nonneg_left hsq hσ]
  calc
    _ = H0 * A * (ε * L + σ * ε ^ 2) * E +
      B * (ε * (L + σ * ε)) * E + KB * A * (ε * L + σ * ε ^ 2) * (ε * G) := by ring
    _ ≤ H0 * A * (ε * L + σ) * E + B * (ε * L + σ) * E +
        KB * A * (ε * L + σ) * E := by gcongr
    _ = ((H0 + KB) * A + B) * (ε * L + σ) * E := by ring
    _ ≤ K * (ε * L + σ) * E := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) (by positivity)) hE

end EmcsfAcExtension.Local.Broad
