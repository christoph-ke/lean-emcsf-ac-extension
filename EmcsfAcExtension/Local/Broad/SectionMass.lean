module

public import EmcsfAcExtension.Local.Broad.MassFluxCore
public import EmcsfAcExtension.Local.Broad.Charge
import EmcsfAcExtension.Local.Broad.ChargeAlgebra

/-! # Broad mass comparison on an increasing characteristic section

An incoming section is reflected before applying this operator lemma.
Every supplied identity is an actual sectional mass or radius constraint;
the callers prove them from the frozen class.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local.Broad

/-- Sectional form of the weighted broad mass comparison. For fixed geometric
box `c,C` and Hardy coefficient `KH`, the positive constant is uniform in all
triangle, coupling, scalar, variation, solution and section parameters.
This helper accepts the exact reconstruction identities and the matching
Hardy budgets, which its outgoing/incoming callers discharge. -/
theorem section_mass_flux_of_bounds (c C KH : ℝ) (hc : 0 < c)
    (hC : 0 ≤ C) (hKH : 0 ≤ KH) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s t e M ε L : ℝ) (S₁ S₂ : Fields),
      IsSolution e S₁ (triangle s t) → IsSolution e S₂ (triangle s t) →
      1 ≤ M → 0 ≤ ε → ε ≤ 1 → ε ^ 2 ≤ 1 / 2 → 0 ≤ L →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s t,
        c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C ∧
        ‖S.phi p.1 p.2‖ ≤ M ∧ ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ ε) →
      (∀ u v, (u, v) ∈ triangle s t → ∀ x ∈ Icc u v, ∀ y ∈ Icc u v,
        ‖S₂.a u x - S₂.a u y‖ ≤ ε) →
      e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2 ≤ 1 →
      ∀ (a b : ℝ) (p : ℝ → ℝ × ℝ) (w₁ w₂ : ℝ → ℝ) (f₁ f₂ : ℝ → ℂ),
      a ≤ b → MapsTo p (Icc a b) (triangle s t) →
      ContinuousOn w₁ (Icc a b) → ContinuousOn w₂ (Icc a b) →
      ContinuousOn f₁ (Icc a b) → ContinuousOn f₂ (Icc a b) →
      (∀ x ∈ Icc a b, c ≤ w₁ x ∧ w₁ x ≤ C ∧ c ≤ w₂ x ∧ w₂ x ≤ C) →
      (∀ x ∈ Icc a b, |w₁ x - w₂ x| ≤ (geometry_distance s t S₁ S₂).toReal) →
      (∀ x ∈ Icc a b, ‖f₁ x‖ ≤ ε ∧ ‖f₂ x‖ ≤ ε ∧
        ‖f₁ x - f₂ x‖ ≤ (normalized_field_distance s t S₁ S₂).toReal +
          ‖S₁.phi (p x).1 (p x).2 - S₂.phi (p x).1 (p x).2‖) →
      let r₁ := fun x => S₁.r (p x).1 (p x).2
      let r₂ := fun x => S₂.r (p x).1 (p x).2
      let μ₁ := fun x => S₁.mu (p x).1 (p x).2
      let μ₂ := fun x => S₂.mu (p x).1 (p x).2
      let F₁ := fun x => (1 - μ₁ x) * ‖f₁ x‖ ^ 2 + S₁.Q (p x).1 (p x).2 ^ 2 / r₁ x ^ 2
      let F₂ := fun x => (1 - μ₂ x) * ‖f₂ x‖ ^ 2 + S₂.Q (p x).1 (p x).2 ^ 2 / r₂ x ^ 2
      (∀ x ∈ Icc a b, r₁ x = ∫ y in a..x, w₁ y) →
      (∀ x ∈ Icc a b, r₂ x = ∫ y in a..x, w₂ y) →
      (∀ x ∈ Ioc a b, 0 < r₁ x ∧ 0 < r₂ x) →
      IntervalIntegrable (fun x => w₁ x * F₁ x) volume a b →
      IntervalIntegrable (fun x => w₂ x * F₂ x) volume a b →
      (∀ x ∈ Icc a b, μ₁ x = (r₁ x)⁻¹ * ∫ y in a..x, w₁ y * F₁ y) →
      (∀ x ∈ Icc a b, μ₂ x = (r₂ x)⁻¹ * ∫ y in a..x, w₂ y * F₂ y) →
      IntervalIntegrable (fun x => w₁ x / r₁ x * ‖f₁ x‖) volume a b →
      IntervalIntegrable (fun x => w₂ x / r₂ x * ‖f₂ x‖) volume a b →
      (∫ x in a..b, w₁ x / r₁ x * ‖f₁ x‖) ≤ KH * L →
      (∫ x in a..b, w₂ x / r₂ x * ‖f₂ x‖) ≤ KH * L →
      (∫ x in a..b, w₁ x * r₁ x) = r₁ b ^ 2 / 2 →
      (∀ x ∈ Icc a b, (∫ y in a..x, w₁ y * r₁ y ^ 2) = r₁ x ^ 3 / 3) →
      r₁ b ≤ C * (t - s) →
      let E := (normalized_field_distance s t S₁ S₂).toReal +
        ε * (geometry_distance s t S₁ S₂).toReal
      IntervalIntegrable (fun x => w₁ x / r₁ x * |μ₁ x - μ₂ x|) volume a b ∧
        (∫ x in a..b, w₁ x / r₁ x * |μ₁ x - μ₂ x|) ≤
          K * L * (normalized_field_distance s t S₁ S₂).toReal +
          K * ε * L * (geometry_distance s t S₁ S₂).toReal +
          K * (e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2) * ε * E := by
  obtain ⟨A, hA, hscalar⟩ := scalar_average_difference_bound c hc
  obtain ⟨Kq, hKq, helectric⟩ := charged_square_difference c C hc hC
  obtain ⟨Kμ, hKμ, hmass⟩ := Local.stab_broad_mu_sup c C hc hC
  let k := C / c
  let KT := k ^ 2 / c + 1
  let KS := ((1 + A) * (1 + k ^ 2) + 2 * Kμ * k ^ 2 + KT * k ^ 4) * KH
  let KQ := 4 * C ^ 2 * (Kq + KT * k ^ 4)
  let K := KS + KQ + 1
  have hk : 0 ≤ k := div_nonneg hC hc.le
  have hKT : 0 ≤ KT := by dsimp [KT]; positivity
  have hKS : 0 ≤ KS := by dsimp [KS]; positivity
  have hKQ : 0 ≤ KQ := by dsimp [KQ]; positivity
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro s t e M ε L S₁ S₂ hS₁ hS₂ hM hε hε1 hsmall hL hbox hosc hσ
    a b p w₁ w₂ f₁ f₂ hab hp cw₁ cw₂ cf₁ cf₂ hw hδw hf
    r₁ r₂ μ₁ μ₂ F₁ F₂ hr₁ hr₂ hrpos iF₁ iF₂ hμ₁ hμ₂ im₁ im₂ hm₁ hm₂ hmom₁ hmom₂ hR E
  have hmem₁ : S₁ ∈ ({S₁, S₂} : Set Fields) := by simp
  have hmem₂ : S₂ ∈ ({S₁, S₂} : Set Fields) := by simp
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  let G := (geometry_distance s t S₁ S₂).toReal
  let H := (1 + A) * E
  let X := 2 * Kμ * ε * E
  let B := e ^ 2 * M ^ 2 * ε ^ 2
  let Bδ := Kq * e ^ 2 * M ^ 2 * ε * E
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hBδ : 0 ≤ Bδ := by dsimp [Bδ]; positivity
  have hεG : ε * G ≤ E := le_add_of_nonneg_left ENNReal.toReal_nonneg
  have hD : (normalized_field_distance s t S₁ S₂).toReal ≤ E :=
    le_add_of_nonneg_right (mul_nonneg hε hG)
  have hfin := geometry_distance_ne_top hS₁ hS₂ hc
    (fun q hq => (hbox S₁ hmem₁ q hq).1)
  have hmass' := hmass s t e M ε S₁ S₂ hS₁ hS₂ hM hε hε1 hsmall hbox hosc
  have hμbound : (mass_ratio_distance s t S₁ S₂).toReal ≤ X := by
    calc
      _ ≤ Kμ * ε * (normalized_field_distance s t S₁ S₂).toReal +
          Kμ * ε ^ 2 * G + Kμ * (e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2) * ε * E := hmass'
      _ = Kμ * ε * E + Kμ * (e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2) * ε * E := by dsimp [E, G]; ring
      _ ≤ Kμ * ε * E + Kμ * 1 * ε * E := by gcongr
      _ = _ := by dsimp [X]; ring
  have hwratio x (hx : x ∈ Icc a b) : w₁ x ≤ k * w₂ x ∧ w₂ x ≤ k * w₁ x := by
    have hkc : k * c = C := by dsimp [k]; field_simp
    constructor
    · exact (hw x hx).2.1.trans (hkc ▸ mul_le_mul_of_nonneg_left (hw x hx).2.2.1 hk)
    · exact (hw x hx).2.2.2.trans (hkc ▸ mul_le_mul_of_nonneg_left (hw x hx).1 hk)
  have hrratio x (hx : x ∈ Icc a b) : r₂ x ≤ k * r₁ x ∧ r₁ x ≤ k * r₂ x := by
    have i₁ : IntervalIntegrable w₁ volume a x := ContinuousOn.intervalIntegrable_of_Icc hx.1
      (cw₁.mono (Icc_subset_Icc le_rfl hx.2))
    have i₂ : IntervalIntegrable w₂ volume a x := ContinuousOn.intervalIntegrable_of_Icc hx.1
      (cw₂.mono (Icc_subset_Icc le_rfl hx.2))
    rw [hr₁ x hx, hr₂ x hx]
    constructor
    · simpa only [intervalIntegral.integral_const_mul] using intervalIntegral.integral_mono_on
        hx.1 i₂ (i₁.const_mul k) (fun y hy => (hwratio y ⟨hy.1, hy.2.trans hx.2⟩).2)
    · simpa only [intervalIntegral.integral_const_mul] using intervalIntegral.integral_mono_on
        hx.1 i₁ (i₂.const_mul k) (fun y hy => (hwratio y ⟨hy.1, hy.2.trans hx.2⟩).1)
  have cr₁ := continuous_radius_of_primitive hab cw₁ hr₁
  have cr₂ := continuous_radius_of_primitive hab cw₂ hr₂
  have hweight x (hx : x ∈ Icc a b) : w₁ x / r₁ x ≤ k ^ 2 * (w₂ x / r₂ x) := by
    rcases eq_or_lt_of_le hx.1 with hax | hax
    · subst x
      rw [hr₁ a (left_mem_Icc.mpr hab), hr₂ a (left_mem_Icc.mpr hab)]
      simp
    · have hr := hrpos x ⟨hax, hx.2⟩
      calc
        _ ≤ (k ^ 2 * w₂ x) / r₂ x := (div_le_div_iff₀ hr.1 hr.2).mpr (by
          calc
            _ ≤ (k * w₂ x) * r₂ x := mul_le_mul_of_nonneg_right (hwratio x hx).1 hr.2.le
            _ ≤ (k * w₂ x) * (k * r₁ x) := mul_le_mul_of_nonneg_left (hrratio x hx).1
              (mul_nonneg hk (hc.le.trans (hw x hx).2.2.1))
            _ = _ := by ring)
        _ = _ := by ring
  have hwpositive x (hx : x ∈ Icc a b) : 0 ≤ w₁ x / r₁ x := by
    have hr0 : 0 ≤ r₁ x := by
      rw [hr₁ x hx]
      exact intervalIntegral.integral_nonneg hx.1
        (fun y hy => hc.le.trans (hw y ⟨hy.1, hy.2.trans hx.2⟩).1)
    exact div_nonneg (hc.le.trans (hw x hx).1) hr0
  have imix : IntervalIntegrable (fun x => w₁ x / r₁ x * ‖f₂ x‖) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    apply (((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp im₂).const_mul (k ^ 2)).mono'
      (((cw₁.aestronglyMeasurable (μ := volume) measurableSet_Icc).div₀
        (cr₁.aestronglyMeasurable (μ := volume) measurableSet_Icc)).mul
          (cf₂.norm.aestronglyMeasurable (μ := volume) measurableSet_Icc))
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    change ‖w₁ x / r₁ x * ‖f₂ x‖‖ ≤ k ^ 2 * (w₂ x / r₂ x * ‖f₂ x‖)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hwpositive x hx) (norm_nonneg _))]
    exact (mul_le_mul_of_nonneg_right (hweight x hx) (norm_nonneg _)).trans_eq (by ring)
  have hmix : (∫ x in a..b, w₁ x / r₁ x * ‖f₂ x‖) ≤ k ^ 2 * (KH * L) := by
    have hi := intervalIntegral.integral_mono_on hab imix (im₂.const_mul (k ^ 2)) (fun x hx =>
      (mul_le_mul_of_nonneg_right (hweight x hx) (norm_nonneg _)).trans_eq (by ring))
    rw [intervalIntegral.integral_const_mul] at hi
    exact hi.trans (mul_le_mul_of_nonneg_left hm₂ (sq_nonneg _))
  have hqself x (hx : x ∈ Icc a b) : S₂.Q (p x).1 (p x).2 ^ 2 / r₂ x ^ 2 ≤ B * r₂ x ^ 2 := by
    have hpx := hp hx
    have hs : outSeg (p x).1 (p x).1 (p x).2 ⊆ triangle s t := by
      rintro ⟨qu, qv⟩ ⟨hqu, hq⟩
      change qu = (p x).1 at hqu
      subst qu
      exact ⟨hpx.1, hq.1, hq.2.trans hpx.2.2⟩
    have hq := charge_bound hS₂ hpx.2.1 hs
      (fun y hy => (hbox S₂ hmem₂ ((p x).1, y) (hs ⟨rfl, hy⟩)).2.2.1)
      (fun y hy => (hbox S₂ hmem₂ ((p x).1, y) (hs ⟨rfl, hy⟩)).2.2.2)
    have hq' : |S₂.Q (p x).1 (p x).2| ≤ (|e| * M * ε) * r₂ x ^ 2 := by
      apply hq.trans
      have h0 : 0 ≤ |e| * M * ε * r₂ x ^ 2 := by positivity
      linarith
    simpa only [B, mul_pow, sq_abs] using electric_square_le_of_charge_bound
      (show 0 ≤ |e| * M * ε by positivity) hq'
  have hF₂ x (hx : x ∈ Icc a b) : 0 ≤ F₂ x ∧ F₂ x ≤ ‖f₂ x‖ ^ 2 + B * r₂ x ^ 2 := by
    have hμ := mu_mem_Ico hS₂ (hp hx)
    refine ⟨add_nonneg (mul_nonneg (by linarith [hμ.2]) (sq_nonneg _))
      (div_nonneg (sq_nonneg _) (sq_nonneg _)), add_le_add ?_ (hqself x hx)⟩
    exact mul_le_of_le_one_left (sq_nonneg _) (by
      change 1 - S₂.mu (p x).1 (p x).2 ≤ 1
      linarith [hμ.1])
  have hδF x (hx : x ∈ Icc a b) : |F₁ x - F₂ x| ≤
      H * (‖f₁ x‖ + ‖f₂ x‖) + X * ‖f₂ x‖ ^ 2 + Bδ * r₁ x ^ 2 := by
    have hμ := mu_mem_Ico hS₁ (hp hx)
    have hδf : ‖f₁ x - f₂ x‖ ≤ H := by
      have hφ := hscalar s t e ε S₁ S₂ hS₁ hS₂ hε
        (fun q hq => (hbox S₁ hmem₁ q hq).1) hosc (p x).1 (p x).2 (hp hx)
      apply (hf x hx).2.2.trans
      dsimp [H]
      linarith
    have hδg : |(1 - μ₁ x) - (1 - μ₂ x)| ≤ X := by
      rw [show (1 - μ₁ x) - (1 - μ₂ x) = -(μ₁ x - μ₂ x) by ring, abs_neg]
      exact (abs_mu_sub_le_mass_ratio_distance hS₁ hS₂ (hp hx)).trans hμbound
    have hs := scalar_mass_difference_le_linear
      (show 0 ≤ 1 - μ₁ x by change 0 ≤ 1 - S₁.mu (p x).1 (p x).2; linarith [hμ.2])
      (show 1 - μ₁ x ≤ 1 by change 1 - S₁.mu (p x).1 (p x).2 ≤ 1; linarith [hμ.1])
      hH hX hδf hδg
    have hq := helectric s t e M ε S₁ S₂ hS₁ hS₂ hM hε hε1 hbox hosc
      (p x).1 (p x).2 (hp hx)
    have heq : F₁ x - F₂ x =
        ((1 - μ₁ x) * ‖f₁ x‖ ^ 2 - (1 - μ₂ x) * ‖f₂ x‖ ^ 2) +
          (S₁.Q (p x).1 (p x).2 ^ 2 / r₁ x ^ 2 - S₂.Q (p x).1 (p x).2 ^ 2 / r₂ x ^ 2) := by
      dsimp [F₁, F₂]; ring
    rw [heq]
    exact ((abs_add_le _ _).trans (add_le_add hs hq)).trans_eq (by dsimp [Bδ]; ring)
  obtain ⟨ii, hi⟩ := weighted_mass_difference_of_bounds hab hc hk hG hH hX hB hBδ hε
    cw₁ cw₂ cf₁.norm cf₂.norm (fun x hx => (hw x hx).1) (fun x hx => (hw x hx).2.2.1)
    hwratio hδw hr₁ hr₂ (fun x hx => (hrpos x hx).1) (fun x hx => (hrpos x hx).2)
    hrratio (fun x hx => abs_radius_sub_le_geometry_distance_mul_radius hS₁ hS₂ hfin (hp hx))
    (fun x hx => ⟨norm_nonneg _, (hf x hx).1⟩) (fun x hx => ⟨norm_nonneg _, (hf x hx).2.1⟩)
    hF₂ hδF iF₁ iF₂ hμ₁ hμ₂ im₁ imix hm₁ hmix hmom₁ hmom₂
  refine ⟨ii, hi.trans ?_⟩
  have hR0 : 0 ≤ r₁ b := by
    rw [hr₁ b (right_mem_Icc.mpr hab)]
    exact intervalIntegral.integral_nonneg hab (fun x hx => hc.le.trans (hw x hx).1)
  have hεsq : ε ^ 2 ≤ 1 := hsmall.trans (by norm_num)
  have hscalar : H * (KH * L + k ^ 2 * (KH * L)) +
      (X + KT * k ^ 2 * G) * ε * (k ^ 2 * (KH * L)) ≤ KS * L * E := by
    calc
      _ = ((1 + A) * (1 + k ^ 2) * KH) * L * E +
          (2 * Kμ * k ^ 2 * KH) * L * (ε ^ 2 * E) +
          (KT * k ^ 4 * KH) * L * (ε * G) := by dsimp [H, X]; ring
      _ ≤ ((1 + A) * (1 + k ^ 2) * KH) * L * E +
          (2 * Kμ * k ^ 2 * KH) * L * (1 * E) +
          (KT * k ^ 4 * KH) * L * E := by gcongr
      _ = _ := by dsimp [KS]; ring
  have hcharged : (Bδ + KT * k ^ 4 * G * B) * r₁ b ^ 2 / 6 ≤
      KQ * (e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2) * ε * E := by
    have hcoeff : Bδ + KT * k ^ 4 * G * B ≤
        (Kq + KT * k ^ 4) * e ^ 2 * M ^ 2 * ε * E := by
      calc
        _ = Kq * e ^ 2 * M ^ 2 * ε * E +
            (KT * k ^ 4 * e ^ 2 * M ^ 2 * ε) * (ε * G) := by dsimp [B, Bδ]; ring
        _ ≤ Kq * e ^ 2 * M ^ 2 * ε * E +
            (KT * k ^ 4 * e ^ 2 * M ^ 2 * ε) * E := by gcongr
        _ = _ := by ring
    calc
      _ ≤ ((Kq + KT * k ^ 4) * e ^ 2 * M ^ 2 * ε * E) * (C * (t - s)) ^ 2 / 6 := by gcongr
      _ ≤ ((Kq + KT * k ^ 4) * e ^ 2 * M ^ 2 * ε * E) * (C * (t - s)) ^ 2 := by
        have h0 : 0 ≤ ((Kq + KT * k ^ 4) * e ^ 2 * M ^ 2 * ε * E) *
            (C * (t - s)) ^ 2 := by positivity
        linarith
      _ = _ := by dsimp [KQ]; ring
  calc
    _ ≤ KS * L * E + KQ * (e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2) * ε * E :=
      add_le_add hscalar hcharged
    _ ≤ K * L * E + K * (e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2) * ε * E := by
      have hSK : KS ≤ K := by dsimp [K]; linarith
      have hQK : KQ ≤ K := by dsimp [K]; linarith
      gcongr
    _ = _ := by dsimp [E, G]; ring

end EmcsfAcExtension.Local.Broad
