module

public import EmcsfAcExtension.Local.Broad.ContractionBudget
public import EmcsfAcExtension.Local.Broad.ContractionCharge
public import EmcsfAcExtension.Local.Broad.GeometryContinuity

/-! # Both oriented geometric scalar-source comparisons

The matching mass budgets are explicit inputs to this helper. Its callers
supply the incoming and outgoing budgets from their separate graph nodes.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Broad

/-- A geometric scalar-source difference has an integrable norm with cost
`K(εL+σ)(D+εG)`. The constant depends only on the geometric box `c,C` and
the supplied uniform mass-budget coefficients `KM,KD`, before all solution
parameters, characteristic sections and scalar traces. -/
theorem section_geometric_scalar_source_of_mass_budgets
    (c C KM KD : ℝ) (hc : 0 < c) (hC : 0 ≤ C) (hKM : 0 ≤ KM) (hKD : 0 ≤ KD) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s t e M ε L : ℝ) (S₁ S₂ : Fields),
      IsSolution e S₁ (triangle s t) → IsSolution e S₂ (triangle s t) →
      1 ≤ M → 0 ≤ ε → ε ≤ 1 → 0 ≤ L →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s t,
        c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C ∧ ‖S.phi p.1 p.2‖ ≤ M ∧
          ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ ε) →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s t, c ≤ 1 - S.mu p.1 p.2) →
      (∀ u v, (u, v) ∈ triangle s t → ∀ x ∈ Icc u v, ∀ y ∈ Icc u v,
        ‖S₂.a u x - S₂.a u y‖ ≤ ε) →
      e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2 ≤ 1 →
      ∀ (a b R : ℝ) (p : ℝ → ℝ × ℝ) (w₁ w₂ : ℝ → ℝ) (z₁ z₂ : ℝ → ℂ),
      a ≤ b → ContinuousOn p (Icc a b) → MapsTo p (Icc a b) (triangle s t) →
      ContinuousOn w₁ (Icc a b) → ContinuousOn w₂ (Icc a b) →
      ContinuousOn z₁ (Icc a b) → ContinuousOn z₂ (Icc a b) →
      (∀ x ∈ Icc a b, c ≤ w₁ x ∧ w₁ x ≤ C ∧ c ≤ w₂ x ∧ w₂ x ≤ C) →
      (∀ x ∈ Icc a b, |w₁ x - w₂ x| ≤ (geometry_distance s t S₁ S₂).toReal) →
      (∀ x ∈ Icc a b, ‖z₂ x‖ ≤ ε ∧ ‖z₁ x - z₂ x‖ ≤
        (normalized_field_distance s t S₁ S₂).toReal +
          ‖S₁.phi (p x).1 (p x).2 - S₂.phi (p x).1 (p x).2‖) →
      0 ≤ R → R ≤ C * (t - s) →
      (∫ x in a..b, w₁ x * S₁.r (p x).1 (p x).2) = R ^ 2 / 2 →
      let d₁ := fun x => w₁ x / S₁.r (p x).1 (p x).2
      let d₂ := fun x => w₂ x / S₂.r (p x).1 (p x).2
      let μ₁ := fun x => S₁.mu (p x).1 (p x).2
      let μ₂ := fun x => S₂.mu (p x).1 (p x).2
      let E := (normalized_field_distance s t S₁ S₂).toReal +
        ε * (geometry_distance s t S₁ S₂).toReal
      let σ := e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2
      IntervalIntegrable (fun x => d₁ x * μ₁ x) volume a b →
      IntervalIntegrable (fun x => d₂ x * μ₂ x) volume a b →
      IntervalIntegrable (fun x => d₁ x * |μ₁ x - μ₂ x|) volume a b →
      (∫ x in a..b, d₁ x * μ₁ x) ≤ KM * (ε * L + σ * ε ^ 2) →
      (∫ x in a..b, d₂ x * μ₂ x) ≤ KM * (ε * L + σ * ε ^ 2) →
      (∫ x in a..b, d₁ x * |μ₁ x - μ₂ x|) ≤ KD * (L + σ * ε) * E →
      let F₁ : ℝ → ℝ := fun x => (μ₁ x - S₁.Q (p x).1 (p x).2 ^ 2 /
        S₁.r (p x).1 (p x).2 ^ 2) / (1 - μ₁ x)
      let F₂ : ℝ → ℝ := fun x => (μ₂ x - S₂.Q (p x).1 (p x).2 ^ 2 /
        S₂.r (p x).1 (p x).2 ^ 2) / (1 - μ₂ x)
      IntervalIntegrable (fun x => (d₁ x : ℂ) * (F₁ x : ℂ) * z₁ x -
        (d₂ x : ℂ) * (F₂ x : ℂ) * z₂ x) volume a b ∧
      (∫ x in a..b, ‖(d₁ x : ℂ) * (F₁ x : ℂ) * z₁ x - (d₂ x : ℂ) * (F₂ x : ℂ) * z₂ x‖) ≤
        K * (ε * L + σ) * E := by
  obtain ⟨A, hA, hscalar⟩ := scalar_average_difference_bound c hc
  obtain ⟨Kq, hKq, hcharge⟩ := charged_square_difference c C hc hC
  let k := C / c
  let W := k ^ 2
  let KB := (1 + C * k) / c
  let KQ := 2 * C ^ 2 * (1 + k ^ 2)
  let KδQ := 2 * C ^ 2 * Kq
  have hk : 0 ≤ k := div_nonneg hC hc.le
  have hKB : 0 ≤ KB := by dsimp [KB]; positivity
  obtain ⟨K, hK, hbudget⟩ := scalar_source_integral_of_budgets c (4 * C ^ 2) W KB (1 + A)
    KM KQ KD KδQ hc (by positivity) (by dsimp [W]; positivity) hKB (by positivity)
    hKM (by dsimp [KQ]; positivity) hKD (by dsimp [KδQ]; positivity)
  refine ⟨K, hK, ?_⟩
  intro s t e M ε L S₁ S₂ hS₁ hS₂ hM hε hε1 hL hbox hgap hosc hσ
    a b R p w₁ w₂ z₁ z₂ hab cp hp cw₁ cw₂ cz₁ cz₂ hw hδw hz hR0 hR hmom
    d₁ d₂ μ₁ μ₂ E σ im₁ im₂ imd hm₁ hm₂ hmd F₁ F₂
  let r₁ := fun x => S₁.r (p x).1 (p x).2
  let q₁ := fun x => S₁.Q (p x).1 (p x).2 ^ 2 / r₁ x ^ 2
  let q₂ := fun x => S₂.Q (p x).1 (p x).2 ^ 2 / S₂.r (p x).1 (p x).2 ^ 2
  let B := e ^ 2 * M ^ 2 * ε ^ 2
  let Bδ := Kq * e ^ 2 * M ^ 2 * ε * E
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hσ0 : 0 ≤ σ := by dsimp [σ]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hBδ : 0 ≤ Bδ := by dsimp [Bδ]; positivity
  have sect {f : ℝ → ℝ → ℝ} (hf : ContinuousOn (Function.uncurry f) (triangle s t)) :=
    hf.comp cp hp
  have cr := sect hS₁.cont_r
  have mμ₁ := (sect (continuousOn_mu hS₁)).aestronglyMeasurable (μ := volume) measurableSet_Icc
  have mμ₂ := (sect (continuousOn_mu hS₂)).aestronglyMeasurable (μ := volume) measurableSet_Icc
  have mq₁ := ((sect hS₁.cont_Q).pow 2).aestronglyMeasurable (μ := volume) measurableSet_Icc |>.div₀
    ((cr.pow 2).aestronglyMeasurable (μ := volume) measurableSet_Icc)
  have mq₂ := ((sect hS₂.cont_Q).pow 2).aestronglyMeasurable (μ := volume) measurableSet_Icc |>.div₀
    (((sect hS₂.cont_r).pow 2).aestronglyMeasurable (μ := volume) measurableSet_Icc)
  have md := (cw₁.aestronglyMeasurable (μ := volume) measurableSet_Icc).div₀
    (cr.aestronglyMeasurable (μ := volume) measurableSet_Icc)
  have hr0 x (hx : x ∈ Icc a b) : 0 ≤ r₁ x := by
    have hpx := hp hx
    rcases eq_or_lt_of_le (show (p x).1 ≤ (p x).2 from hpx.2.1) with he | he
    · dsimp [r₁]
      rw [← he]
      exact (hS₁.axis (p x).1 ⟨hpx.1, le_rfl, he.symm ▸ hpx.2.2⟩).1.symm.le
    · exact (hS₁.r_pos (p x) hpx he).le
  have hq x (hx : x ∈ Icc a b) := electric_square_pointwise_bounds hc hC hS₁ hS₂
    (zero_le_one.trans hM) hε hε1 hbox hσ (hp hx)
  obtain ⟨iq₁, hq₁⟩ := weighted_quadratic_integral_of_bounds hab hB cw₁ cr mq₁
    (fun x hx => hc.le.trans (hw x hx).1) hr0 (fun x hx => (hq x hx).1) hmom
  obtain ⟨iq₂, hq₂⟩ := weighted_quadratic_integral_of_bounds hab (mul_nonneg hB (sq_nonneg k))
    cw₁ cr mq₂ (fun x hx => hc.le.trans (hw x hx).1) hr0
    (fun x hx => (hq x hx).2.1) hmom
  obtain ⟨iqd, hqd⟩ := weighted_quadratic_integral_of_bounds hab hBδ cw₁ cr
    ((mq₁.sub mq₂).norm) (fun x hx => hc.le.trans (hw x hx).1) hr0
    (fun x hx => ⟨abs_nonneg _, by
      have hh := hcharge s t e M ε S₁ S₂ hS₁ hS₂ hM hε hε1 hbox hosc
        (p x).1 (p x).2 (hp hx)
      exact hh.trans_eq (by dsimp [Bδ, E, r₁, Function.uncurry]; ring)⟩) hmom
  have hst : 0 ≤ t - s := by
    have hpa := hp ⟨le_rfl, hab⟩
    linarith [hpa.1, hpa.2.1, hpa.2.2]
  have hR2 : R ^ 2 ≤ (C * (t - s)) ^ 2 := (sq_le_sq₀ hR0 (mul_nonneg hC hst)).mpr hR
  have bound (T : ℝ) (hT : 0 ≤ T) : T * B * R ^ 2 / 2 ≤ 2 * C ^ 2 * T * σ * ε ^ 2 := by
    calc
      _ ≤ T * B * (C * (t - s)) ^ 2 / 2 := by gcongr
      _ = _ := by dsimp [B, σ]; ring
  have hq₁' : (∫ x in a..b, d₁ x * q₁ x) ≤ KQ * σ * ε ^ 2 := by
    apply hq₁.trans
    have hh := bound 1 zero_le_one
    have hh' : 0 ≤ 2 * C ^ 2 * k ^ 2 * σ * ε ^ 2 := by positivity
    dsimp [KQ]
    nlinarith only [hh, hh']
  have hq₂' : (∫ x in a..b, d₁ x * q₂ x) ≤ KQ * σ * ε ^ 2 := by
    apply hq₂.trans
    have hh := bound (k ^ 2) (sq_nonneg _)
    have hh' : 0 ≤ 2 * C ^ 2 * σ * ε ^ 2 := by positivity
    dsimp [KQ]
    nlinarith only [hh, hh']
  have hqd' : (∫ x in a..b, d₁ x * |q₁ x - q₂ x|) ≤ KδQ * σ * ε * E := by
    apply hqd.trans
    calc
      _ ≤ Bδ * (C * (t - s)) ^ 2 / 2 := by gcongr
      _ = _ := by dsimp [Bδ, KδQ, σ]; ring
  have hpoint x (hx : x ∈ Icc a b) := radial_weights_of_solution_box hc hC hS₁ hS₂
    (fun S hm q hq => ⟨(hbox S hm q hq).1, (hbox S hm q hq).2.1⟩) (hp hx) (hw x hx) (hδw x hx)
  have h1 : AEStronglyMeasurable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Icc a b)) :=
    aestronglyMeasurable_const
  have realcast {f : ℝ → ℝ} (hf : AEStronglyMeasurable f (volume.restrict (Icc a b))) :
      AEStronglyMeasurable (fun x => (f x : ℂ)) (volume.restrict (Icc a b)) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hf
  have md₂ := (cw₂.aestronglyMeasurable (μ := volume) measurableSet_Icc).div₀
    ((sect hS₂.cont_r).aestronglyMeasurable (μ := volume) measurableSet_Icc)
  have ms : AEStronglyMeasurable (fun x => (d₁ x : ℂ) * (F₁ x : ℂ) * z₁ x -
      (d₂ x : ℂ) * (F₂ x : ℂ) * z₂ x) (volume.restrict (Icc a b)) := by
    have hh := ((realcast md).mul (realcast ((mμ₁.sub mq₁).div₀ (h1.sub mμ₁))) |>.mul
      (cz₁.aestronglyMeasurable measurableSet_Icc)).sub
      ((realcast md₂).mul (realcast ((mμ₂.sub mq₂).div₀ (h1.sub mμ₂))) |>.mul
        (cz₂.aestronglyMeasurable measurableSet_Icc))
    apply hh.congr
    filter_upwards [] with x
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply, Function.comp_apply,
      Function.uncurry_def, F₁, F₂, d₁, d₂, μ₁, μ₂]
  apply hbudget a b ε σ L E (geometry_distance s t S₁ S₂).toReal d₁ d₂ μ₁ μ₂ q₁ q₂ z₁ z₂
    hab hε hε1 hσ0 hL hE ENNReal.toReal_nonneg
    (le_add_of_nonneg_left ENNReal.toReal_nonneg) md mμ₁ mμ₂ mq₁ mq₂
    (fun x hx => ⟨div_nonneg (hc.le.trans (hw x hx).1) (hr0 x hx), (hpoint x hx).1⟩)
    (fun x hx => ⟨(mu_mem_Ico hS₁ (hp hx)).1, (mu_mem_Ico hS₂ (hp hx)).1,
      (mu_mem_Ico hS₂ (hp hx)).2.le⟩)
    (fun x hx => ⟨(hq x hx).1.1, (hq x hx).2.1.1, (hq x hx).2.2⟩)
    (fun x hx => ⟨hgap S₁ (by simp) (p x) (hp hx), hgap S₂ (by simp) (p x) (hp hx)⟩)
    (fun x hx => (hpoint x hx).2)
    (fun x hx => ⟨(hz x hx).1, ((hz x hx).2).trans (by
      have hh := hscalar s t e ε S₁ S₂ hS₁ hS₂ hε
        (fun q hq => (hbox S₁ (by simp) q hq).1) hosc (p x).1 (p x).2 (hp hx)
      have hD : (normalized_field_distance s t S₁ S₂).toReal ≤ E := by
        exact le_add_of_nonneg_right (by positivity)
      nlinarith only [hh, hD])⟩)
    im₁ im₂ imd iq₁ iq₂ iqd hm₁ hm₂ hmd hq₁' hq₂' hqd' ms

end EmcsfAcExtension.Local.Broad
