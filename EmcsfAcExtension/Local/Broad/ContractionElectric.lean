module

public import EmcsfAcExtension.Local.Broad.ContractionElectricBounds
public import EmcsfAcExtension.Local.Broad.GeometryContinuity

/-! # Sectional electric scalar-source budgets

The section keeps its natural radial Jacobian. Incoming and outgoing
callers discharge the exact quadratic radius moment separately.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Broad

/-- The electric scalar forcing has an integrable difference with budget
`K*σ*(D+εG)` on either oriented complete section. For fixed `c,C`, the
positive constant is chosen before all triangle, coupling, scalar and
section parameters. The moment and radius premises are exact geometric
identities/bounds discharged by the two orientation callers. -/
theorem section_electric_scalar_source_difference (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s t e M ε : ℝ) (S₁ S₂ : Fields),
      IsSolution e S₁ (triangle s t) → IsSolution e S₂ (triangle s t) →
      1 ≤ M → 0 ≤ ε → ε ≤ 1 → ε ^ 2 ≤ 1 / 2 →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s t,
        c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C ∧
        ‖S.phi p.1 p.2‖ ≤ M ∧ ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ ε) →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s t, c ≤ 1 - S.mu p.1 p.2) →
      (∀ u v, (u, v) ∈ triangle s t → ∀ x ∈ Icc u v, ∀ y ∈ Icc u v,
        ‖S₂.a u x - S₂.a u y‖ ≤ ε) →
      e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2 ≤ 1 →
      ∀ (a b : ℝ) (p : ℝ → ℝ × ℝ) (w₁ w₂ : ℝ → ℝ) (R : ℝ),
      a ≤ b → ContinuousOn p (Icc a b) → MapsTo p (Icc a b) (triangle s t) →
      ContinuousOn w₁ (Icc a b) → ContinuousOn w₂ (Icc a b) →
      (∀ x ∈ Icc a b, c ≤ w₁ x ∧ w₁ x ≤ C ∧ c ≤ w₂ x ∧ w₂ x ≤ C) →
      (∀ x ∈ Icc a b, |w₁ x - w₂ x| ≤ (geometry_distance s t S₁ S₂).toReal) →
      0 ≤ R → R ≤ C * (t - s) →
      (∫ x in a..b, w₁ x * S₁.r (p x).1 (p x).2) = R ^ 2 / 2 →
      let F := fun x => I * e *
        (((w₁ x : ℂ) / S₁.r (p x).1 (p x).2) * S₁.Q (p x).1 (p x).2 * S₁.phi (p x).1 (p x).2 /
          (1 - S₁.mu (p x).1 (p x).2) -
        ((w₂ x : ℂ) / S₂.r (p x).1 (p x).2) * S₂.Q (p x).1 (p x).2 * S₂.phi (p x).1 (p x).2 /
          (1 - S₂.mu (p x).1 (p x).2))
      let E := (normalized_field_distance s t S₁ S₂).toReal +
        ε * (geometry_distance s t S₁ S₂).toReal
      IntervalIntegrable F volume a b ∧ (∫ x in a..b, ‖F x‖) ≤
        K * (e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2) * E := by
  obtain ⟨Ke, hKe, helectric⟩ := electric_scalar_source_difference c C hc hC
  let K := 2 * Ke * C ^ 2 + 1
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro s t e M ε S₁ S₂ hS₁ hS₂ hM hε hε1 hsmall hbox hgap hosc hσ a b p w₁ w₂ R
    hab cp hp cw₁ cw₂ hw hδw hR0 hR hmom F E
  have sect {f : ℝ → ℝ → ℝ} (hf : ContinuousOn (Function.uncurry f) (triangle s t)) := hf.comp cp hp
  have cr₁ := sect hS₁.cont_r
  have cr₂ := sect hS₂.cont_r
  have cq₁ := sect hS₁.cont_Q
  have cq₂ := sect hS₂.cont_Q
  have cμ₁ := sect (continuousOn_mu hS₁)
  have cμ₂ := sect (continuousOn_mu hS₂)
  have cφ₁ := hS₁.cont_phi.comp cp hp
  have cφ₂ := hS₂.cont_phi.comp cp hp
  have realcast {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) :
      AEStronglyMeasurable (fun x => (f x : ℂ)) (volume.restrict (Icc a b)) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable (hf.aestronglyMeasurable measurableSet_Icc)
  have hmeas : AEStronglyMeasurable F (volume.restrict (Icc a b)) := by
    have hI : AEStronglyMeasurable (fun _ : ℝ => I) (volume.restrict (Icc a b)) :=
      aestronglyMeasurable_const
    have he : AEStronglyMeasurable (fun _ : ℝ => (e : ℂ)) (volume.restrict (Icc a b)) :=
      aestronglyMeasurable_const
    have h1 : AEStronglyMeasurable (fun _ : ℝ => (1 : ℂ)) (volume.restrict (Icc a b)) :=
      aestronglyMeasurable_const
    have hh := (hI.mul he).mul
      (((((realcast cw₁).div₀ (realcast cr₁)).mul (realcast cq₁)).mul
        (cφ₁.aestronglyMeasurable measurableSet_Icc)).div₀
          (h1.sub (realcast cμ₁)) |>.sub
      (((((realcast cw₂).div₀ (realcast cr₂)).mul (realcast cq₂)).mul
        (cφ₂.aestronglyMeasurable measurableSet_Icc)).div₀
          (h1.sub (realcast cμ₂))))
    apply hh.congr
    filter_upwards [] with x
    simp only [F, Pi.mul_apply, Pi.sub_apply, Pi.div_apply, Function.comp_apply,
      Function.uncurry_def]
  let N := fun x => Ke * e ^ 2 * M ^ 2 * E * (w₁ x * S₁.r (p x).1 (p x).2)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have iN : IntervalIntegrable N volume a b :=
    (ContinuousOn.intervalIntegrable_of_Icc hab (cw₁.mul cr₁)).const_mul _
  have hmaj x (hx : x ∈ Icc a b) : ‖F x‖ ≤ N x :=
    helectric s t e M ε S₁ S₂ hS₁ hS₂ hM hε hε1 hsmall hbox hgap hosc hσ
      (p x).1 (p x).2 (hp hx) (w₁ x) (w₂ x) (hw x hx).1 (hw x hx).2.1
      (hw x hx).2.2.1 (hw x hx).2.2.2 (hδw x hx)
  have ii : IntervalIntegrable F volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    apply ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp iN).mono' hmeas
    exact (ae_restrict_mem measurableSet_Icc).mono (fun x hx => hmaj x hx)
  refine ⟨ii, (intervalIntegral.integral_mono_on hab ii.norm iN hmaj).trans ?_⟩
  change (∫ x in a..b, Ke * e ^ 2 * M ^ 2 * E * (w₁ x * S₁.r (p x).1 (p x).2)) ≤
    K * (e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2) * E
  rw [intervalIntegral.integral_const_mul, hmom]
  have hst : 0 ≤ t - s := by
    have hpa := hp ⟨le_rfl, hab⟩
    linarith [hpa.1, hpa.2.1, hpa.2.2]
  have hR2 : R ^ 2 ≤ (C * (t - s)) ^ 2 := (sq_le_sq₀ hR0 (mul_nonneg hC hst)).mpr hR
  calc
    _ ≤ Ke * e ^ 2 * M ^ 2 * E * ((C * (t - s)) ^ 2 / 2) := by gcongr
    _ = (2 * Ke * C ^ 2) * (e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2) * E := by ring
    _ ≤ K * (e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2) * E := by
      gcongr
      dsimp [K]
      linarith

end EmcsfAcExtension.Local.Broad
