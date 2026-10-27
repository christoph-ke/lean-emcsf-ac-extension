module

public import EmcsfAcExtension.Local.Broad.ContractionSection
public import EmcsfAcExtension.Local.Broad.ContractionElectric
public import EmcsfAcExtension.Local.Broad.ContractionMassOutgoing
public import EmcsfAcExtension.Local.Broad.ContractionSources
public import EmcsfAcExtension.Local.Broad.ContractionFTC
public import EmcsfAcExtension.Local.Broad.OutgoingMass

/-! # Outgoing transport of the incoming normalized scalar

The axis value is retained as an explicit term. No incoming AC regularity
of the normalized incoming field is assumed or used.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Broad

/-- [node restart-stab-broad-uniqueness#incoming-scalar-contraction]
The incoming normalized scalar is bounded by its outgoing axis difference
and the small transport cost from internal project record (Sb),
charged_SF_new_version.tex:L5871–5892.
The positive constant depends only on `c,C`, before all triangle, coupling,
scalar, variation and solution parameters. -/
theorem incoming_scalar_contraction (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s t e M ε L : ℝ) (S₁ S₂ : Fields),
      IsSolution e S₁ (triangle s t) → IsSolution e S₂ (triangle s t) →
      1 ≤ M → 0 ≤ ε → ε ≤ 1 → ε ^ 2 ≤ 1 / 2 → 0 ≤ L →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s t,
        c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C ∧ c ≤ -S.nu p.1 p.2 ∧
        -S.nu p.1 p.2 ≤ C ∧ c ≤ 1 - S.mu p.1 p.2 ∧ ‖S.phi p.1 p.2‖ ≤ M ∧
        ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ ε ∧ ‖S.xi p.1 p.2 / S.nu p.1 p.2‖ ≤ ε) →
      (∀ u v, (u, v) ∈ triangle s t → ∀ x ∈ Icc u v, ∀ y ∈ Icc u v,
        ‖S₂.a u x - S₂.a u y‖ ≤ ε) →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ u v, (u, v) ∈ triangle s t →
        eVariationOn (S.a u) (Icc u v) ≤ ENNReal.ofReal L) →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ v ∈ Icc s t,
        eVariationOn (fun x => S.b x v) (Icc s v) ≤ ENNReal.ofReal L) →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ u ∈ Icc s t, S.A u u = 0) →
      e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2 ≤ 1 →
      ∀ u v, (u, v) ∈ triangle s t →
      ‖S₁.b u v - S₂.b u v‖ ≤ ‖S₁.a u u - S₂.a u u‖ +
        K * (ε * L + e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2) *
          ((normalized_field_distance s t S₁ S₂).toReal +
            ε * (geometry_distance s t S₁ S₂).toReal) := by
  obtain ⟨KM, hKM, hmass⟩ := outgoing_undifferenced_mass_budget C hC
  obtain ⟨KD, hKD, hdiff⟩ := outgoing_mass_difference c C hc hC
  obtain ⟨KG, hKG, hgeom⟩ := section_geometric_scalar_source_of_mass_budgets c C KM KD
    hc hC hKM.le hKD.le
  obtain ⟨KE, hKE, helec⟩ := section_electric_scalar_source_difference c C hc hC
  let K := KG + KE + 1
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro s t e M ε L S₁ S₂ hS₁ hS₂ hM hε hε1 hsmall hL hbox hosc hvo _hvi _haxis hσ
    u v huv
  let E := (normalized_field_distance s t S₁ S₂).toReal +
    ε * (geometry_distance s t S₁ S₂).toReal
  let σ := e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hσ0 : 0 ≤ σ := by dsimp [σ]; positivity
  have hu : u ∈ Icc s t := ⟨huv.1, huv.2.1.trans huv.2.2⟩
  have hs : outSeg u u t ⊆ triangle s t := by
    rintro p ⟨rfl, hx⟩
    exact ⟨hu.1, hx.1, hx.2⟩
  have hboxM : ∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s t,
      c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C ∧ ‖S.phi p.1 p.2‖ ≤ M ∧
        ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ ε := by
    intro S hm p hp
    rcases hbox S hm p hp with ⟨hl, hl', hn, hn', hg, hφ, hθ, hξ⟩
    exact ⟨hl, hl', hφ, hθ⟩
  have hvar S (hm : S ∈ ({S₁, S₂} : Set Fields)) u (hu : u ∈ Icc s t) :=
    hvo S hm u t ⟨hu.1, hu.2, le_rfl⟩
  have hm {S : Fields} (hS : IsSolution e S (triangle s t))
      (hmem : S ∈ ({S₁, S₂} : Set Fields)) := hmass s t e M ε L S hS
    (zero_le_one.trans hM) hε hL
    (fun p hp => ⟨(hboxM S hmem p hp).2.1, (hboxM S hmem p hp).2.2.1,
      (hboxM S hmem p hp).2.2.2⟩) (hvar S hmem) u hu
  have hd := hdiff s t e M ε L S₁ S₂ hS₁ hS₂ hM hε hε1 hsmall hL hboxM
    hosc hvar hσ u hu
  have hfin := geometry_distance_ne_top hS₁ hS₂ hc
    (fun p hp => (hboxM S₁ (by simp) p hp).1)
  have hw x (hx : x ∈ Icc u t) : c ≤ S₁.lam u x ∧ S₁.lam u x ≤ C ∧
      c ≤ S₂.lam u x ∧ S₂.lam u x ≤ C :=
    ⟨(hboxM S₁ (by simp) (u, x) (hs ⟨rfl, hx⟩)).1,
      (hboxM S₁ (by simp) (u, x) (hs ⟨rfl, hx⟩)).2.1,
      (hboxM S₂ (by simp) (u, x) (hs ⟨rfl, hx⟩)).1,
      (hboxM S₂ (by simp) (u, x) (hs ⟨rfl, hx⟩)).2.1⟩
  have hδw x (hx : x ∈ Icc u t) : |S₁.lam u x - S₂.lam u x| ≤
      (geometry_distance s t S₁ S₂).toReal :=
    abs_lam_sub_le_geometry_distance hS₁ hfin (hs ⟨rfl, hx⟩)
  have hR0 : 0 ≤ S₁.r u t := by
    rcases eq_or_lt_of_le hu.2 with he | he
    · subst t; exact (hS₁.axis u ⟨hu.1, le_rfl, le_rfl⟩).1.symm.le
    · exact (hS₁.r_pos (u, t) ⟨hu.1, hu.2, le_rfl⟩ he).le
  have hR : S₁.r u t ≤ C * (t - s) :=
    (outgoing_radius_upper hS₁ hu.2 hs
      (fun x hx => (hw x hx).2.1)).trans
      (mul_le_mul_of_nonneg_left (sub_le_sub_left hu.1 t) hC)
  have hmom : (∫ x in u..t, S₁.lam u x * S₁.r u x) = S₁.r u t ^ 2 / 2 := by
    convert outgoing_radius_moment hS₁ hu.2 hs 1 using 1 <;> norm_num
  have hgap := fun S hm p hp => (hbox S hm p hp).2.2.2.2.1
  obtain ⟨ig, hg⟩ := hgeom s t e M ε L S₁ S₂ hS₁ hS₂ hM hε hε1 hL hboxM hgap hosc hσ
    u t (S₁.r u t) (fun x => (u, x)) (S₁.lam u) (S₂.lam u)
    (fun x => S₁.xi u x / S₁.nu u x) (fun x => S₂.xi u x / S₂.nu u x)
    hu.2 (continuous_const.prodMk continuous_id).continuousOn
    (fun x hx => hs ⟨rfl, hx⟩)
    (continuousOn_out_section hS₁.cont_lam hs) (continuousOn_out_section hS₂.cont_lam hs)
    (continuousOn_out_section (f := fun x y => S₁.xi x y / S₁.nu x y)
      (IsSolution.cont_incoming_ratio hS₁) hs)
    (continuousOn_out_section (f := fun x y => S₂.xi x y / S₂.nu x y)
      (IsSolution.cont_incoming_ratio hS₂) hs) hw hδw
    (fun x hx => ⟨(hbox S₂ (by simp) (u, x) (hs ⟨rfl, hx⟩)).2.2.2.2.2.2.2,
      (norm_ratio_sub_le_distance_add_scalar hS₁ hS₂ (hs ⟨rfl, hx⟩)).2⟩)
    hR0 hR hmom (hm hS₁ (by simp)).1 (hm hS₂ (by simp)).1 hd.1
    (by convert (hm hS₁ (by simp)).2.2 using 1; ring)
    (by convert (hm hS₂ (by simp)).2.2 using 1; ring)
    (by convert hd.2 using 1; ring)
  obtain ⟨ie, he⟩ := helec s t e M ε S₁ S₂ hS₁ hS₂ hM hε hε1 hsmall hboxM hgap hosc hσ
    u t (fun x => (u, x)) (S₁.lam u) (S₂.lam u) (S₁.r u t) hu.2
    (continuous_const.prodMk continuous_id).continuousOn (fun x hx => hs ⟨rfl, hx⟩)
    (continuousOn_out_section hS₁.cont_lam hs) (continuousOn_out_section hS₂.cont_lam hs)
    hw hδw hR0 hR hmom
  let sg : ℝ → ℂ := fun x =>
    ((S₁.lam u x / S₁.r u x : ℝ) : ℂ) *
      (((S₁.mu u x - S₁.Q u x ^ 2 / S₁.r u x ^ 2) / (1 - S₁.mu u x) : ℝ) : ℂ) *
        (S₁.xi u x / S₁.nu u x) -
    ((S₂.lam u x / S₂.r u x : ℝ) : ℂ) *
      (((S₂.mu u x - S₂.Q u x ^ 2 / S₂.r u x ^ 2) / (1 - S₂.mu u x) : ℝ) : ℂ) *
        (S₂.xi u x / S₂.nu u x)
  let se : ℝ → ℂ := fun x => I * e *
    (((S₁.lam u x : ℂ) / S₁.r u x) * S₁.Q u x * S₁.phi u x / (1 - S₁.mu u x) -
      ((S₂.lam u x : ℂ) / S₂.r u x) * S₂.Q u x * S₂.phi u x / (1 - S₂.mu u x))
  change IntervalIntegrable sg volume u t at ig
  change (∫ x in u..t, ‖sg x‖) ≤ KG * (ε * L + σ) * E at hg
  change IntervalIntegrable se volume u t at ie
  change (∫ x in u..t, ‖se x‖) ≤ KE * σ * E at he
  have hh := norm_increment_le_three_integrals (g := fun x => -sg x) (h := se) (k := fun _ => 0)
    hu.2 ((continuousOn_out_section (IsSolution.cont_b hS₁) hs).sub
      (continuousOn_out_section (IsSolution.cont_b hS₂) hs))
    (fun x hx => by
      apply ((hasDerivAt_b_out_real_coefficients hS₁ hs hx).sub
        (hasDerivAt_b_out_real_coefficients hS₂ hs hx)).congr_deriv
      dsimp [sg, se]
      push_cast
      ring) ig.neg ie intervalIntegrable_const ⟨huv.2.1, huv.2.2⟩
  simp only [norm_neg, norm_zero, intervalIntegral.integral_zero, add_zero] at hh
  have haxis₁ := hS₁.axis u ⟨hu.1, le_rfl, hu.2⟩
  have haxis₂ := hS₂.axis u ⟨hu.1, le_rfl, hu.2⟩
  have hba : S₁.b u u - S₂.b u u = S₁.a u u - S₂.a u u := by
    rw [haxis₁.2.2.2.2.2, haxis₂.2.2.2.2.2, haxis₁.2.2.2.2.1, haxis₂.2.2.2.2.1]
  change ‖(S₁.b u v - S₂.b u v) - (S₁.b u u - S₂.b u u)‖ ≤ _ at hh
  rw [hba] at hh
  calc
    _ ≤ ‖S₁.b u u - S₂.b u u‖ + ‖(S₁.b u v - S₂.b u v) - (S₁.b u u - S₂.b u u)‖ := by
      simpa only [add_sub_cancel] using norm_add_le (S₁.b u u - S₂.b u u)
        ((S₁.b u v - S₂.b u v) - (S₁.b u u - S₂.b u u))
    _ ≤ ‖S₁.a u u - S₂.a u u‖ + (KG * (ε * L + σ) * E + KE * σ * E) := by
      rw [hba]
      exact add_le_add le_rfl (hh.trans (add_le_add hg he))
    _ ≤ ‖S₁.a u u - S₂.a u u‖ + K * (ε * L + σ) * E := by
      have hle : σ ≤ ε * L + σ := le_add_of_nonneg_left (mul_nonneg hε hL)
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hKE.le) hE
      have hh' : 0 ≤ (ε * L + σ) * E := by positivity
      dsimp [K]
      nlinarith only [hh, hh']

end EmcsfAcExtension.Local.Broad
