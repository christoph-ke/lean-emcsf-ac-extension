module

public import EmcsfAcExtension.Local.Broad.ContractionSection
public import EmcsfAcExtension.Local.Broad.ContractionElectric
public import EmcsfAcExtension.Local.Broad.ContractionMassIncoming
public import EmcsfAcExtension.Local.Broad.ContractionSources
public import EmcsfAcExtension.Local.Broad.ContractionFTC
public import EmcsfAcExtension.Local.Broad.IncomingMass
public import EmcsfAcExtension.Local.Broad.Potential

/-! # Incoming transport contracts the outgoing normalized scalar

Both undifferenced and differenced incoming mass budgets are used. The
ordinary connection term is estimated in the zero-axis gauge.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Broad

/-- [node restart-stab-broad-uniqueness#outgoing-scalar-contraction]
The outgoing normalized scalar obeys the small difference bound from
internal project record (Sa), charged_SF_new_version.tex:L5839–5861. The positive constant depends
only on `c,C`, before the triangle, coupling, scalar, variation and solution
parameters. The finite variation budget need not be small. -/
theorem outgoing_scalar_contraction (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C) :
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
      (∀ v ∈ Icc s t, S₁.r s v = S₂.r s v ∧ S₁.a s v = S₂.a s v) →
      e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2 ≤ 1 →
      ∀ u v, (u, v) ∈ triangle s t →
      ‖S₁.a u v - S₂.a u v‖ ≤
        K * (ε * L + e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2) *
          ((normalized_field_distance s t S₁ S₂).toReal +
            ε * (geometry_distance s t S₁ S₂).toReal) := by
  obtain ⟨KM, hKM, hmass⟩ := incoming_undifferenced_mass_budget c C hc hC
  obtain ⟨KD, hKD, hdiff⟩ := Local.stab_broad_mu_flux c C hc hC
  obtain ⟨KG, hKG, hgeom⟩ := section_geometric_scalar_source_of_mass_budgets c C KM KD
    hc hC hKM.le hKD.le
  obtain ⟨KE, hKE, helec⟩ := section_electric_scalar_source_difference c C hc hC
  obtain ⟨KA, hKA, hgauge⟩ := potential_and_scalar_gauge_cost c C hc hC
  let K := KG + KE + KA + 1
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro s t e M ε L S₁ S₂ hS₁ hS₂ hM hε hε1 hsmall hL hbox hosc hvo hvi haxis hdata hσ
    u v huv
  let E := (normalized_field_distance s t S₁ S₂).toReal +
    ε * (geometry_distance s t S₁ S₂).toReal
  let σ := e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hσ0 : 0 ≤ σ := by dsimp [σ]; positivity
  have hv : v ∈ Icc s t := ⟨huv.1.trans huv.2.1, huv.2.2⟩
  have hs : inSeg s v v ⊆ triangle s t := by
    rintro p ⟨hx, hy, rfl⟩
    exact ⟨hx, hy, hv.2⟩
  have hboxM : ∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s t,
      c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C ∧ ‖S.phi p.1 p.2‖ ≤ M ∧
        ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ ε := by
    intro S hm p hp
    rcases hbox S hm p hp with ⟨hl, hl', hn, hn', hg, hφ, hθ, hξ⟩
    exact ⟨hl, hl', hφ, hθ⟩
  have hng : ∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s t,
      c ≤ -S.nu p.1 p.2 ∧ -S.nu p.1 p.2 ≤ C ∧ c ≤ 1 - S.mu p.1 p.2 ∧
        ‖S.xi p.1 p.2 / S.nu p.1 p.2‖ ≤ ε := by
    intro S hm p hp
    rcases hbox S hm p hp with ⟨hl, hl', hn, hn', hg, hφ, hθ, hξ⟩
    exact ⟨hn, hn', hg, hξ⟩
  have hm {S : Fields} (hS : IsSolution e S (triangle s t))
      (hmem : S ∈ ({S₁, S₂} : Set Fields)) := hmass s t e M ε L S hS hM hε hε1 hL
    (fun p hp => ⟨(hboxM S hmem p hp).1, (hboxM S hmem p hp).2.1,
      (hng S hmem p hp).2.1, (hng S hmem p hp).2.2.1,
      (hboxM S hmem p hp).2.2.1, (hboxM S hmem p hp).2.2.2, (hng S hmem p hp).2.2.2⟩)
    (hvo S hmem) (hvi S hmem) (haxis S hmem) hσ v hv
  have hd := hdiff s t e M ε L S₁ S₂ hS₁ hS₂ hM hε hε1 hsmall hL hboxM hng
    hosc hvo hvi haxis hσ v hv
  have hfin := geometry_distance_ne_top hS₁ hS₂ hc
    (fun p hp => (hboxM S₁ (by simp) p hp).1)
  have hw x (hx : x ∈ Icc s v) : c ≤ -S₁.nu x v ∧ -S₁.nu x v ≤ C ∧
      c ≤ -S₂.nu x v ∧ -S₂.nu x v ≤ C :=
    ⟨(hng S₁ (by simp) (x, v) (hs ⟨hx.1, hx.2, rfl⟩)).1,
      (hng S₁ (by simp) (x, v) (hs ⟨hx.1, hx.2, rfl⟩)).2.1,
      (hng S₂ (by simp) (x, v) (hs ⟨hx.1, hx.2, rfl⟩)).1,
      (hng S₂ (by simp) (x, v) (hs ⟨hx.1, hx.2, rfl⟩)).2.1⟩
  have hδw x (hx : x ∈ Icc s v) : |-S₁.nu x v - -S₂.nu x v| ≤
      (geometry_distance s t S₁ S₂).toReal := by
    simpa only [neg_sub_neg, abs_sub_comm] using
      abs_nu_sub_le_geometry_distance hS₁ hfin (hs ⟨hx.1, hx.2, rfl⟩)
  have hR0 : 0 ≤ S₁.r s v := by
    rcases eq_or_lt_of_le hv.1 with he | he
    · subst v; exact (hS₁.axis s ⟨le_rfl, le_rfl, hv.2⟩).1.symm.le
    · exact (hS₁.r_pos (s, v) ⟨le_rfl, hv.1, hv.2⟩ he).le
  have hsout : outSeg s s v ⊆ triangle s t := by
    rintro p ⟨rfl, hx⟩
    exact ⟨le_rfl, hx.1, hx.2.trans hv.2⟩
  have hR : S₁.r s v ≤ C * (t - s) :=
    (outgoing_radius_upper hS₁ hv.1 hsout
      (fun x hx => (hboxM S₁ (by simp) (s, x) (hsout ⟨rfl, hx⟩)).2.1)).trans
      (mul_le_mul_of_nonneg_left (sub_le_sub_right hv.2 s) hC)
  have hmom : (∫ x in s..v, (-S₁.nu x v) * S₁.r x v) = S₁.r s v ^ 2 / 2 := by
    convert incoming_radius_moment hS₁ hv.1 hs 1 using 1 <;> norm_num
  have hgap := fun S hm p hp => (hng S hm p hp).2.2.1
  obtain ⟨ig, hg⟩ := hgeom s t e M ε L S₁ S₂ hS₁ hS₂ hM hε hε1 hL hboxM hgap hosc hσ
    s v (S₁.r s v) (fun x => (x, v)) (fun x => -S₁.nu x v) (fun x => -S₂.nu x v)
    (fun x => S₁.theta x v / S₁.lam x v) (fun x => S₂.theta x v / S₂.lam x v)
    hv.1 (continuous_id.prodMk continuous_const).continuousOn
    (fun x hx => hs ⟨hx.1, hx.2, rfl⟩)
    (continuousOn_in_section hS₁.cont_nu hs).neg (continuousOn_in_section hS₂.cont_nu hs).neg
    (continuousOn_in_section (f := fun x y => S₁.theta x y / S₁.lam x y)
      (IsSolution.cont_outgoing_ratio hS₁) hs)
    (continuousOn_in_section (f := fun x y => S₂.theta x y / S₂.lam x y)
      (IsSolution.cont_outgoing_ratio hS₂) hs) hw hδw
    (fun x hx => ⟨(hboxM S₂ (by simp) (x, v) (hs ⟨hx.1, hx.2, rfl⟩)).2.2.2,
      (norm_ratio_sub_le_distance_add_scalar hS₁ hS₂ (hs ⟨hx.1, hx.2, rfl⟩)).1⟩)
    hR0 hR hmom (hm hS₁ (by simp)).1 (hm hS₂ (by simp)).1 hd.1
    (by convert (hm hS₁ (by simp)).2.2 using 1; ring)
    (by convert (hm hS₂ (by simp)).2.2 using 1; ring)
    (by convert hd.2 using 1; ring)
  obtain ⟨ie, he⟩ := helec s t e M ε S₁ S₂ hS₁ hS₂ hM hε hε1 hsmall hboxM hgap hosc hσ
    s v (fun x => (x, v)) (fun x => -S₁.nu x v) (fun x => -S₂.nu x v) (S₁.r s v)
    hv.1 (continuous_id.prodMk continuous_const).continuousOn
    (fun x hx => hs ⟨hx.1, hx.2, rfl⟩)
    (continuousOn_in_section hS₁.cont_nu hs).neg (continuousOn_in_section hS₂.cont_nu hs).neg
    hw hδw hR0 hR hmom
  let sg : ℝ → ℂ := fun x =>
    (((-S₁.nu x v) / S₁.r x v : ℝ) : ℂ) *
      (((S₁.mu x v - S₁.Q x v ^ 2 / S₁.r x v ^ 2) / (1 - S₁.mu x v) : ℝ) : ℂ) *
        (S₁.theta x v / S₁.lam x v) -
    (((-S₂.nu x v) / S₂.r x v : ℝ) : ℂ) *
      (((S₂.mu x v - S₂.Q x v ^ 2 / S₂.r x v ^ 2) / (1 - S₂.mu x v) : ℝ) : ℂ) *
        (S₂.theta x v / S₂.lam x v)
  let se : ℝ → ℂ := fun x => I * e *
    ((((-S₁.nu x v : ℝ) : ℂ) / S₁.r x v) * S₁.Q x v * S₁.phi x v / (1 - S₁.mu x v) -
      (((-S₂.nu x v : ℝ) : ℂ) / S₂.r x v) * S₂.Q x v * S₂.phi x v / (1 - S₂.mu x v))
  change IntervalIntegrable sg volume s v at ig
  change (∫ x in s..v, ‖sg x‖) ≤ KG * (ε * L + σ) * E at hg
  change IntervalIntegrable se volume s v at ie
  change (∫ x in s..v, ‖se x‖) ≤ KE * σ * E at he
  have ha := (hgauge s t e M ε S₁ S₂ hS₁ hS₂ hM hε hε1 hsmall hboxM
    (fun S hm p hp => ⟨(hng S hm p hp).2.1, (hng S hm p hp).2.2.1⟩)
    haxis hosc hσ).2 v hv
  let ag := fun x => -(I * e * ((S₁.A x v : ℂ) * S₁.a x v - (S₂.A x v : ℂ) * S₂.a x v))
  have cag : ContinuousOn ag (Icc s v) := by
    apply ContinuousOn.neg
    exact (continuousOn_const.mul continuousOn_const).mul
      (((continuous_ofReal.comp_continuousOn (continuousOn_in_section hS₁.cont_A hs)).mul
        (continuousOn_in_section (IsSolution.cont_a hS₁) hs)).sub
        ((continuous_ofReal.comp_continuousOn (continuousOn_in_section hS₂.cont_A hs)).mul
          (continuousOn_in_section (IsSolution.cont_a hS₂) hs)))
  have iag : IntervalIntegrable ag volume s v := ContinuousOn.intervalIntegrable_of_Icc hv.1 cag
  have hag : (∫ x in s..v, ‖ag x‖) ≤ KA * σ * E := by
    simpa only [ag, norm_neg, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, one_mul] using ha.2
  have hh := norm_increment_le_three_integrals (g := sg) (h := se) (k := ag) hv.1
    ((continuousOn_in_section (IsSolution.cont_a hS₁) hs).sub
      (continuousOn_in_section (IsSolution.cont_a hS₂) hs))
    (fun x hx => by
      apply ((hasDerivAt_a_in_real_coefficients hS₁ hs hx).sub
        (hasDerivAt_a_in_real_coefficients hS₂ hs hx)).congr_deriv
      dsimp [ag, sg, se]
      push_cast
      ring) ig ie iag ⟨huv.1, huv.2.1⟩
  have hinit : S₁.a s v - S₂.a s v = 0 := sub_eq_zero.mpr (hdata v hv).2
  change ‖(S₁.a u v - S₂.a u v) - (S₁.a s v - S₂.a s v)‖ ≤ _ at hh
  rw [hinit, sub_zero] at hh
  apply hh.trans
  calc
    _ ≤ KG * (ε * L + σ) * E + KE * σ * E + KA * σ * E := add_le_add (add_le_add hg he) hag
    _ ≤ (KG + KE + KA) * (ε * L + σ) * E := by
      have hle : σ ≤ ε * L + σ := le_add_of_nonneg_left (mul_nonneg hε hL)
      have h₁ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hKE.le) hE
      have h₂ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hKA.le) hE
      nlinarith only [h₁, h₂]
    _ ≤ K * (ε * L + σ) * E := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) (by positivity)) hE

end EmcsfAcExtension.Local.Broad
