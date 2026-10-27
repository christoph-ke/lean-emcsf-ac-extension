module

public import EmcsfAcExtension.Global.Interaction.WrappersProfiles
public import EmcsfAcExtension.Global.Interaction.ElectricArea
public import EmcsfAcExtension.Global.Interaction.ElectricMixed
import EmcsfAcExtension.Global.Calculus.Sections
import EmcsfAcExtension.Local.Api.Mono

/-! # Separate explicit and mixed electromagnetic costs

All canonical profiles are derived from the stopped-envelope and
core/boundary hypotheses. The explicit costs are exported separately,
with the recorded factors `F` and `F³`. Source:
`charged_SF_new_version.tex:L3722–L3743`.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global.InteractionEstimate

open Interaction

/-- [internal] Separate profile-conditional explicit electromagnetic costs.
The positive coefficient depends only on `δ,Λ,F,Cq`, before the coupling,
scalar scale, radius, measurable history, and duration. The source-setting
consumer below discharges both profile premises. -/
theorem explicit_electromagnetic_source_cost_of_profiles_separate (δ Λ F Cq : ℝ)
    (hδ : 0 < δ) (hΛ : 0 < Λ) (hF : 0 ≤ F) (hCq : 0 ≤ Cq) :
    ∃ C : ℝ, 0 < C ∧ ∀ (e M R₀ a b c ε : ℝ) (S : Fields)
      (D : Set (ℝ × ℝ)) (U : Set ℝ) (vb : ℝ → ℝ),
      IsSolution e S D → ExteriorStops S D δ c Λ F ε →
      a ≤ b → b ≤ 0 → inSeg a b 0 ⊆ D → MeasurableSet U → U ⊆ Icc a b →
      0 ≤ R₀ → 1 ≤ M → (∀ u ∈ U, u < vb u ∧ vb u ≤ 0) →
      (∀ u ∈ U, outSeg u (vb u) 0 ⊆ D) → (∀ u ∈ U, S.r u 0 ≤ R₀) →
      (∀ u ∈ U, ∀ v ∈ Icc (vb u) 0, ‖S.phi u v‖ ≤ M) →
      (∀ u ∈ U, ∀ v ∈ Icc (vb u) 0,
        |S.Q u v| / S.r u v ^ 2 ≤ Cq * |e| * M * F) →
      (∫⁻ u in U, ∫⁻ v in Icc (vb u) 0,
        ENNReal.ofReal ‖((S.lam u v / (1 - S.mu u v) : ℝ) : ℂ) *
          Local.emSourceJ e S u v‖) ≤
        ENNReal.ofReal (C * Local.sigma e M (2 * R₀) * F) ∧
      (∫⁻ u in U, ∫⁻ v in Icc (vb u) 0,
        ENNReal.ofReal ‖curvatureScalarSource S u v (S.theta u v / S.lam u v)
          (radialCurvatureEM e S u (vb u) v)‖) ≤
        ENNReal.ofReal (C * Local.sigma e M (2 * R₀) * F ^ 3) := by
  obtain ⟨A, hA, hcurv⟩ := ct_c_charge_of_profiles Cq hCq
  let Kr := ((5 * Cq ^ 2 * F ^ 2 + Cq * (3 * F + 1) + 1) / δ) * (Λ / 2)
  let Kc := 3 * A * Λ / (2 * δ)
  have hKr : 0 ≤ Kr := by dsimp [Kr]; positivity
  have hKc : 0 ≤ Kc := by dsimp [Kc]; positivity
  refine ⟨Kr + Kc + 1, by positivity, ?_⟩
  intro e M R₀ a b c ε S D U vb hS hstop hab hb hterm hU hsub hR hM hvb hrow hupper hphi hQ
  have hst (u : ℝ) (hu : u ∈ U) (v : ℝ) (hv : v ∈ Icc (vb u) 0) :=
    hstop (u, v) (hrow u hu ⟨rfl, hv⟩)
  have hcharge (u : ℝ) (hu : u ∈ U) (v : ℝ) (hv : v ∈ Icc (vb u) 0) :
      S.Q u v ^ 2 / S.r u v ^ 2 ≤ S.mu u v := by
    linarith only [(hst u hu v hv).1, (hst u hu v hv).2.2.2.2.2.2]
  have hrem := explicit_electromagnetic_remainder_cost δ F Cq Λ hδ hF hCq hΛ.le
    hS hab hb hterm hU hsub hR hM hvb hrow hcharge hupper
    (fun u hu v hv => (hst u hu v hv).2.2.2.1)
    (fun u hu v hv => (hst u hu v hv).2.1) hphi
    (fun u hu v hv => (hst u hu v hv).2.2.2.2.1) hQ
  have helectric : (∫⁻ u in U, ∫⁻ v in Icc (vb u) 0,
      ENNReal.ofReal ‖curvatureScalarSource S u v (S.theta u v / S.lam u v)
        (radialCurvatureEM e S u (vb u) v)‖) ≤
      ENNReal.ofReal (Kc * (|e| * M * R₀) ^ 2 * F ^ 3) := by
    have hcoef : 0 ≤ (3 * A / δ) * e ^ 2 * M ^ 2 * F ^ 3 := by positivity
    calc
      _ ≤ ∫⁻ u in U, ∫⁻ v in Icc (vb u) 0,
          ENNReal.ofReal (((3 * A / δ) * e ^ 2 * M ^ 2 * F ^ 3) *
            ((-S.nu u v) * S.lam u v ^ 2)) := by
        apply setLIntegral_mono' hU
        intro u hu
        apply setLIntegral_mono' measurableSet_Icc
        intro v hv
        have hs : outSeg u (vb u) v ⊆ D :=
          fun p hp => hrow u hu ⟨hp.1, hp.2.1, hp.2.2.trans hv.2⟩
        have hr := hS.r_pos (u, v) (hs ⟨rfl, hv.1, le_rfl⟩) ((hvb u hu).1.trans_le hv.1)
        have hn := (hS.nu_neg (u, v) (hs ⟨rfl, hv.1, le_rfl⟩)).le
        have hn0 := neg_nonneg.mpr hn
        have hl := (hS.lam_pos (u, v) (hs ⟨rfl, hv.1, le_rfl⟩)).le
        have hc := hcurv e M F S D u (vb u) v hS (hvb u hu).1 hv.1 hs
          (by linarith only [hM]) hF
          (fun x hx => hphi u hu x ⟨hx.1, hx.2.trans hv.2⟩)
          (fun x hx => (hst u hu x ⟨hx.1, hx.2.trans hv.2⟩).2.2.2.2.1)
          (fun x hx => hQ u hu x ⟨hx.1, hx.2.trans hv.2⟩)
        apply ENNReal.ofReal_le_ofReal
        apply (curvature_scalar_source_le S u v δ (S.lam u v) F _ _ hδ hr hn hl
          le_rfl (hst u hu v hv).2.1 (hst u hu v hv).2.2.2.2.1).trans
        apply (mul_le_mul_of_nonneg_left hc (by positivity)).trans_eq
        field_simp [hr.ne', hδ.ne']
      _ = ENNReal.ofReal ((3 * A / δ) * e ^ 2 * M ^ 2 * F ^ 3) *
          (∫⁻ u in U, ∫⁻ v in Icc (vb u) 0,
            ENNReal.ofReal ((-S.nu u v) * S.lam u v ^ 2)) := by
        simp_rw [ENNReal.ofReal_mul hcoef, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal ((3 * A / δ) * e ^ 2 * M ^ 2 * F ^ 3) *
          ENNReal.ofReal (Λ * R₀ ^ 2 / 2) := by
        gcongr
        exact (ct_area hS hab hb hterm hU hsub hR hΛ.le hvb hrow hcharge hupper
          (fun u hu v hv => (hst u hu v hv).2.2.2.1)).2
      _ = _ := by
        rw [← ENNReal.ofReal_mul hcoef]
        dsimp [Kc]
        congr 1
        rw [mul_pow, mul_pow, sq_abs]
        ring
  have hζ : (|e| * M * R₀) ^ 2 = Local.sigma e M (2 * R₀) := by
    rw [ct_zeta, mul_pow, mul_pow, sq_abs]
  rw [hζ] at hrem helectric
  have hζ0 : 0 ≤ Local.sigma e M (2 * R₀) := by rw [ct_zeta]; positivity
  constructor
  · apply hrem.trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith only [hKc] : Kr ≤ Kr + Kc + 1) hζ0) hF
  · apply helectric.trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith only [hKr] : Kc ≤ Kr + Kc + 1) hζ0)
      (pow_nonneg hF 3)


/-- [node prop:ct-interaction#explicit-electromagnetic-source-cost]
The two explicit electric costs, separately bounded by `C ζ² F` and
`C ζ² F³`. The positive coefficient depends only on fixed geometry and
stops, before coupling, canonical `M₀`, radius, stage count and duration.
No scalar or charge profile is assumed. -/
theorem explicit_electromagnetic_source_cost_of_stopped (δ c Λ F ε ρ : ℝ)
    (hbox : ExteriorBox δ c Λ F ε ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ui e : ℝ) (S : Fields),
      OriginalData ui e S → SignedTerminalBound ui S → ∀ Jstop : ℝ,
      ∃ a ∈ Ioo ui 0, ∀ (u₀ u₁ v₀ R₀ : ℝ) (vb g en : ℝ → ℝ),
        a ≤ u₀ →
        StoppedProfileData ui u₀ u₁ v₀ R₀ δ c Λ F ε Jstop S vb g →
        (∀ u ∈ Icc u₀ u₁, S.m u (vb u) / S.r u (vb u) ≤ en u ∧ en u ≤ F ^ 2) →
        (∫⁻ u in Icc u₀ u₁, ∫⁻ v in Icc (vb u) 0,
          ENNReal.ofReal ‖((S.lam u v / (1 - S.mu u v) : ℝ) : ℂ) *
            Local.emSourceJ e S u v‖) ≤
          ENNReal.ofReal (C * Local.sigma e (scalarBackground ui R₀ c F Jstop S) (2 * R₀) * F) ∧
        (∫⁻ u in Icc u₀ u₁, ∫⁻ v in Icc (vb u) 0,
          ENNReal.ofReal ‖curvatureScalarSource S u v (S.theta u v / S.lam u v)
            (radialCurvatureEM e S u (vb u) v)‖) ≤
          ENNReal.ofReal
            (C * Local.sigma e (scalarBackground ui R₀ c F Jstop S) (2 * R₀) * F ^ 3) := by
  obtain ⟨Cq, hCq, hprofiles⟩ := stopped_profiles
  obtain ⟨C, hC, hbound⟩ := explicit_electromagnetic_source_cost_of_profiles_separate
    δ Λ F Cq hbox.1 (hbox.2.2.1.trans_le hbox.2.2.2.1) hbox.2.2.2.2.1 hCq.le
  refine ⟨C, hC, ?_⟩
  intro ui e S h hs Jstop
  obtain ⟨a, ha, hprof⟩ := hprofiles ui e S h hs Jstop
  refine ⟨a, ha, ?_⟩
  intro u₀ u₁ v₀ R₀ vb g en hau d hbudget
  have hp := hprof u₀ u₁ v₀ R₀ δ c Λ F ε vb g en hau d hbudget
  by_cases h01 : u₀ ≤ u₁
  · have hM := d.one_le_background h ⟨le_rfl, h01⟩
    have hSE := Local.isSolution_mono h.solution (D' := exteriorDomain ui u₀ u₁ vb)
      (fun p hp => hp.1)
    have hb : u₁ ≤ 0 := ((d.rows u₁ ⟨h01, le_rfl⟩).2.1.trans_le
      (d.rows u₁ ⟨h01, le_rfl⟩).2.2.1).le
    have hterm : inSeg u₀ u₁ 0 ⊆ exteriorDomain ui u₀ u₁ vb := by
      rintro ⟨u, v⟩ ⟨hu0, hu1, rfl⟩
      exact d.row_mem ⟨hu0, hu1⟩ ⟨(d.rows u ⟨hu0, hu1⟩).2.2.1, le_rfl⟩
    exact hbound e _ R₀ u₀ u₁ c ε S _ (Icc u₀ u₁) vb hSE d.stops h01 hb hterm
      measurableSet_Icc Subset.rfl d.radius_pos.le hM
      (fun u hu => ⟨(d.rows u hu).2.1, (d.rows u hu).2.2.1⟩)
      (fun u hu => d.exterior_segment hu ⟨(d.rows u hu).2.2.1, le_rfl⟩)
      (fun u hu => (d.annulus u hu).2)
      (fun u hu v hv => (hp u hu v hv).2.1)
      (fun u hu v hv => (hp u hu v hv).2.2)
  · have he : Icc u₀ u₁ = ∅ := Icc_eq_empty_of_lt (lt_of_not_ge h01)
    simp only [he, Measure.restrict_empty, lintegral_zero_measure]
    exact ⟨bot_le, bot_le⟩

/-- [internal]
The mixed electric cost `C ζ² F² J`, independent of time duration.
The positive coefficient depends only on fixed geometry and stops,
before coupling, canonical `M₀`, radii, envelope and stage count. The
landed outer kernel and incoming radius moment supply the integration. -/
theorem electromagnetic_mixed_cost_of_stopped (δ c Λ F ε ρ : ℝ)
    (hbox : ExteriorBox δ c Λ F ε ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ui e : ℝ) (S : Fields),
      OriginalData ui e S → SignedTerminalBound ui S → ∀ Jstop : ℝ,
      ∃ a ∈ Ioo ui 0, ∀ (u₀ u₁ v₀ R₀ : ℝ) (vb g en : ℝ → ℝ)
        (N : ℕ) (_B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N),
        a ≤ u₀ →
        StoppedProfileData ui u₀ u₁ v₀ R₀ δ c Λ F ε Jstop S vb g →
        (∀ u ∈ Icc u₀ u₁, S.m u (vb u) / S.r u (vb u) ≤ en u ∧ en u ≤ F ^ 2) →
        (∫⁻ u in Icc u₀ u₁, ∫⁻ v in Icc (vb u) 0,
          ENNReal.ofReal ‖curvatureScalarSource S u v (S.theta u v / S.lam u v)
            (radialCurvatureWith S u (vb u) v (radialZEM e S u (vb u)))‖) ≤
          ENNReal.ofReal (C * Local.sigma e (scalarBackground ui R₀ c F Jstop S) (2 * R₀) *
            F ^ 2 * (∫ s in v₀..0, g s)) := by
  obtain ⟨Cq, hCq, hprofiles⟩ := stopped_profiles
  have hε : ε < 2 := by
    have hp := (le_max_left ε (1 / 2)).trans_lt hbox.2.2.2.2.2.2.2.1
    linarith only [hp, sq_nonneg F]
  obtain ⟨C, hC, hbound⟩ := electromagnetic_mixed_cost δ c Λ ε Cq hbox.1
    hbox.2.2.1 (hbox.2.2.1.trans_le hbox.2.2.2.1) hε hCq.le
  refine ⟨C, hC, ?_⟩
  intro ui e S h hs Jstop
  obtain ⟨a, ha, hprof⟩ := hprofiles ui e S h hs Jstop
  refine ⟨a, ha, ?_⟩
  intro u₀ u₁ v₀ R₀ vb g en N B hau d hbudget
  have hp := hprof u₀ u₁ v₀ R₀ δ c Λ F ε vb g en hau d hbudget
  have h01 : u₀ ≤ u₁ := by
    calc
      _ = B.cuts 0 := B.first.symm
      _ ≤ B.cuts (Fin.last N) := B.ordered (Fin.zero_le _)
      _ = _ := B.last
  have hM := d.one_le_background h ⟨le_rfl, h01⟩
  have hv0 : v₀ ≤ 0 := (d.rows u₀ ⟨le_rfl, h01⟩).2.2.2.trans
    (d.rows u₀ ⟨le_rfl, h01⟩).2.2.1
  exact hbound e ui _ R₀ u₀ u₁ v₀ ρ F S vb g N B h.solution d.stops
    ((by norm_num : (0 : ℝ) ≤ 1).trans hM) d.scalar_nonneg d.radius_pos.le
    (fun u hu => (d.annulus u hu).2)
    (fun p hp' => ⟨ct_m0 h d p hp', (hp p.1 ⟨hp'.2.1, hp'.2.2.1⟩ p.2
      ⟨hp'.2.2.2, hp'.1.2.2.2⟩).2.2⟩)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hv0).mpr d.integrable)
    d.nonneg (fun u hu => d.row_majorant hu ⟨(d.rows u hu).2.2.1, le_rfl⟩)

end EmcsfAcExtension.Global.InteractionEstimate
