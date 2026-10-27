module

public import EmcsfAcExtension.Global.Interaction.PairIntegrated
public import EmcsfAcExtension.Global.Interaction.IncomingOptics
import EmcsfAcExtension.Global.Interaction.OutgoingOptics
import EmcsfAcExtension.Global.Interaction.PairTonelli
import EmcsfAcExtension.Local.Api.Mono
import EmcsfAcExtension.Global.Calculus.Sections

/-! # Exact recorded interaction coefficients

These exports expose the coefficients used by the pair and finite-endpoint
proofs, rather than hiding them behind an existential estimate constant.
Source: `charged_SF_new_version.tex:L3658–L3663`, L3756–L3765.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global.InteractionEstimate

private theorem ordered_separation_of_envelope {a b : ℝ} (hab : a ≤ b)
    (g : ℝ → ℝ) (hg : IntervalIntegrable g volume a b)
    (hg0 : ∀ᵐ s ∂volume.restrict (Icc a b), 0 ≤ g s)
    (G : ℝ → ℝ≥0∞) (_hG : Measurable G)
    (hGeq : (fun s => ENNReal.ofReal (g s)) =ᵐ[volume.restrict (Icc a b)] G) :
    ENNReal.ofReal (∫ s in a..b, (∫ t in a..s, (s - t) * g t) * g s) =
      ∫⁻ s in Icc a b, (∫⁻ t in Icc a s, ENNReal.ofReal (s - t) * G t) * G s := by
  let P := fun s => ∫ t in a..s, (s - t) * g t
  have cP := continuousOn_separation_primitive hab g hg
  have iPg := hg.continuousOn_mul (by simpa only [uIcc_of_le hab] using cP)
  have hP (s : ℝ) (hs : s ∈ Icc a b) : 0 ≤ P s ∧
      ENNReal.ofReal (P s) = ∫⁻ t in Icc a s, ENNReal.ofReal (s - t) * G t := by
    have hsub : Icc a s ⊆ Icc a b := Icc_subset_Icc le_rfl hs.2
    have hsub' : uIcc a s ⊆ uIcc a b := by
      simpa only [uIcc_of_le hs.1, uIcc_of_le hab] using hsub
    have h0 := hg0.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
    have ih : IntervalIntegrable (fun t => (s - t) * g t) volume a s :=
      (hg.mono_set hsub').continuousOn_mul
        ((continuousOn_const : ContinuousOn (fun _ : ℝ => s) (uIcc a s)).sub continuousOn_id)
    have h0p : ∀ᵐ t ∂volume.restrict (Icc a s), 0 ≤ (s - t) * g t := by
      filter_upwards [h0, ae_restrict_mem measurableSet_Icc] with t hgt ht
      exact mul_nonneg (sub_nonneg.mpr ht.2) hgt
    refine ⟨intervalIntegral.integral_nonneg_of_ae_restrict hs.1 h0p, ?_⟩
    dsimp only [P]
    rw [intervalIntegral.integral_of_le hs.1, ← integral_Icc_eq_integral_Ioc,
      ofReal_integral_eq_lintegral_ofReal
        ((intervalIntegrable_iff_integrableOn_Icc_of_le hs.1).mp ih) h0p]
    apply lintegral_congr_ae
    filter_upwards [hGeq.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)),
      ae_restrict_mem measurableSet_Icc] with t hgt ht
    rw [ENNReal.ofReal_mul (sub_nonneg.mpr ht.2), hgt]
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp iPg)
      (by filter_upwards [hg0, ae_restrict_mem measurableSet_Icc] with s hgs hs;
          exact mul_nonneg (hP s hs).1 hgs)]
  apply lintegral_congr_ae
  filter_upwards [hGeq, ae_restrict_mem measurableSet_Icc] with s hgs hs
  rw [ENNReal.ofReal_mul (hP s hs).1, (hP s hs).2, hgs]

/-- [node prop:ct-interaction#pair-source-integrated]
The pair cost with coefficient `3 F Λ³ / (2 δ (1-F²) (2-ε) c⁴)`.
Only fixed geometric stops enter this coefficient; it is independent of
coupling, fields, envelope, radius scales, stages, and duration. -/
theorem pair_source_integrated_exact (δ c Λ F ε : ℝ)
    (hδ : 0 < δ) (hc : 0 < c) (hΛ : 0 < Λ)
    (hF : 0 ≤ F) (hF1 : F < 1) (hε : ε < 2) :
    ∀ (e ui u₀ u₁ v₀ ρ : ℝ) (S : Fields)
      (vb g : ℝ → ℝ) (N : ℕ) (_B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N),
      IsSolution e S (origDomain ui) →
      ExteriorStops S (exteriorDomain ui u₀ u₁ vb) δ c Λ F ε →
      IntervalIntegrable g volume v₀ 0 →
      (∀ᵐ s ∂volume.restrict (Icc v₀ 0), 0 ≤ g s) →
      (∀ u ∈ Icc u₀ u₁, ∀ᵐ v ∂volume.restrict (Icc (vb u) 0), ‖weightedJ S u v‖ ≤ g v) →
      (∫⁻ u in Icc u₀ u₁, ∫⁻ v in Icc (vb u) 0,
        ENNReal.ofReal ‖curvatureScalarSource S u v (S.theta u v / S.lam u v)
          (radialCurvatureWith S u (vb u) v (radialZSource S u (vb u)))‖) ≤
        ENNReal.ofReal ((3 * F * Λ ^ 3 / (2 * δ * (1 - F ^ 2) * (2 - ε) * c ^ 4)) *
          (∫ s in v₀..0, g s) ^ 2) := by
  let p := 1 - F ^ 2
  let β := 3 * F * Λ ^ 3 / (δ * p * c ^ 2)
  have hp : 0 < p := by dsimp [p]; nlinarith only [hF, hF1, sq_nonneg (F - 1)]
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  intro e ui u₀ u₁ v₀ ρ S vb g N B hS hstop hg hg0 hmajor
  let E := exteriorDomain ui u₀ u₁ vb
  have hSE : IsSolution e S E := Local.isSolution_mono hS inter_subset_left
  have h01 : u₀ ≤ u₁ := calc
    _ = B.cuts 0 := B.first.symm
    _ ≤ B.cuts (Fin.last N) := B.ordered (Fin.zero_le _)
    _ = _ := B.last
  have hv0 : v₀ ≤ 0 := by
    rw [← B.entry_label]
    exact (B.mem u₀ ⟨le_rfl, h01⟩).2.2.2
  let μ := volume.restrict (Icc v₀ 0)
  have ig : Integrable g μ := (intervalIntegrable_iff_integrableOn_Icc_of_le hv0).mp hg
  have hm : AEMeasurable (fun s => ENNReal.ofReal (g s)) μ :=
    ENNReal.continuous_ofReal.measurable.comp_aemeasurable ig.aestronglyMeasurable.aemeasurable
  let G := hm.mk (fun s => ENNReal.ofReal (g s))
  have hG : Measurable G := hm.measurable_mk
  have hGeq : (fun s => ENNReal.ofReal (g s)) =ᵐ[μ] G := hm.ae_eq_mk
  have hpoint (u : ℝ) (hu : u ∈ Icc u₀ u₁) (v : ℝ) (hv : v ∈ Icc (vb u) 0) :
      ENNReal.ofReal ‖curvatureScalarSource S u v (S.theta u v / S.lam u v)
        (radialCurvatureWith S u (vb u) v (radialZSource S u (vb u)))‖ ≤
        ENNReal.ofReal β * (ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 3) *
          (∫⁻ s in Icc (vb u) v, (∫⁻ t in Icc (vb u) s,
            ENNReal.ofReal (s - t) * G t) * G s)) := by
    have hs : outSeg u (vb u) v ⊆ E :=
      fun z hz => finite_boundary_row B u hu ⟨hz.1, hz.2.1, hz.2.2.trans hv.2⟩
    have hsub : Icc (vb u) v ⊆ Icc v₀ 0 :=
      Icc_subset_Icc (finite_boundary_label_bounds B u hu).1 hv.2
    have hsub' : uIcc (vb u) v ⊆ uIcc v₀ 0 := by
      simpa only [uIcc_of_le hv.1, uIcc_of_le hv0] using hsub
    have hg' := hg.mono_set hsub'
    have h0 := hg0.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
    have hmaj := (hmajor u hu).filter_mono
      (ae_mono (Measure.restrict_mono (Icc_subset_Icc le_rfl hv.2) le_rfl))
    have hpt := pair_source_pointwise hSE hstop (B.off_axis u hu) hv.1 hs hδ hc hF hF1 g hg' hmaj
    have heq := ordered_separation_of_envelope hv.1 g hg' h0 G hG
      (hGeq.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)))
    have hn := (neg_pos.mpr (hSE.nu_neg (u, v) (hs ⟨rfl, hv.1, le_rfl⟩))).le
    have hr := hSE.r_pos (u, v) (hs ⟨rfl, hv.1, le_rfl⟩) ((B.off_axis u hu).trans_le hv.1)
    apply (ENNReal.ofReal_le_ofReal hpt).trans_eq
    change ENNReal.ofReal (β * ((-S.nu u v) / S.r u v ^ 3) * _) = _
    rw [ENNReal.ofReal_mul (mul_nonneg hβ (by positivity)), ENNReal.ofReal_mul hβ, heq, mul_assoc]
  calc
    _ ≤ ∫⁻ u in Icc u₀ u₁, ∫⁻ v in Icc (vb u) 0, ENNReal.ofReal β *
        (ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 3) *
          (∫⁻ s in Icc (vb u) v, (∫⁻ t in Icc (vb u) s,
            ENNReal.ofReal (s - t) * G t) * G s)) := by
      apply setLIntegral_mono' measurableSet_Icc
      intro u hu
      exact setLIntegral_mono' measurableSet_Icc (hpoint u hu)
    _ = ENNReal.ofReal β * (∫⁻ u in Icc u₀ u₁, ∫⁻ v in Icc (vb u) 0,
        ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 3) *
          (∫⁻ s in Icc (vb u) v, (∫⁻ t in Icc (vb u) s,
            ENNReal.ofReal (s - t) * G t) * G s)) := by
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal β * (ENNReal.ofReal (1 / (c ^ 2 * (2 - ε))) *
        (∫⁻ s in Icc v₀ 0, ∫⁻ t in Icc v₀ s, G t * G s)) := by
      gcongr
      exact pair_source_kernel hS B hstop hc hε G hG
    _ = _ := by
      rw [lintegral_ordered_label_product_of_real_envelope hv0 g hg hg0 G hG hGeq,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hβ]
      congr 1
      dsimp [β, p]
      field_simp [hp.ne', hδ.ne', hc.ne', (sub_pos.mpr hε).ne']


/-- [node prop:ct-interaction#source-mass-finite-endpoint]
The derivative-source scalar mass with exact coefficient `Λ/c²`.
The coefficient depends only on the expansion bounds, independently of
coupling, fields, envelope, radii, and duration. The finite endpoint
`b - max s t` is retained, including coincident labels. -/
theorem source_mass_finite_endpoint_exact (c Λ F : ℝ) (hc : 0 < c) (hΛ : 0 < Λ)
    (hF : 0 ≤ F) (hF1 : F ≤ 1) :
    ∀ (e : ℝ) (S : Fields) (D : Set (ℝ × ℝ))
      (u a b : ℝ) (g : ℝ → ℝ), IsSolution e S D → u < a → a ≤ b → outSeg u a b ⊆ D →
      (∀ v ∈ Icc a b, c ≤ S.lam u v ∧ S.lam u v ≤ Λ) →
      (∀ v ∈ Icc a b, ‖S.theta u v / S.lam u v‖ ≤ F) →
      IntervalIntegrable g volume a b →
      (∀ᵐ v ∂volume.restrict (Icc a b), ‖weightedJ S u v‖ ≤ g v) →
      (∫⁻ x in Icc a b, ENNReal.ofReal (S.lam u x * ‖radialYSource S u a x‖ ^ 2)) ≤
        ENNReal.ofReal (Λ / c ^ 2) * (∫⁻ s in Icc a b, ∫⁻ t in Icc a b,
          ENNReal.ofReal (b - max s t) * ENNReal.ofReal (g s) * ENNReal.ofReal (g t)) := by
  have hcoef : Λ / c ^ 2 = Λ * c⁻¹ ^ 2 := by simp [div_eq_mul_inv, inv_pow]
  rw [hcoef]
  intro e S D u a b g hS hua hab hs hlam hy hg hmajor
  let μ := volume.restrict (Icc a b)
  have ig : Integrable g μ := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hg
  have hmeas : AEMeasurable (fun v => ENNReal.ofReal (g v)) μ :=
    ENNReal.continuous_ofReal.measurable.comp_aemeasurable ig.aestronglyMeasurable.aemeasurable
  let G := hmeas.mk (fun v => ENNReal.ofReal (g v))
  have hG : Measurable G := hmeas.measurable_mk
  have hGeq : (fun v => ENNReal.ofReal (g v)) =ᵐ[μ] G := hmeas.ae_eq_mk
  have hg0 : ∀ᵐ v ∂μ, 0 ≤ g v := hmajor.mono fun _ h => (norm_nonneg _).trans h
  have hprefix (x : ℝ) (hx : x ∈ Icc a b) :
      ENNReal.ofReal (∫ t in a..x, g t) = ∫⁻ t in Icc a x, G t := by
    have hsub : Icc a x ⊆ Icc a b := Icc_subset_Icc le_rfl hx.2
    have hsub' : uIcc a x ⊆ uIcc a b := by
      simpa only [uIcc_of_le hx.1, uIcc_of_le hab] using hsub
    have igx := (intervalIntegrable_iff_integrableOn_Icc_of_le hx.1).mp (hg.mono_set hsub')
    have h0x := hg0.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
    rw [intervalIntegral.integral_of_le hx.1, ← integral_Icc_eq_integral_Ioc,
      ofReal_integral_eq_lintegral_ofReal igx h0x]
    exact lintegral_congr_ae (hGeq.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)))
  have hdouble : (∫⁻ s in Icc a b, ∫⁻ t in Icc a b,
      ENNReal.ofReal (b - max s t) * G s * G t) =
      ∫⁻ s in Icc a b, ∫⁻ t in Icc a b,
        ENNReal.ofReal (b - max s t) * ENNReal.ofReal (g s) * ENNReal.ofReal (g t) := by
    apply lintegral_congr_ae
    filter_upwards [hGeq] with s hs
    apply lintegral_congr_ae
    filter_upwards [hGeq] with t ht
    rw [hs, ht]
  calc
    _ ≤ ∫⁻ x in Icc a b, ENNReal.ofReal (Λ * c⁻¹ ^ 2) *
        (∫⁻ t in Icc a x, G t) ^ 2 := by
      apply setLIntegral_mono' measurableSet_Icc
      intro x hx
      have hsub : Icc a x ⊆ Icc a b := Icc_subset_Icc le_rfl hx.2
      have hsub' : uIcc a x ⊆ uIcc a b := by
        simpa only [uIcc_of_le hx.1, uIcc_of_le hab] using hsub
      have hsrc := (outgoing_scalar_pointwise hS hua hx.1
        (fun p hp => hs ⟨hp.1, hp.2.1, hp.2.2.trans hx.2⟩) hc hF hF1
        (fun v hv => (hlam v (hsub hv)).1) (fun v hv => hy v (hsub hv)) g
        (hg.mono_set hsub')
        (hmajor.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)))).1
      have hnorm : ENNReal.ofReal ‖radialYSource S u a x‖ ≤
          ENNReal.ofReal c⁻¹ * (∫⁻ t in Icc a x, G t) := by
        apply (ENNReal.ofReal_le_ofReal hsrc).trans_eq
        rw [ENNReal.ofReal_mul (inv_nonneg.mpr hc.le), hprefix x hx]
      have hl := (hS.lam_pos (u, x) (hs ⟨rfl, hx⟩)).le
      rw [ENNReal.ofReal_mul hl, ENNReal.ofReal_pow (norm_nonneg _) 2,
        ENNReal.ofReal_mul hΛ.le, ENNReal.ofReal_pow (inv_nonneg.mpr hc.le) 2]
      calc
        _ ≤ ENNReal.ofReal Λ * (ENNReal.ofReal c⁻¹ * (∫⁻ t in Icc a x, G t)) ^ 2 := by
          gcongr
          exact (hlam x hx).2
        _ = _ := by ring
    _ = ENNReal.ofReal (Λ * c⁻¹ ^ 2) *
        (∫⁻ x in Icc a b, (∫⁻ t in Icc a x, G t) ^ 2) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by rw [lintegral_prefix_square_eq hab G hG, hdouble]


end EmcsfAcExtension.Global.InteractionEstimate
