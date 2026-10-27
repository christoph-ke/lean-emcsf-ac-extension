module

public import EmcsfAcExtension.Global.Interaction.BoundaryMoments
public import EmcsfAcExtension.Global.Interaction.BoundarySourceKernel
import EmcsfAcExtension.Global.Calculus.Sections
import EmcsfAcExtension.Local.Api.Mono
import Mathlib.Tactic

/-! # Derivative scalar source times boundary curvature

The scalar damping power is kept through outgoing integration; the
remaining incoming moment is paid by the actual stage budget.
Source: charged_SF_new_version.tex:L3673–L3687; internal project record `(sb)`.
-/

public section
open Set MeasureTheory
open scoped ENNReal
namespace EmcsfAcExtension.Global.InteractionEstimate

/-- [internal]
The actual outgoing scalar source is controlled by its power-weighted
label envelope, with exact coefficient `c⁻¹`, uniformly in physical data,
row endpoints, radius, and duration. -/
theorem radial_y_source_envelope {e δ c Λ F ε : ℝ} {S : Fields}
    {D : Set (ℝ × ℝ)} (hS : IsSolution e S D)
    (hstop : ExteriorStops S D δ c Λ F ε) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D)
    (hc : 0 < c) (hF : 0 ≤ F) (g : ℝ → ℝ) (hg : IntervalIntegrable g volume a b)
    (hmajor : ∀ᵐ v ∂volume.restrict (Icc a b), ‖weightedJ S u v‖ ≤ g v) :
    ‖radialYSource S u a b‖ ≤ c⁻¹ *
      (∫ s in a..b, (S.r u s / S.r u b) ^ (1 - F ^ 2) * g s) := by
  have hr (s : ℝ) (h : s ∈ Icc a b) : 0 < S.r u s :=
    hS.r_pos (u, s) (hs ⟨rfl, h⟩) (hua.trans_le h.1)
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cp : ContinuousOn (fun s => (S.r u s / S.r u b) ^ (1 - F ^ 2)) (Icc a b) :=
    (cr.div_const _).rpow_const (fun s h => Or.inl (div_pos (hr s h) (hr b ⟨hab, le_rfl⟩)).ne')
  have iq := Interaction.radial_y_source_integrable hS hua hab hs
  have iqn : IntervalIntegrable (fun s => ‖weightedJ S u s‖ / S.lam u s) volume a b := by
    apply iq.norm.congr
    intro s h
    have h' : s ∈ Icc a b := by simpa only [uIcc_of_le hab] using uIoc_subset_uIcc h
    change ‖weightedJ S u s / (S.lam u s : ℂ)‖ = ‖weightedJ S u s‖ / S.lam u s
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hS.lam_pos (u, s) (hs ⟨rfl, h'⟩))]
  have i₁ := iqn.continuousOn_mul (by simpa only [uIcc_of_le hab] using cp)
  have i₂ := hg.continuousOn_mul (by simpa only [uIcc_of_le hab] using cp)
  apply (ct_y_split hS hua hab hs hF
    (fun v hv => (hstop (u, v) (hs ⟨rfl, hv⟩)).2.2.2.2.1)).2.trans
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_ae_restrict hab i₁ (i₂.const_mul _)
  filter_upwards [hmajor, ae_restrict_mem measurableSet_Icc] with s hgs hs'
  have hgs0 := (norm_nonneg _).trans hgs
  have hlam := (hstop (u, s) (hs ⟨rfl, hs'⟩)).2.2.1
  have hl := hc.trans_le hlam
  have hden : ‖weightedJ S u s‖ / S.lam u s ≤ c⁻¹ * g s := by
    calc
      _ ≤ g s / S.lam u s := div_le_div_of_nonneg_right hgs hl.le
      _ ≤ g s / c := div_le_div_of_nonneg_left hgs0 hc hlam
      _ = _ := by ring
  change _ ≤ c⁻¹ * ((S.r u s / S.r u b) ^ (1 - F ^ 2) * g s)
  exact (mul_le_mul_of_nonneg_left hden (Real.rpow_nonneg (div_nonneg (hr s hs').le (hr b ⟨hab,
    le_rfl⟩).le) _)).trans_eq (by ring)

/-- [internal]
Pointwise selected outgoing derivative source times actual boundary
curvature, retaining its damping power. The exact coefficient
`3Λ²/(δc)` depends only on fixed stops, uniformly in all data and labels. -/
theorem source_boundary_pointwise {e δ c Λ F ε : ℝ} {S : Fields}
    {D : Set (ℝ × ℝ)} (hS : IsSolution e S D)
    (hstop : ExteriorStops S D δ c Λ F ε) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D)
    (hδ : 0 < δ) (hc : 0 < c) (hF : 0 ≤ F)
    (g : ℝ → ℝ) (hg : IntervalIntegrable g volume a b)
    (hmajor : ∀ᵐ v ∂volume.restrict (Icc a b), ‖weightedJ S u v‖ ≤ g v) :
    ‖curvatureScalarSource S u b (radialYSource S u a b) (radialCurvatureBoundary S u a b)‖ ≤
      (3 * Λ ^ 2 / (δ * c)) * ((-S.nu u b) / S.r u b ^ 3) *
        (∫ s in a..b, ((S.r u s / S.r u b) ^ (1 - F ^ 2) *
          (S.r u a * (S.mu u a + ‖S.theta u a / S.lam u a‖ * ‖S.xi u a / S.nu u a‖))) * g s) := by
  let M := S.mu u a + ‖S.theta u a / S.lam u a‖ * ‖S.xi u a / S.nu u a‖
  let H := ∫ s in a..b, (S.r u s / S.r u b) ^ (1 - F ^ 2) * g s
  have hra := hS.r_pos (u, a) (hs ⟨rfl, le_rfl, hab⟩) hua
  have hrb := hS.r_pos (u, b) (hs ⟨rfl, hab, le_rfl⟩) (hua.trans_le hab)
  have hn := (hS.nu_neg (u, b) (hs ⟨rfl, hab, le_rfl⟩)).le
  have hnn := neg_nonneg.mpr hn
  have hl := (hS.lam_pos (u, b) (hs ⟨rfl, hab, le_rfl⟩)).le
  have hst := hstop (u, b) (hs ⟨rfl, hab, le_rfl⟩)
  have hM : 0 ≤ M := add_nonneg (hstop (u, a) (hs ⟨rfl, le_rfl, hab⟩)).1 (by positivity)
  have hy := radial_y_source_envelope hS hstop hua hab hs hc hF g hg hmajor
  have hH : 0 ≤ H := by
    have hh : 0 ≤ c⁻¹ * H := (norm_nonneg _).trans hy
    exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hc)).mp hh
  have hC : ‖radialCurvatureBoundary S u a b‖ ≤ S.r u a / S.r u b * M := by
    rw [radialCurvatureBoundary, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos hra hrb)]
    exact mul_le_mul_of_nonneg_left
      (curvature_norm_le S u a (hstop (u, a) (hs ⟨rfl, le_rfl, hab⟩)).1
        (hS.one_sub_mu_pos (u, a) (hs ⟨rfl, le_rfl, hab⟩)).le) (by positivity)
  have heq : (∫ s in a..b, ((S.r u s / S.r u b) ^ (1 - F ^ 2) * (S.r u a * M)) * g s) =
      (S.r u a * M) * H := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only [H]
    ring
  change _ ≤ _ * _ * (∫ s in a..b, ((S.r u s / S.r u b) ^ (1 - F ^ 2) * (S.r u a * M)) * g s)
  rw [heq]
  calc
    _ ≤ (3 * Λ ^ 2 * (c⁻¹ * H) / δ) * ((-S.nu u b) / S.r u b ^ 2) *
        ‖radialCurvatureBoundary S u a b‖ :=
      curvature_scalar_source_le S u b δ Λ (c⁻¹ * H) _ _ hδ hrb hn hl hst.2.2.2.1 hst.2.1 hy
    _ ≤ (3 * Λ ^ 2 * (c⁻¹ * H) / δ) * ((-S.nu u b) / S.r u b ^ 2) * (S.r u a / S.r u b * M) :=
      mul_le_mul_of_nonneg_left hC (by positivity)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

/-- [node prop:ct-interaction#source-boundary-curvature]
The actual outgoing derivative source times boundary curvature costs
`C E_n J` on each complete stage, including its assigned connector.
The positive constant depends only on `δ,c,Λ,F,ε,ρ`, chosen before every
physical datum, boundary scale, envelope, stage count, and duration.
The damping power and exact outgoing denominator are retained before
applying the actual mass and quadratic boundary budgets.
Source: charged_SF_new_version.tex:L3673–L3687; internal project record `(sb)`. -/
theorem source_boundary_curvature (δ c Λ F ε ρ : ℝ)
    (hbox : ExteriorBox δ c Λ F ε ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (e ui u₀ u₁ v₀ : ℝ) (S : Fields)
      (vb g : ℝ → ℝ) (N : ℕ) (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) (E : Fin N → ℝ),
      IsSolution e S (origDomain ui) → BoundaryBudgets S ui u₀ u₁ v₀ ρ vb N B E →
      ExteriorStops S (exteriorDomain ui u₀ u₁ vb) δ c Λ F ε →
      IntervalIntegrable g volume v₀ 0 →
      (∀ᵐ s ∂volume.restrict (Icc v₀ 0), 0 ≤ g s) →
      (∀ u ∈ Icc u₀ u₁, ∀ᵐ v ∂volume.restrict (Icc (vb u) 0), ‖weightedJ S u v‖ ≤ g v) →
      ∀ n : Fin N,
      (∫⁻ u in Icc (B.cuts n.castSucc) (B.cuts n.succ), ∫⁻ v in Icc (vb u) 0,
        ENNReal.ofReal ‖curvatureScalarSource S u v (radialYSource S u (vb u) v)
          (radialCurvatureBoundary S u (vb u) v)‖) ≤
        ENNReal.ofReal (C * E n * (∫ s in v₀..0, g s)) := by
  rcases hbox with ⟨hδ, _, hc, hcΛ, hF, _, _, hp, hρ, _⟩
  let p := 1 - F ^ 2
  let β := 3 * Λ ^ 2 / (δ * c)
  let Kb := 2 / ρ + Real.sqrt (ρ ^ (ε - 3) / (3 - ε))
  have hΛ : 0 < Λ := hc.trans_le hcΛ
  have hep : ε < p := (le_max_left ε (1 / 2)).trans_lt hp
  have hε3 : ε < 3 := by dsimp [p] at hep; nlinarith only [hep, sq_nonneg F]
  have hq : 0 < 2 + p - ε := by linarith only [hep]
  have hβ : 0 < β := by dsimp [β]; positivity
  have hKb : 0 < Kb := add_pos_of_pos_of_nonneg (div_pos (by norm_num) hρ) (Real.sqrt_nonneg _)
  refine ⟨β * Kb / (c * (2 + p - ε)), by positivity, ?_⟩
  intro e ui u₀ u₁ v₀ S vb g N B E hS hE hstop hg hg0 hmajor n
  have hEn : 0 ≤ E n := (hE n).1
  let D := exteriorDomain ui u₀ u₁ vb
  let U := Icc (B.cuts n.castSucc) (B.cuts n.succ)
  let P := fun z : ℝ × ℝ => S.r z.1 (vb z.1) *
    (S.mu z.1 (vb z.1) + ‖S.theta z.1 (vb z.1) / S.lam z.1 (vb z.1)‖ *
      ‖S.xi z.1 (vb z.1) / S.nu z.1 (vb z.1)‖)
  have hSE : IsSolution e S D := Local.isSolution_mono hS inter_subset_left
  have h01 : u₀ ≤ u₁ := calc
    _ = B.cuts 0 := B.first.symm
    _ ≤ B.cuts (Fin.last N) := B.ordered (Fin.zero_le _)
    _ = _ := B.last
  have hv0 : v₀ ≤ 0 := by rw [← B.entry_label]; exact (B.mem u₀ ⟨le_rfl, h01⟩).2.2.2
  obtain ⟨G, hG, hGeq, hmass⟩ := exists_measurable_envelope hv0 g hg hg0
  have hpB : ContinuousOn (fun u => (u, vb u)) (Icc u₀ u₁) := continuousOn_id.prodMk B.cont
  obtain ⟨cy, cz, cm, _⟩ := continuousOn_boundary_traces hS B
  have cp : ContinuousOn (fun u => P (u, (0 : ℝ))) (Icc u₀ u₁) :=
    (hS.cont_r.comp hpB B.mem).mul (cm.add (cy.mul cz))
  have hP : ContinuousOn P D := cp.comp continuousOn_fst (fun z hz => ⟨hz.2.1, hz.2.2.1⟩)
  have hP0 (z : ℝ × ℝ) (hz : z ∈ D) : 0 ≤ P z := by
    have hui : z.1 ∈ Icc u₀ u₁ := ⟨hz.2.1, hz.2.2.1⟩
    have hr := hS.r_pos (z.1, vb z.1) (B.mem z.1 hui) (B.off_axis z.1 hui)
    have hm := (hstop (z.1, vb z.1) (finite_boundary_row B z.1 hui
      ⟨rfl, le_rfl, (B.mem z.1 hui).2.2.2⟩)).1
    dsimp only [P]
    positivity
  have hlabel (s : ℝ) (hs : s ∈ Icc v₀ 0) :
      (∫⁻ u in U ∩ {u | vb u ≤ s}, ENNReal.ofReal (P (u, s) * (-S.nu u s) / S.r u s ^ 2)) ≤
        ENNReal.ofReal (Kb * E n) := by
    obtain ⟨z, hz, hzs, hist, hin⟩ := label_history_interval B hs
    have hset : U ∩ {u | vb u ≤ s} = U ∩ Icc u₀ z := by
      ext u
      constructor
      · rintro ⟨hu, hvs⟩
        exact ⟨hu, hist ▸ ⟨finite_boundary_stage_subset B n hu, hvs⟩⟩
      · rintro ⟨hu, huz⟩
        exact ⟨hu, (show u ∈ {u | u ∈ Icc u₀ u₁ ∧ vb u ≤ s} from hist.symm ▸ huz).2⟩
    rw [hset]
    exact source_boundary_label_budget hS B hE hstop hρ hε3 n hz.1 hzs.le hin
      (measurableSet_Icc.inter measurableSet_Icc) inter_subset_right inter_subset_left
      (fun u hu => (show u ∈ {u | u ∈ Icc u₀ u₁ ∧ vb u ≤ s} from hist.symm ▸ hu.2).2)
      (fun u hu q hq => finite_boundary_row B u (finite_boundary_stage_subset B n hu.1)
        ⟨hq.1, hq.2.1, hq.2.2.trans hs.2⟩)
  have hpoint (u : ℝ) (hu : u ∈ U) (v : ℝ) (hv : v ∈ Icc (vb u) 0) :
      ENNReal.ofReal ‖curvatureScalarSource S u v (radialYSource S u (vb u) v)
        (radialCurvatureBoundary S u (vb u) v)‖ ≤ ENNReal.ofReal β *
        (ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 3) *
          (∫⁻ s in Icc (vb u) v, ENNReal.ofReal ((S.r u s / S.r u v) ^ p * P (u, s)) * G s)) := by
    have hui := finite_boundary_stage_subset B n hu
    have hrow : outSeg u (vb u) v ⊆ D := fun q hq => finite_boundary_row B u hui
      ⟨hq.1, hq.2.1, hq.2.2.trans hv.2⟩
    have hsub : Icc (vb u) v ⊆ Icc v₀ 0 := Icc_subset_Icc (finite_boundary_label_bounds B u
      hui).1 hv.2
    have hsub' : uIcc (vb u) v ⊆ uIcc v₀ 0 := by simpa only [uIcc_of_le hv.1, uIcc_of_le hv0]
      using hsub
    have hg' := hg.mono_set hsub'
    have hmaj := (hmajor u hui).filter_mono
      (ae_mono (Measure.restrict_mono (Icc_subset_Icc le_rfl hv.2) le_rfl))
    have hpt := source_boundary_pointwise hSE hstop (B.off_axis u hui) hv.1 hrow hδ hc hF g hg' hmaj
    have hr (s : ℝ) (hs : s ∈ Icc (vb u) v) : 0 < S.r u s :=
      hSE.r_pos (u, s) (hrow ⟨rfl, hs⟩) ((B.off_axis u hui).trans_le hs.1)
    have cr := Calculus.continuousOn_out_section hSE.cont_r hrow
    have cweight : ContinuousOn (fun s => (S.r u s / S.r u v) ^ p * P (u, s)) (Icc (vb u) v) :=
      ((cr.div_const _).rpow_const (fun s hs => Or.inl (div_pos (hr s hs) (hr v ⟨hv.1,
        le_rfl⟩)).ne')).mul
        (hP.comp (continuousOn_const.prodMk continuousOn_id) (fun s hs => hrow ⟨rfl, hs⟩))
    have heq := ofReal_integral_weighted_envelope hv.1 hsub g hg' hg0 G hGeq _ cweight
      (fun s hs => mul_nonneg (Real.rpow_nonneg (div_nonneg (hr s hs).le (hr v ⟨hv.1,
        le_rfl⟩).le) _) (hP0 (u, s) (hrow ⟨rfl, hs⟩)))
    have hn := (neg_pos.mpr (hSE.nu_neg (u, v) (hrow ⟨rfl, hv.1, le_rfl⟩))).le
    have hrv := hr v ⟨hv.1, le_rfl⟩
    apply (ENNReal.ofReal_le_ofReal hpt).trans_eq
    change ENNReal.ofReal (β * ((-S.nu u v) / S.r u v ^ 3) * _) = _
    rw [ENNReal.ofReal_mul (mul_nonneg hβ.le (by positivity)), ENNReal.ofReal_mul hβ.le, heq,
      mul_assoc]
  calc
    _ ≤ ENNReal.ofReal β * (∫⁻ u in U, ∫⁻ v in Icc (vb u) 0,
        ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 3) *
          (∫⁻ s in Icc (vb u) v, ENNReal.ofReal ((S.r u s / S.r u v) ^ p * P (u, s)) * G s)) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply setLIntegral_mono' measurableSet_Icc
      intro u hu
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact setLIntegral_mono' measurableSet_Icc (hpoint u hu)
    _ ≤ ENNReal.ofReal β * (ENNReal.ofReal ((Kb * E n) / (c * (2 + p - ε))) *
        (∫⁻ s in Icc v₀ 0, G s)) := by
      gcongr
      exact radial_history_kernel_of_label_bound hS B hstop hc hq n P hP hP0 G hG hlabel
    _ = _ := by
      rw [hmass, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hβ.le]
      congr 1
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

end EmcsfAcExtension.Global.InteractionEstimate
