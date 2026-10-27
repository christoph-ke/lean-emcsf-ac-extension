module

public import EmcsfAcExtension.Global.Interaction.BoundaryMoments
public import EmcsfAcExtension.Global.Interaction.BoundarySourceKernel
import EmcsfAcExtension.Global.Calculus.Sections
import EmcsfAcExtension.Local.Api.Mono
import Mathlib.Tactic

/-! # Incoming boundary scalar times derivative curvature source

The retained incoming expansion ratio is cancelled only after the outer
radius integration. Actual stage budgets pay the remaining square moment.
Source: charged_SF_new_version.tex:L3688–L3704; internal project record `(ib)`.
-/

public section
open Set MeasureTheory
open scoped ENNReal
namespace EmcsfAcExtension.Global.InteractionEstimate

/-- [internal]
The actual selected incoming boundary primitive is continuous at every
proper closed row endpoint. Its expansion ratio is retained literally. -/
theorem continuousOn_radialZBoundary_end {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) : ContinuousOn (radialZBoundary S u a) (Icc a b) := by
  have cn := Calculus.continuousOn_out_section hS.cont_nu hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cY := continuousOn_radialYBoundary_end hS hua hab hs
  have hr (v : ℝ) (hv : v ∈ Icc a b) : S.r u v ≠ 0 :=
    (hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)).ne'
  have hn (v : ℝ) (hv : v ∈ Icc a b) : (S.nu u v : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hS.nu_neg (u, v) (hs ⟨rfl, hv⟩)).ne
  have ci := (Complex.continuous_ofReal.comp_continuousOn ((cn.mul cl).div cr hr)).mul cY
  have cp := intervalIntegral.continuousOn_primitive_interval'
    (ci.intervalIntegrable_of_Icc hab (μ := volume)) left_mem_uIcc
  have cp' : ContinuousOn (fun v => ∫ t in a..v,
      ((S.nu u t * S.lam u t / S.r u t : ℝ) : ℂ) * radialYBoundary S u a t)
      (Icc a b) := by simpa only [uIcc_of_le hab, Pi.mul_apply, Pi.div_apply, Function.comp_def]
        using! cp
  have cRatio : ContinuousOn (fun v => ((S.nu u a / S.nu u v : ℝ) : ℂ)) (Icc a b) :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.div cn
      (fun v hv => (hS.nu_neg (u, v) (hs ⟨rfl, hv⟩)).ne))
  exact (cRatio.mul continuousOn_const).sub
    (((Complex.continuous_ofReal.comp_continuousOn cn).inv₀ hn).mul cp')

/-- [internal]
The actual curvature primitive selecting the incoming boundary piece has
its expansion-ratio weighted label majorant. Its exact coefficient is
`3Λ²F/(δc)`, uniformly in the solution, row, scales and duration. -/
theorem incoming_boundary_pointwise {e δ c Λ F ε : ℝ} {S : Fields}
    {D : Set (ℝ × ℝ)} (hS : IsSolution e S D)
    (hstop : ExteriorStops S D δ c Λ F ε) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D)
    (hδ : 0 < δ) (hc : 0 < c) (hF : 0 ≤ F) (hε : 0 ≤ ε)
    (hep : ε < 1 - F ^ 2) (g : ℝ → ℝ) (hg : IntervalIntegrable g volume a b)
    (hmajor : ∀ᵐ v ∂volume.restrict (Icc a b), ‖weightedJ S u v‖ ≤ g v) :
    ‖curvatureScalarSource S u b (S.theta u b / S.lam u b)
      (radialCurvatureWith S u a b (radialZBoundary S u a))‖ ≤
      (3 * Λ ^ 2 / (δ * c) * F) * ((-S.nu u b) / S.r u b ^ 3) *
        (∫ s in a..b, (S.r u s * ((-S.nu u a) / (-S.nu u s)) *
          (‖S.xi u a / S.nu u a‖ + ‖S.theta u a / S.lam u a‖ / (1 - F ^ 2 - ε))) * g s) := by
  let P := fun s => S.r u s * ((-S.nu u a) / (-S.nu u s)) *
    (‖S.xi u a / S.nu u a‖ + ‖S.theta u a / S.lam u a‖ / (1 - F ^ 2 - ε))
  have hr (s : ℝ) (h : s ∈ Icc a b) : 0 < S.r u s :=
    hS.r_pos (u, s) (hs ⟨rfl, h⟩) (hua.trans_le h.1)
  have hn (s : ℝ) (h : s ∈ Icc a b) : 0 < -S.nu u s :=
    neg_pos.mpr (hS.nu_neg (u, s) (hs ⟨rfl, h⟩))
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cn := (Calculus.continuousOn_out_section hS.cont_nu hs).neg
  have cP : ContinuousOn P (Icc a b) :=
    (cr.mul (continuousOn_const.div cn (fun s h => (hn s h).ne'))).mul continuousOn_const
  have cZ := continuousOn_radialZBoundary_end hS hua hab hs
  have iZ := hg.continuousOn_mul (by simpa only [uIcc_of_le hab] using cr.mul cZ.norm)
  have iP := hg.continuousOn_mul (by simpa only [uIcc_of_le hab] using cP)
  have hi : (∫ s in a..b, S.r u s * ‖radialZBoundary S u a s‖ * g s) ≤
      ∫ s in a..b, P s * g s := by
    apply intervalIntegral.integral_mono_ae_restrict hab iZ iP
    filter_upwards [hmajor, ae_restrict_mem measurableSet_Icc] with s hgs hs'
    have hgs0 := (norm_nonneg _).trans hgs
    have hz := ct_z_boundary hS hstop hua hs'.1
      (fun q hq => hs ⟨hq.1, hq.2.1, hq.2.2.trans hs'.2⟩) hF hε hep
    change S.r u s * ‖radialZBoundary S u a s‖ * g s ≤ P s * g s
    apply mul_le_mul_of_nonneg_right _ hgs0
    apply (mul_le_mul_of_nonneg_left hz (hr s hs').le).trans_eq
    dsimp only [P]
    ring
  have hrb := hr b ⟨hab, le_rfl⟩
  have hcurv := (radial_curvature_with_le hS hstop hua hab hs hc _ cZ g hg hmajor).trans
    (mul_le_mul_of_nonneg_left hi (by positivity))
  have hst := hstop (u, b) (hs ⟨rfl, hab, le_rfl⟩)
  have hnb := (hn b ⟨hab, le_rfl⟩).le
  have hl := (hS.lam_pos (u, b) (hs ⟨rfl, hab, le_rfl⟩)).le
  calc
    _ ≤ (3 * Λ ^ 2 * F / δ) * ((-S.nu u b) / S.r u b ^ 2) *
        ‖radialCurvatureWith S u a b (radialZBoundary S u a)‖ :=
      curvature_scalar_source_le S u b δ Λ F _ _ hδ (hr b ⟨hab, le_rfl⟩)
        (neg_nonneg.mp hnb) hl hst.2.2.2.1 hst.2.1 hst.2.2.2.2.1
    _ ≤ (3 * Λ ^ 2 * F / δ) * ((-S.nu u b) / S.r u b ^ 2) *
        ((c * S.r u b)⁻¹ * ∫ s in a..b, P s * g s) :=
      mul_le_mul_of_nonneg_left hcurv (by positivity)
    _ = _ := by dsimp only [P]; simp only [div_eq_mul_inv, mul_inv_rev]; ring

/-- [node prop:ct-interaction#incoming-boundary-source]
The actual incoming boundary piece in the derivative curvature source
costs `C F J sqrt E_n` on each complete stage, including its connector.
The positive constant depends only on the fixed `δ,c,Λ,F,ε,ρ`, before
physical data, envelope, stage radius and count, and every duration.
The incoming expansion ratio is cancelled after outgoing integration.
Source: charged_SF_new_version.tex:L3688–L3697; internal project record `(ib)`. -/
theorem incoming_boundary_source (δ c Λ F ε ρ : ℝ)
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
        ENNReal.ofReal ‖curvatureScalarSource S u v (S.theta u v / S.lam u v)
          (radialCurvatureWith S u (vb u) v (radialZBoundary S u (vb u)))‖) ≤
        ENNReal.ofReal (C * F * (∫ s in v₀..0, g s) * Real.sqrt (E n)) := by
  rcases hbox with ⟨hδ, _, hc, hcΛ, hF, _, hε, hp, hρ, _⟩
  let β := 3 * Λ ^ 2 / (δ * c)
  let Kb := Real.sqrt (2 * max (1 : ℝ) ((1 - F ^ 2 - ε)⁻¹ ^ 2)) * Real.sqrt ρ⁻¹
  have hΛ : 0 < Λ := hc.trans_le hcΛ
  have hep : ε < 1 - F ^ 2 := (le_max_left ε (1 / 2)).trans_lt hp
  have hd : 0 < 1 - F ^ 2 - ε := sub_pos.mpr hep
  have hε2 : ε < 2 := by nlinarith only [hep, sq_nonneg F]
  have hq : 0 < 2 + (0 : ℝ) - ε := by linarith only [hε2]
  have hβ : 0 < β := by dsimp [β]; positivity
  have hKb : 0 < Kb := by dsimp [Kb]; positivity
  refine ⟨β * Kb / (c * (2 - ε)), by positivity, ?_⟩
  intro e ui u₀ u₁ v₀ S vb g N B E hS hE hstop hg hg0 hmajor n
  let D := exteriorDomain ui u₀ u₁ vb
  let A := fun u => ‖S.xi u (vb u) / S.nu u (vb u)‖ +
    ‖S.theta u (vb u) / S.lam u (vb u)‖ / (1 - F ^ 2 - ε)
  let P := fun z : ℝ × ℝ => S.r z.1 z.2 * ((-S.nu z.1 (vb z.1)) / (-S.nu z.1 z.2)) * A z.1
  let U := Icc (B.cuts n.castSucc) (B.cuts n.succ)
  have hSE : IsSolution e S D := Local.isSolution_mono hS inter_subset_left
  have h01 : u₀ ≤ u₁ := calc
    _ = B.cuts 0 := B.first.symm
    _ ≤ B.cuts (Fin.last N) := B.ordered (Fin.zero_le _)
    _ = _ := B.last
  have hv0 : v₀ ≤ 0 := by rw [← B.entry_label]; exact (B.mem u₀ ⟨le_rfl, h01⟩).2.2.2
  obtain ⟨G, hG, hGeq, hmass⟩ := exists_measurable_envelope hv0 g hg hg0
  have hpB : ContinuousOn (fun u => (u, vb u)) (Icc u₀ u₁) := continuousOn_id.prodMk B.cont
  obtain ⟨cy, cz, _, _⟩ := continuousOn_boundary_traces hS B
  have cAb : ContinuousOn A (Icc u₀ u₁) := cz.add (cy.div_const _)
  have cNb : ContinuousOn (fun u => -S.nu u (vb u)) (Icc u₀ u₁) := (hS.cont_nu.comp hpB B.mem).neg
  have hmap : ∀ z ∈ D, z.1 ∈ Icc u₀ u₁ := fun z hz => ⟨hz.2.1, hz.2.2.1⟩
  have hn (z : ℝ × ℝ) (hz : z ∈ D) : 0 < -S.nu z.1 z.2 := neg_pos.mpr (hSE.nu_neg z hz)
  have hP : ContinuousOn P D :=
    (hSE.cont_r.mul ((cNb.comp continuousOn_fst hmap).div hSE.cont_nu.neg
      (fun z hz => (hn z hz).ne'))).mul (cAb.comp continuousOn_fst hmap)
  have hP0 (z : ℝ × ℝ) (hz : z ∈ D) : 0 ≤ P z := by
    have hui := hmap z hz
    have hnb := neg_pos.mpr (hS.nu_neg (z.1, vb z.1) (B.mem z.1 hui))
    have hns := hn z hz
    have hr := hSE.r_pos z hz ((B.off_axis z.1 hui).trans_le hz.2.2.2)
    dsimp only [P, A]
    positivity
  have hlabel (s : ℝ) (hs : s ∈ Icc v₀ 0) :
      (∫⁻ u in U ∩ {u | vb u ≤ s}, ENNReal.ofReal (P (u, s) * (-S.nu u s) / S.r u s ^ 2)) ≤
        ENNReal.ofReal (Kb * Real.sqrt (E n)) := by
    obtain ⟨z, hz, hzs, hist, hin⟩ := label_history_interval B hs
    have hset : U ∩ {u | vb u ≤ s} = U ∩ Icc u₀ z := by
      ext u
      constructor
      · rintro ⟨hu, hvs⟩
        exact ⟨hu, hist ▸ ⟨finite_boundary_stage_subset B n hu, hvs⟩⟩
      · rintro ⟨hu, huz⟩
        exact ⟨hu, (show u ∈ {u | u ∈ Icc u₀ u₁ ∧ vb u ≤ s} from hist.symm ▸ huz).2⟩
    rw [hset]
    have heq : (∫⁻ u in U ∩ Icc u₀ z, ENNReal.ofReal (P (u, s) * (-S.nu u s) / S.r u s ^ 2)) =
        ∫⁻ u in U ∩ Icc u₀ z, ENNReal.ofReal (A u * (-S.nu u (vb u)) / S.r u s) := by
      apply setLIntegral_congr_fun (measurableSet_Icc.inter measurableSet_Icc)
      intro u hu
      have humem : u ∈ {u | u ∈ Icc u₀ u₁ ∧ vb u ≤ s} := hist.symm ▸ hu.2
      have hmem : (u, s) ∈ D := finite_boundary_row B u humem.1 ⟨rfl, humem.2, hs.2⟩
      have hns := hn (u, s) hmem
      have hr := hSE.r_pos (u, s) hmem ((B.off_axis u humem.1).trans_le humem.2)
      change ENNReal.ofReal (P (u, s) * (-S.nu u s) / S.r u s ^ 2) = _
      congr 1
      dsimp only [P]
      have hns' : S.nu u s ≠ 0 := (hSE.nu_neg (u, s) hmem).ne
      field_simp [hns', hr.ne']
    rw [heq]
    have hh := incoming_boundary_label_budget hS B hE hstop hρ hd n hz.1 hzs.le hin
      (measurableSet_Icc.inter measurableSet_Icc) inter_subset_right inter_subset_left
      (fun u hu => (show u ∈ {u | u ∈ Icc u₀ u₁ ∧ vb u ≤ s} from hist.symm ▸ hu.2).2)
      (fun u hu q hq => finite_boundary_row B u (finite_boundary_stage_subset B n hu.1)
        ⟨hq.1, hq.2.1, hq.2.2.trans hs.2⟩)
    exact hh
  have hpoint (u : ℝ) (hu : u ∈ U) (v : ℝ) (hv : v ∈ Icc (vb u) 0) :
      ENNReal.ofReal ‖curvatureScalarSource S u v (S.theta u v / S.lam u v)
        (radialCurvatureWith S u (vb u) v (radialZBoundary S u (vb u)))‖ ≤
        ENNReal.ofReal (β * F) * (ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 3) *
          (∫⁻ s in Icc (vb u) v, ENNReal.ofReal ((S.r u s / S.r u v) ^ (0 : ℝ) * P (u, s)) * G
            s)) := by
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
    have hpt := incoming_boundary_pointwise hSE hstop (B.off_axis u hui) hv.1 hrow hδ hc hF hε
      hep g hg' hmaj
    have cw : ContinuousOn (fun s => P (u, s)) (Icc (vb u) v) :=
      hP.comp (continuousOn_const.prodMk continuousOn_id) (fun s hs => hrow ⟨rfl, hs⟩)
    have heq := ofReal_integral_weighted_envelope hv.1 hsub g hg' hg0 G hGeq _ cw
      (fun s hs => hP0 (u, s) (hrow ⟨rfl, hs⟩))
    have hns := (hn (u, v) (hrow ⟨rfl, hv.1, le_rfl⟩)).le
    have hr := hSE.r_pos (u, v) (hrow ⟨rfl, hv.1, le_rfl⟩) ((B.off_axis u hui).trans_le hv.1)
    apply (ENNReal.ofReal_le_ofReal hpt).trans_eq
    change ENNReal.ofReal ((β * F) * ((-S.nu u v) / S.r u v ^ 3) * _) = _
    simp only [Real.rpow_zero, one_mul]
    rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hβ.le hF) (by positivity)),
      ENNReal.ofReal_mul (mul_nonneg hβ.le hF), heq, mul_assoc]
  calc
    _ ≤ ENNReal.ofReal (β * F) * (∫⁻ u in U, ∫⁻ v in Icc (vb u) 0,
        ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 3) *
          (∫⁻ s in Icc (vb u) v, ENNReal.ofReal ((S.r u s / S.r u v) ^ (0 : ℝ) * P (u, s)) * G
            s)) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply setLIntegral_mono' measurableSet_Icc
      intro u hu
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact setLIntegral_mono' measurableSet_Icc (hpoint u hu)
    _ ≤ ENNReal.ofReal (β * F) * (ENNReal.ofReal ((Kb * Real.sqrt (E n)) / (c * (2 + (0 : ℝ) -
      ε))) *
        (∫⁻ s in Icc v₀ 0, G s)) := by
      gcongr
      exact radial_history_kernel_of_label_bound hS B hstop hc hq n P hP hP0 G hG hlabel
    _ = _ := by
      rw [hmass, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (mul_nonneg hβ.le hF)]
      congr 1
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

end EmcsfAcExtension.Global.InteractionEstimate
