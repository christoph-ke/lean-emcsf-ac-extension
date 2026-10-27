module

public import EmcsfAcExtension.Global.Interaction.BoundaryKernels
public import EmcsfAcExtension.Global.Interaction.ConnectorKernels
import EmcsfAcExtension.Local.Api.Mono
import EmcsfAcExtension.Global.Calculus.Sections
import Mathlib.Tactic

/-! # Weighted boundary moments on actual stage histories

The boundary budget and the incoming radius kernels are combined before
integrating the source label. Both cylinders and their assigned connectors
are covered by the fixed radius range.
Source: charged_SF_new_version.tex:L3673–L3704; internal project record `(sb)`, `(ib)`.
-/

public section
open Set MeasureTheory
open scoped ENNReal
namespace EmcsfAcExtension.Global.InteractionEstimate

/-- [internal]
The source/boundary curvature label moment is bounded by
`(2/ρ + sqrt (ρ^(ε-3)/(3-ε))) E_n`. The coefficient depends only on
`ρ,ε`, before fields, budget, radius, stage, label, and duration. -/
theorem source_boundary_label_budget {e ui u₀ u₁ v₀ ρ δ c Λ F ε : ℝ}
    {S : Fields} {vb : ℝ → ℝ} {N : ℕ}
    (hS : IsSolution e S (origDomain ui))
    (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) {E : Fin N → ℝ}
    (hE : BoundaryBudgets S ui u₀ u₁ v₀ ρ vb N B E)
    (hstop : ExteriorStops S (exteriorDomain ui u₀ u₁ vb) δ c Λ F ε)
    (hρ : 0 < ρ) (hε : ε < 3) (n : Fin N)
    {a b s : ℝ} (hab : a ≤ b) (hbs : b ≤ s)
    (hin : inSeg a b s ⊆ exteriorDomain ui u₀ u₁ vb)
    {U : Set ℝ} (hU : MeasurableSet U) (hsub : U ⊆ Icc a b)
    (hstage : U ⊆ Icc (B.cuts n.castSucc) (B.cuts n.succ))
    (hlabel : ∀ u ∈ U, vb u ≤ s)
    (hrows : ∀ u ∈ U, outSeg u (vb u) s ⊆ exteriorDomain ui u₀ u₁ vb) :
    (∫⁻ u in U, ENNReal.ofReal (S.r u (vb u) *
      (S.mu u (vb u) + ‖S.theta u (vb u) / S.lam u (vb u)‖ *
        ‖S.xi u (vb u) / S.nu u (vb u)‖) * (-S.nu u s) / S.r u s ^ 2)) ≤
      ENNReal.ofReal ((2 / ρ + Real.sqrt (ρ ^ (ε - 3) / (3 - ε))) * E n) := by
  classical
  let D := exteriorDomain ui u₀ u₁ vb
  have hSE : IsSolution e S D := Local.isSolution_mono hS inter_subset_left
  have hui (u : ℝ) (hu : u ∈ U) : u ∈ Icc u₀ u₁ := finite_boundary_stage_subset B n (hstage hu)
  let rb := fun u => S.r u (vb u)
  let nb := fun u => -S.nu u (vb u)
  let ns := fun u => -S.nu u s
  let rs := fun u => S.r u s
  let y := fun u => ‖S.theta u (vb u) / S.lam u (vb u)‖
  let z := fun u => ‖S.xi u (vb u) / S.nu u (vb u)‖
  let m := fun u => S.mu u (vb u)
  have hrb (u : ℝ) (hu : u ∈ U) : 0 < rb u := hS.r_pos (u, vb u) (B.mem u (hui u hu))
    (B.off_axis u (hui u hu))
  have hnb (u : ℝ) (hu : u ∈ U) : 0 < nb u := neg_pos.mpr (hS.nu_neg (u, vb u) (B.mem u (hui u hu)))
  have hrs (u : ℝ) (hu : u ∈ U) : 0 < rs u := hSE.r_pos (u, s)
    (hrows u hu ⟨rfl, hlabel u hu, le_rfl⟩) ((B.off_axis u (hui u hu)).trans_le (hlabel u hu))
  have hns (u : ℝ) (hu : u ∈ U) : 0 < ns u := neg_pos.mpr
    (hSE.nu_neg (u, s) (hrows u hu ⟨rfl, hlabel u hu, le_rfl⟩))
  have hm (u : ℝ) (hu : u ∈ U) : 0 ≤ m u :=
    (hstop (u, vb u) (hrows u hu ⟨rfl, le_rfl, hlabel u hu⟩)).1
  have hEn : 0 ≤ E n := (hE n).1
  have hBn : 0 < B.radii n := B.radius_pos n
  have hgap : 0 < 3 - ε := sub_pos.mpr hε
  have hsup (u : ℝ) (hu : u ∈ U) : m u ≤ 2 * E n ∧ y u ≤ Real.sqrt (E n) := by
    have he := (hE n).2.1 u (hstage hu)
    have hmr : 0 ≤ S.m u (vb u) / S.r u (vb u) := by
      have heq : S.m u (vb u) / S.r u (vb u) = m u / 2 := by dsimp [m, Fields.mu]; ring
      rw [heq]
      exact div_nonneg (hm u hu) (by norm_num)
    constructor
    · have heq : m u = 2 * (S.m u (vb u) / S.r u (vb u)) := by dsimp [m, Fields.mu]; ring
      rw [heq]
      nlinarith only [he, sq_nonneg (y u)]
    · calc
        y u = Real.sqrt (y u ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt (E n) := Real.sqrt_le_sqrt (by dsimp [y]; linarith only [he, hmr])
  have hp : ContinuousOn (fun u => (u, vb u)) (Icc u₀ u₁) := continuousOn_id.prodMk B.cont
  have crb := (hS.cont_r.comp hp B.mem).mono (fun u hu => hui u hu)
  have cnb := (hS.cont_nu.comp hp B.mem).neg.mono (fun u hu => hui u hu)
  have crs := (Calculus.continuousOn_in_section hSE.cont_r hin).mono hsub
  have cns := (Calculus.continuousOn_in_section hSE.cont_nu hin).neg.mono hsub
  obtain ⟨cy, cz, cm, cw⟩ := continuousOn_boundary_traces hS B
  have cyU := cy.mono (fun u hu => hui u hu)
  have czU := cz.mono (fun u hu => hui u hu)
  have cmU := cm.mono (fun u hu => hui u hu)
  let f := fun u => z u ^ 2 * nb u / rb u
  let g := fun u => rb u ^ 3 / rs u ^ 4 * (ns u / nb u) ^ 2 * nb u
  let q := fun u => rb u * z u * ns u / rs u ^ 2
  have cf : ContinuousOn f U := ((czU.pow 2).mul cnb).div crb (fun u hu => (hrb u hu).ne')
  have cg : ContinuousOn g U :=
    (((crb.pow 3).div (crs.pow 4) (fun u hu => pow_ne_zero _ (hrs u hu).ne')).mul
      ((cns.div cnb (fun u hu => (hnb u hu).ne')).pow 2)).mul cnb
  have hif : (∫⁻ u in U, ENNReal.ofReal (f u)) ≤ ENNReal.ofReal (E n) := by
    apply le_trans _ (boundary_budget_lintegral hS B hE n hstage)
    apply setLIntegral_mono' hU
    intro u hu
    apply ENNReal.ofReal_le_ofReal
    change z u ^ 2 * nb u / rb u ≤ (y u ^ 2 + z u ^ 2 + m u ^ 2) * nb u / rb u
    have hn := hnb u hu
    have hr := hrb u hu
    apply div_le_div_of_nonneg_right _ hr.le
    apply mul_le_mul_of_nonneg_right _ hn.le
    nlinarith only [sq_nonneg (y u), sq_nonneg (m u)]
  have hig : (∫⁻ u in U, ENNReal.ofReal (g u)) ≤
      ENNReal.ofReal (ρ ^ (ε - 3) / (3 - ε)) :=
    stage_source_boundary_kernel hSE hstop hab hbs hin hU hsub hρ (B.radius_pos n) hε vb
      (fun u hu => ⟨B.off_axis u (hui u hu), hlabel u hu, hrows u hu⟩)
      (fun u hu => B.radius_range n u (hstage hu))
  have hK : 0 ≤ ρ ^ (ε - 3) / (3 - ε) := by positivity
  have hcauchy := lintegral_cauchy_of_square_factorization hU q f g hEn hK
    (ENNReal.continuous_ofReal.comp_continuousOn cf |>.aemeasurable hU)
    (ENNReal.continuous_ofReal.comp_continuousOn cg |>.aemeasurable hU)
    (by
      intro u hu
      have hr := hrb u hu
      have hn := hnb u hu
      have hR := hrs u hu
      have hN := hns u hu
      have hz : 0 ≤ z u := norm_nonneg _
      refine ⟨by dsimp [q]; positivity, by dsimp [f]; positivity,
        by dsimp [g]; positivity, ?_⟩
      dsimp only [q, f, g]
      field_simp [hr.ne', hn.ne', hR.ne']) hif hig
  have hscalar : (∫⁻ u in U, ENNReal.ofReal (rb u * y u * z u * ns u / rs u ^ 2)) ≤
      ENNReal.ofReal (E n * Real.sqrt (ρ ^ (ε - 3) / (3 - ε))) := by
    calc
      _ ≤ ∫⁻ u in U, ENNReal.ofReal (Real.sqrt (E n)) * ENNReal.ofReal (q u) := by
        apply setLIntegral_mono' hU
        intro u hu
        have hr := hrb u hu
        have hn := hns u hu
        have hR := hrs u hu
        have hz : 0 ≤ z u := norm_nonneg _
        rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        dsimp only [q]
        calc
          _ = y u * (rb u * z u * ns u / rs u ^ 2) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (hsup u hu).2 (by positivity)
      _ = ENNReal.ofReal (Real.sqrt (E n)) * (∫⁻ u in U, ENNReal.ofReal (q u)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Real.sqrt (E n)) * ENNReal.ofReal
          (Real.sqrt (E n) * Real.sqrt (ρ ^ (ε - 3) / (3 - ε))) := by gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← mul_assoc, Real.mul_self_sqrt hEn]
  have hradius (u : ℝ) (hu : u ∈ U) : ρ * B.radii n ≤ S.r u s :=
    (B.radius_range n u (hstage hu)).1.trans
      ((outgoing_radius_calculus hSE (B.off_axis u (hui u hu)).le (hlabel u hu) (hrows u
        hu)).2.monotoneOn
        ⟨le_rfl, hlabel u hu⟩ ⟨hlabel u hu, le_rfl⟩ (hlabel u hu))
  have hmass : (∫⁻ u in U, ENNReal.ofReal (rb u * m u * ns u / rs u ^ 2)) ≤
      ENNReal.ofReal (2 / ρ * E n) := by
    calc
      _ ≤ ∫⁻ u in U, ENNReal.ofReal (2 * E n * B.radii n) *
          ENNReal.ofReal (ns u / rs u ^ 2) := by
        apply setLIntegral_mono' hU
        intro u hu
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have hh := mul_le_mul (B.radius_range n u (hstage hu)).2 (hsup u hu).1
          (hm u hu) (B.radius_pos n).le
        calc
          _ ≤ (B.radii n * (2 * E n)) * ns u / rs u ^ 2 :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hh (hns u hu).le) (sq_nonneg _)
          _ = _ := by ring
      _ = ENNReal.ofReal (2 * E n * B.radii n) * ∫⁻ u in U, ENNReal.ofReal (ns u / rs u ^ 2) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (2 * E n * B.radii n) * ENNReal.ofReal (1 / (ρ * B.radii n)) := by
        gcongr
        exact incoming_inverse_square_kernel hSE hab hbs hin hU hsub (mul_pos hρ (B.radius_pos
          n)) hradius
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp [(B.radius_pos n).ne', hρ.ne']
  have cMass : ContinuousOn (fun u => ENNReal.ofReal (rb u * m u * ns u / rs u ^ 2)) U :=
    ENNReal.continuous_ofReal.comp_continuousOn
      (((crb.mul cmU).mul cns).div (crs.pow 2) (fun u hu => pow_ne_zero _ (hrs u hu).ne'))
  calc
    _ = ∫⁻ u in U, ENNReal.ofReal (rb u * m u * ns u / rs u ^ 2) +
        ENNReal.ofReal (rb u * y u * z u * ns u / rs u ^ 2) := by
      apply setLIntegral_congr_fun hU
      intro u hu
      have hr := hrb u hu
      have hn := hns u hu
      have hR := hrs u hu
      have hμ := hm u hu
      have hy : 0 ≤ y u := norm_nonneg _
      have hz : 0 ≤ z u := norm_nonneg _
      change ENNReal.ofReal (rb u * (m u + y u * z u) * ns u / rs u ^ 2) = _
      rw [show rb u * (m u + y u * z u) * ns u / rs u ^ 2 =
        rb u * m u * ns u / rs u ^ 2 + rb u * y u * z u * ns u / rs u ^ 2 by ring,
        ENNReal.ofReal_add (by positivity) (by positivity)]
    _ = (∫⁻ u in U, ENNReal.ofReal (rb u * m u * ns u / rs u ^ 2)) +
        (∫⁻ u in U, ENNReal.ofReal (rb u * y u * z u * ns u / rs u ^ 2)) :=
      lintegral_add_left' (cMass.aemeasurable hU) _
    _ ≤ ENNReal.ofReal (2 / ρ * E n) +
        ENNReal.ofReal (E n * Real.sqrt (ρ ^ (ε - 3) / (3 - ε))) := add_le_add hmass hscalar
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- [internal]
The incoming boundary label moment costs
`sqrt (2 max (1,(1-F²-ε)⁻²)) sqrt (ρ⁻¹) sqrt E_n`.
The coefficient depends only on `F,ε,ρ`, before every physical parameter,
stage radius, budget, label, and duration. Both square moments are supplied
by the actual field budget and the incoming radius kernel. -/
theorem incoming_boundary_label_budget {e ui u₀ u₁ v₀ ρ δ c Λ F ε : ℝ}
    {S : Fields} {vb : ℝ → ℝ} {N : ℕ}
    (hS : IsSolution e S (origDomain ui))
    (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) {E : Fin N → ℝ}
    (hE : BoundaryBudgets S ui u₀ u₁ v₀ ρ vb N B E)
    (hstop : ExteriorStops S (exteriorDomain ui u₀ u₁ vb) δ c Λ F ε)
    (hρ : 0 < ρ) (hd : 0 < 1 - F ^ 2 - ε) (n : Fin N)
    {a b s : ℝ} (hab : a ≤ b) (hbs : b ≤ s)
    (hin : inSeg a b s ⊆ exteriorDomain ui u₀ u₁ vb)
    {U : Set ℝ} (hU : MeasurableSet U) (hsub : U ⊆ Icc a b)
    (hstage : U ⊆ Icc (B.cuts n.castSucc) (B.cuts n.succ))
    (hlabel : ∀ u ∈ U, vb u ≤ s)
    (hrows : ∀ u ∈ U, outSeg u (vb u) s ⊆ exteriorDomain ui u₀ u₁ vb) :
    (∫⁻ u in U, ENNReal.ofReal
      ((‖S.xi u (vb u) / S.nu u (vb u)‖ +
        ‖S.theta u (vb u) / S.lam u (vb u)‖ / (1 - F ^ 2 - ε)) *
        (-S.nu u (vb u)) / S.r u s)) ≤
      ENNReal.ofReal (Real.sqrt (2 * max (1 : ℝ) ((1 - F ^ 2 - ε)⁻¹ ^ 2)) *
        Real.sqrt ρ⁻¹ * Real.sqrt (E n)) := by
  let D := exteriorDomain ui u₀ u₁ vb
  have hSE : IsSolution e S D := Local.isSolution_mono hS inter_subset_left
  have hui (u : ℝ) (hu : u ∈ U) : u ∈ Icc u₀ u₁ := finite_boundary_stage_subset B n (hstage hu)
  let rb := fun u => S.r u (vb u)
  let nb := fun u => -S.nu u (vb u)
  let rs := fun u => S.r u s
  let y := fun u => ‖S.theta u (vb u) / S.lam u (vb u)‖
  let z := fun u => ‖S.xi u (vb u) / S.nu u (vb u)‖
  let m := fun u => S.mu u (vb u)
  let d := 1 - F ^ 2 - ε
  let K := 2 * max (1 : ℝ) (d⁻¹ ^ 2)
  let A := fun u => z u + y u / d
  let f := fun u => A u ^ 2 * nb u / rb u
  let g := fun u => rb u * nb u / rs u ^ 2
  let q := fun u => A u * nb u / rs u
  have hrb (u : ℝ) (hu : u ∈ U) : 0 < rb u :=
    hS.r_pos (u, vb u) (B.mem u (hui u hu)) (B.off_axis u (hui u hu))
  have hnb (u : ℝ) (hu : u ∈ U) : 0 < nb u :=
    neg_pos.mpr (hS.nu_neg (u, vb u) (B.mem u (hui u hu)))
  have hrs (u : ℝ) (hu : u ∈ U) : 0 < rs u := hSE.r_pos (u, s)
    (hrows u hu ⟨rfl, hlabel u hu, le_rfl⟩) ((B.off_axis u (hui u hu)).trans_le (hlabel u hu))
  have hA (u : ℝ) : 0 ≤ A u := add_nonneg (norm_nonneg _) (div_nonneg (norm_nonneg _) hd.le)
  have hK : 0 < K := by dsimp [K]; positivity
  have hEn : 0 ≤ E n := (hE n).1
  have hAsq (u : ℝ) : A u ^ 2 ≤ K * (y u ^ 2 + z u ^ 2 + m u ^ 2) := by
    have h₁ := mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) (d⁻¹ ^ 2)) (sq_nonneg (z u))
    have h₂ := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) (d⁻¹ ^ 2)) (sq_nonneg (y u))
    have h₃ := mul_nonneg hK.le (sq_nonneg (m u))
    have hh := sq_nonneg (z u - y u / d)
    dsimp only [A, K]
    simp only [div_eq_mul_inv] at hh ⊢
    nlinarith only [h₁, h₂, h₃, hh]
  have hp : ContinuousOn (fun u => (u, vb u)) (Icc u₀ u₁) := continuousOn_id.prodMk B.cont
  have crb := (hS.cont_r.comp hp B.mem).mono (fun u hu => hui u hu)
  have cnb := (hS.cont_nu.comp hp B.mem).neg.mono (fun u hu => hui u hu)
  have crs := (Calculus.continuousOn_in_section hSE.cont_r hin).mono hsub
  obtain ⟨cy, cz, _, _⟩ := continuousOn_boundary_traces hS B
  have cA : ContinuousOn A U := (cz.mono (fun u hu => hui u hu)).add
    ((cy.mono (fun u hu => hui u hu)).div_const d)
  have cf : ContinuousOn f U := ((cA.pow 2).mul cnb).div crb (fun u hu => (hrb u hu).ne')
  have cg : ContinuousOn g U := (crb.mul cnb).div (crs.pow 2) (fun u hu => pow_ne_zero _ (hrs u
    hu).ne')
  have hif : (∫⁻ u in U, ENNReal.ofReal (f u)) ≤ ENNReal.ofReal (K * E n) := by
    calc
      _ ≤ ∫⁻ u in U, ENNReal.ofReal K * ENNReal.ofReal
          ((y u ^ 2 + z u ^ 2 + m u ^ 2) * nb u / rb u) := by
        apply setLIntegral_mono' hU
        intro u hu
        rw [← ENNReal.ofReal_mul hK.le]
        apply ENNReal.ofReal_le_ofReal
        dsimp only [f]
        exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hAsq u)
          (hnb u hu).le) (hrb u hu).le).trans_eq (by ring)
      _ = ENNReal.ofReal K * (∫⁻ u in U, ENNReal.ofReal
          ((y u ^ 2 + z u ^ 2 + m u ^ 2) * nb u / rb u)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal K * ENNReal.ofReal (E n) := by
        gcongr
        exact boundary_budget_lintegral hS B hE n hstage
      _ = _ := (ENNReal.ofReal_mul hK.le).symm
  have hig : (∫⁻ u in U, ENNReal.ofReal (g u)) ≤ ENNReal.ofReal ρ⁻¹ :=
    stage_incoming_boundary_kernel hSE hstop hab hbs hin hU hsub hρ (B.radius_pos n) vb
      (fun u hu => ⟨B.off_axis u (hui u hu), hlabel u hu, hrows u hu⟩)
      (fun u hu => B.radius_range n u (hstage hu))
  have hh := lintegral_cauchy_of_square_factorization hU q f g (mul_nonneg hK.le hEn)
    (inv_nonneg.mpr hρ.le)
    (ENNReal.continuous_ofReal.comp_continuousOn cf |>.aemeasurable hU)
    (ENNReal.continuous_ofReal.comp_continuousOn cg |>.aemeasurable hU)
    (by
      intro u hu
      have hr := hrb u hu
      have hn := hnb u hu
      have hR := hrs u hu
      have hAu := hA u
      refine ⟨by dsimp [q]; positivity, by dsimp [f]; positivity,
        by dsimp [g]; positivity, ?_⟩
      dsimp only [q, f, g]
      field_simp [hr.ne', hR.ne']) hif hig
  apply hh.trans_eq
  congr 1
  rw [Real.sqrt_mul hK.le]
  dsimp only [K, d]
  ring

end EmcsfAcExtension.Global.InteractionEstimate
