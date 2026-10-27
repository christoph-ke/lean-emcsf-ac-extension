module

public import EmcsfAcExtension.Global.Interaction.BoundarySource
public import EmcsfAcExtension.Global.Interaction.IncomingBoundarySource
import Mathlib.Tactic

/-! # The three actual source costs on assigned connectors

A connector is a measurable portion of its full budgeted stage. The
fixed-ratio incoming kernels proved for complete stages therefore give
all three source estimates, without an inverse energy or duration factor.
Source: charged_SF_new_version.tex:L3699–L3704; internal project record connector comparison.
-/

public section
open Set MeasureTheory
open scoped ENNReal
namespace EmcsfAcExtension.Global.InteractionEstimate

/-- [node prop:ct-interaction#connector-kernel-comparison]
All three actual boundary source costs on every assigned connector are
bounded by `C E_n`, `C E_n J`, and `C F J sqrt E_n`, respectively.
The same positive constant is chosen from fixed `δ,c,Λ,F,ε,ρ` before
physical data, boundary scale, envelope, stage count, or any duration.
Only the given full-stage budget is used; its production is separate.
Source: charged_SF_new_version.tex:L3699–L3704; internal project record connector comparison. -/
theorem connector_kernel_comparison (δ c Λ F ε ρ : ℝ)
    (hbox : ExteriorBox δ c Λ F ε ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (e ui u₀ u₁ v₀ : ℝ) (S : Fields)
      (vb g : ℝ → ℝ) (N : ℕ) (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) (E : Fin N → ℝ),
      IsSolution e S (origDomain ui) → BoundaryBudgets S ui u₀ u₁ v₀ ρ vb N B E →
      ExteriorStops S (exteriorDomain ui u₀ u₁ vb) δ c Λ F ε →
      IntervalIntegrable g volume v₀ 0 →
      (∀ᵐ s ∂volume.restrict (Icc v₀ 0), 0 ≤ g s) →
      (∀ u ∈ Icc u₀ u₁, ∀ᵐ v ∂volume.restrict (Icc (vb u) 0), ‖weightedJ S u v‖ ≤ g v) →
      ∀ n : Fin N,
      ((∫⁻ u in Icc (B.cool n) (B.cuts n.succ), ∫⁻ v in Icc (vb u) 0,
        ENNReal.ofReal ‖curvatureScalarSource S u v (radialYBoundary S u (vb u) v)
          (radialCurvatureBoundary S u (vb u) v)‖) ≤ ENNReal.ofReal (C * E n)) ∧
      ((∫⁻ u in Icc (B.cool n) (B.cuts n.succ), ∫⁻ v in Icc (vb u) 0,
        ENNReal.ofReal ‖curvatureScalarSource S u v (radialYSource S u (vb u) v)
          (radialCurvatureBoundary S u (vb u) v)‖) ≤
        ENNReal.ofReal (C * E n * (∫ s in v₀..0, g s))) ∧
      ((∫⁻ u in Icc (B.cool n) (B.cuts n.succ), ∫⁻ v in Icc (vb u) 0,
        ENNReal.ofReal ‖curvatureScalarSource S u v (S.theta u v / S.lam u v)
          (radialCurvatureWith S u (vb u) v (radialZBoundary S u (vb u)))‖) ≤
        ENNReal.ofReal (C * F * (∫ s in v₀..0, g s) * Real.sqrt (E n))) := by
  obtain ⟨Cs, hCs, hs⟩ := source_boundary_curvature δ c Λ F ε ρ hbox
  obtain ⟨Ci, hCi, hi⟩ := incoming_boundary_source δ c Λ F ε ρ hbox
  rcases hbox with ⟨hδ, _, hc, hcΛ, hF, hF1, _, hp, _, _⟩
  have hep : ε < 1 - F ^ 2 := (le_max_left ε (1 / 2)).trans_lt hp
  have hq : 0 < 3 - F ^ 2 - ε := by nlinarith only [hep, sq_nonneg F]
  obtain ⟨Cb, hCb, hb⟩ := boundary_boundary_source δ c Λ F ε hδ hc hcΛ hF hF1.le hq
  let C := Cb + Cs + Ci
  have hC : 0 < C := by dsimp [C]; positivity
  have hbC : Cb ≤ C := by dsimp [C]; linarith only [hCs, hCi]
  have hsC : Cs ≤ C := by dsimp [C]; linarith only [hCb, hCi]
  have hiC : Ci ≤ C := by dsimp [C]; linarith only [hCb, hCs]
  refine ⟨C, hC, ?_⟩
  intro e ui u₀ u₁ v₀ S vb g N B E hS hE hstop hg hg0 hmajor n
  have hEn := (hE n).1
  have h01 : u₀ ≤ u₁ := calc
    _ = B.cuts 0 := B.first.symm
    _ ≤ B.cuts (Fin.last N) := B.ordered (Fin.zero_le _)
    _ = _ := B.last
  have hv0 : v₀ ≤ 0 := by rw [← B.entry_label]; exact (B.mem u₀ ⟨le_rfl, h01⟩).2.2.2
  have hJ := intervalIntegral.integral_nonneg_of_ae_restrict hv0 hg0
  have hsub : Icc (B.cool n) (B.cuts n.succ) ⊆ Icc (B.cuts n.castSucc) (B.cuts n.succ) :=
    Icc_subset_Icc (B.split n).1 le_rfl
  refine ⟨?_, ?_, ?_⟩
  · exact (lintegral_mono_set hsub).trans ((hb e ui u₀ u₁ v₀ ρ S vb N B E hS hE hstop n).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hbC hEn)))
  · apply (lintegral_mono_set hsub).trans
    apply (hs e ui u₀ u₁ v₀ S vb g N B E hS hE hstop hg hg0 hmajor n).trans
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsC
      hEn) hJ)
  · apply (lintegral_mono_set hsub).trans
    apply (hi e ui u₀ u₁ v₀ S vb g N B E hS hE hstop hg hg0 hmajor n).trans
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hiC hF) hJ) (Real.sqrt_nonneg _))

end EmcsfAcExtension.Global.InteractionEstimate
