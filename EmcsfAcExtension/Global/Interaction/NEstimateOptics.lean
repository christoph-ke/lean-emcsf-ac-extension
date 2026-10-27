module

public import EmcsfAcExtension.Global.Interaction.NEstimate
public import EmcsfAcExtension.Global.Interaction.WrappersOptical

/-! # Charged source and optical estimates with one uniform constant

The total weighted source estimate and both landed optical estimates are
combined at a common late entry. All profiles are derived from the stopped
source hypotheses. Source: `charged_SF_new_version.tex:L3589–L3623`.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global.Interaction

open InteractionEstimate

/-- [node prop:ct-interaction]
All three conclusions of the charged source and optical proposition on
each sufficiently late stopped finite exterior, with assigned connectors.
The single positive constant depends only on `δ, c, Λ, F, ε, ρ`, including
the gap and connector ratio, before coupling, canonical `M₀`, radius,
stage count and duration. `Jstop` is fixed before the common late entry.
No scalar, charge or source estimate is assumed.
Source: `charged_SF_new_version.tex:L3589–L3623`. -/
theorem source_and_optics_of_stopped (δ c Λ F ε ρ : ℝ)
    (hbox : ExteriorBox δ c Λ F ε ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ui e : ℝ) (S : Fields),
      OriginalData ui e S → SignedTerminalBound ui S → ∀ Jstop : ℝ,
      ∃ a ∈ Ioo ui 0, ∀ (u₀ u₁ v₀ R₀ : ℝ) (vb g en : ℝ → ℝ)
        (N : ℕ) (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) (E : Fin N → ℝ),
        a ≤ u₀ → StoppedProfileData ui u₀ u₁ v₀ R₀ δ c Λ F ε Jstop S vb g →
        (∀ u ∈ Icc u₀ u₁, S.m u (vb u) / S.r u (vb u) ≤ en u ∧ en u ≤ F ^ 2) →
        BoundaryBudgets S ui u₀ u₁ v₀ ρ vb N B E →
        let J := ∫ v in v₀..0, g v
        let E₁ := ∑ n, E n
        let Ehalf := ∑ n, Real.sqrt (E n)
        let ζ₂ := Local.sigma e (scalarBackground ui R₀ c F Jstop S) (2 * R₀)
        sourceInteraction e S (exteriorDomain ui u₀ u₁ vb) v₀ ≤
          ENNReal.ofReal (C * E₁ + C * J * E₁ + C * F * J * Ehalf +
            C * F * J ^ 2 + C * ζ₂ * (1 + J)) ∧
        (⨆ v ∈ Icc v₀ 0,
          ∫⁻ u in {u | (u, v) ∈ exteriorDomain ui u₀ u₁ vb},
            ENNReal.ofReal (positiveExpIntegrand S u v)) ≤
          ENNReal.ofReal (C * E₁ + C * J ^ 2 + C * ζ₂) ∧
        ∀ u ∈ Icc u₀ u₁,
          Real.log ((-S.nu u 0) / (-S.nu u (vb u))) ≤
            C * (S.m u (vb u) / S.r u (vb u) +
              ‖S.theta u (vb u) / S.lam u (vb u)‖ ^ 2 + J ^ 2 + ζ₂) := by
  obtain ⟨Cn, hCn, hn⟩ := ct_n_estimate_of_stopped δ c Λ F ε ρ hbox
  obtain ⟨Ci, hCi, hi⟩ := ct_optical_in_of_stopped δ c Λ F ε ρ hbox
  obtain ⟨Co, hCo, ho⟩ := ct_optical_out_of_stopped δ c Λ F ε ρ hbox
  let C := Cn + Ci + Co
  have hC : 0 < C := by dsimp [C]; positivity
  have hCnC : Cn ≤ C := by dsimp [C]; linarith only [hCi, hCo]
  have hCiC : Ci ≤ C := by dsimp [C]; linarith only [hCn, hCo]
  have hCoC : Co ≤ C := by dsimp [C]; linarith only [hCn, hCi]
  refine ⟨C, hC, ?_⟩
  intro ui e S h hs Jstop
  obtain ⟨an, han, hn⟩ := hn ui e S h hs Jstop
  obtain ⟨ai, hai, hi⟩ := hi ui e S h hs Jstop
  obtain ⟨ao, hao, ho⟩ := ho ui e S h hs Jstop
  let a := max an (max ai ao)
  have ha : a ∈ Ioo ui 0 :=
    ⟨han.1.trans_le (le_max_left _ _), max_lt han.2 (max_lt hai.2 hao.2)⟩
  refine ⟨a, ha, ?_⟩
  intro u₀ u₁ v₀ R₀ vb g en N B E hau d hbudget hE
  have han0 := (le_max_left an (max ai ao)).trans hau
  have hai0 := ((le_max_left ai ao).trans (le_max_right an (max ai ao))).trans hau
  have hao0 := ((le_max_right ai ao).trans (le_max_right an (max ai ao))).trans hau
  have hn := hn u₀ u₁ v₀ R₀ vb g en N B E han0 d hbudget hE
  have hi := hi u₀ u₁ v₀ R₀ vb g en N B E hai0 d hbudget hE
  have ho := ho u₀ u₁ v₀ R₀ vb g en hao0 d hbudget
  dsimp only at hn ⊢
  have hab : u₀ ≤ u₁ := by
    simpa only [B.first, B.last] using B.ordered (Fin.zero_le (Fin.last N))
  have hv₀ : v₀ ≤ 0 := (finite_boundary_label_bounds B u₀ ⟨le_rfl, hab⟩).1.trans
    (finite_boundary_label_bounds B u₀ ⟨le_rfl, hab⟩).2
  have hJ : 0 ≤ ∫ v in v₀..0, g v :=
    intervalIntegral.integral_nonneg_of_ae_restrict hv₀ d.nonneg
  have hE₁ : 0 ≤ ∑ n, E n := Finset.sum_nonneg (fun n _ => (hE n).1)
  have hEh : 0 ≤ ∑ n, Real.sqrt (E n) := Finset.sum_nonneg (fun n _ => Real.sqrt_nonneg _)
  have hζ : 0 ≤ Local.sigma e (scalarBackground ui R₀ c F Jstop S) (2 * R₀) := by
    unfold Local.sigma
    positivity
  have hF : 0 ≤ F := hbox.2.2.2.2.1
  refine ⟨hn.trans (ENNReal.ofReal_le_ofReal ?_), ?_, ?_⟩
  · gcongr
  · apply iSup_le
    intro v
    apply iSup_le
    intro hv
    have hist : {u | (u, v) ∈ exteriorDomain ui u₀ u₁ vb} =
        {u | u ∈ Icc u₀ u₁ ∧ vb u ≤ v} := by
      ext u
      constructor
      · intro hp
        exact ⟨⟨hp.2.1, hp.2.2.1⟩, hp.2.2.2⟩
      · rintro ⟨hu, hvu⟩
        exact finite_boundary_row B u hu ⟨rfl, hvu, hv.2⟩
    rw [hist]
    have hhist := (le_iSup_of_le v (le_iSup_of_le hv le_rfl)).trans hi
    apply hhist.trans
    apply ENNReal.ofReal_le_ofReal
    gcongr
  · intro u hu
    apply (ho u hu).trans
    have hμ := (d.stops (u, vb u) (finite_boundary_row B u hu
      ⟨rfl, le_rfl, (B.mem u hu).2.2.2⟩)).1
    have hm : 0 ≤ S.m u (vb u) / S.r u (vb u) := by
      have heq : S.m u (vb u) / S.r u (vb u) = S.mu u (vb u) / 2 := by
        unfold Fields.mu
        ring
      rw [heq]
      positivity
    exact mul_le_mul_of_nonneg_right hCoC (by positivity)

end EmcsfAcExtension.Global.Interaction
