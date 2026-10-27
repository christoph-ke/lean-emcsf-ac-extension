module

public import EmcsfAcExtension.Local.Construction.ContinuationInputs
public import EmcsfAcExtension.Local.Broad.RectangleState
import EmcsfAcExtension.Local.Construction.Corner
import EmcsfAcExtension.Local.Construction.ContinuationParameters

/-! # Enlarged continuation bounds fixed before corner localization

The common old bound, the fixed entering block and its C¹ trace bound
are enlarged together before the short-cone time or corner width is
chosen. The charged threshold is capped at `1/32` because the frozen
`chargedScale` uses `T/2`, whereas the original Picard input uses `T`.
-/

public section

open Set
open scoped NNReal

namespace EmcsfAcExtension.Local

/-- Enlarged continuation parameters in the C¹ construction route.
Only the four pending producer inputs are used. Universal thresholds
precede the datum; the original wedge, entering block, common primary
bound, cone class and short-cone time precede every candidate apex and
corner width. The explicit enlargement includes both the global entering
Lipschitz coefficient and its fixed value/first-derivative bound.
The numerical charged cap is `1/32` for `chargedScale`, hence
`1/16` for the original input's product `|e| M T`. -/
theorem enlarged_continuation_parameters_of_inputs
    (hOriginal : ContinuationOriginalPicardInput) (hShort : ContinuationShortPicardInput)
    (hRecovery : ContinuationRecoveryInput) (hBound : ContinuationC1BoundInput) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      ∀ (T e : ℝ) (h : ℝ → ℂ), 0 < T → ContDiffOn ℝ 1 h (Icc 0 T) →
        datumVar h T ≤ ε → chargedScale e h T ≤ δ →
        ∃ (a : ℝ) (F₀ : Fields) (J : ℝ≥0) (yi : ℝ → Broad.RectangleIncoming)
            (B_AP Ci B Bc ℓ τ : ℝ),
          0 < a ∧ a ≤ T ∧ IsC1Solution e F₀ (continuationWedge 0 a T) ∧
          IsRestartData F₀ h T ∧
          0 < J ∧ LipschitzWith J yi ∧ ContDiffOn ℝ 1 yi (Icc 0 T) ∧
          EqOn yi (fun v => (F₀.lam 0 v,F₀.theta 0 v)) (Icc 0 T) ∧
          0 < B_AP ∧ 0 < Ci ∧ B = 4*(B_AP+(J : ℝ)+Ci+1) ∧
          0 < B ∧ (J : ℝ) ≤ B/4 ∧ Ci ≤ B/4 ∧
          (∀ v ∈ Icc 0 T, ‖yi v‖ ≤ Ci ∧ ‖derivWithin yi (Icc 0 T) v‖ ≤ Ci) ∧
          (∀ v ∈ Icc 0 T, ‖yi v‖ ≤ B/4 ∧ ‖derivWithin yi (Icc 0 T) v‖ ≤ B/4) ∧
          (∀ (s : ℝ) (F : Fields), 0 < s → s ≤ T →
            IsC1Solution e F (triangle 0 s) → IsRestartData F h s →
            C1BoundOn F (triangle 0 s) B_AP ∧ C1BoundOn F (triangle 0 s) (B/4)) ∧
          ℓ = B⁻¹ ∧ 0 < ℓ ∧ 1 ≤ Bc ∧
          Bc = 1+16*(B+1)*(1+ℓ⁻¹)+64*(B+1)^2*ℓ⁻¹^2 ∧ 0 < τ ∧
          (∀ (c L : ℝ) (lam₀ : ℝ → ℝ) (h₀ : ℝ → ℂ), 0 < L → L ≤ τ →
            ContDiffOn ℝ 1 lam₀ (Icc c (c+L)) → ContDiffOn ℝ 1 h₀ (Icc c (c+L)) →
            (∀ v ∈ Icc c (c+L), ℓ/2 ≤ lam₀ v ∧ |lam₀ v| ≤ Bc ∧ ‖h₀ v‖ ≤ Bc ∧
              |derivWithin lam₀ (Icc c (c+L)) v| ≤ Bc ∧
              ‖derivWithin h₀ (Icc c (c+L)) v‖ ≤ Bc) →
            ∃ F : Fields, IsC1Solution e F (triangle c (c+L)) ∧
              (∀ v ∈ Icc c (c+L), F.lam c v = lam₀ v ∧ F.a c v = h₀ v) ∧
              ∀ t ∈ Icc c (c+L), F.A t t = 0) ∧
          ∀ q : ℝ, 0 < q → q ≤ T →
            ∃ η : ℝ, 0 < η ∧ η < q/8 ∧ η < τ/8 := by
  obtain ⟨ε_AP,δ_AP,hε_AP,hδ_AP,hAP⟩ := hBound
  refine ⟨min ε_AP (1/64),min δ_AP (1/32),
    lt_min hε_AP (by norm_num),lt_min hδ_AP (by norm_num),?_⟩
  intro T e h hT hh hsmall hscale
  have hsmallAP : datumVar h T ≤ ε_AP := hsmall.trans (min_le_left _ _)
  have hscaleAP : chargedScale e h T ≤ δ_AP := hscale.trans (min_le_left _ _)
  have hsmallOriginal : datumVar h T ≤ 1/64 := hsmall.trans (min_le_right _ _)
  have hscaleOriginal : |e| * datumM h T*T ≤ 1/16 := by
    have heq : |e| * datumM h T*T = 2*chargedScale e h T := by
      rw [chargedScale_def]
      ring
    have hc : chargedScale e h T ≤ 1/32 := hscale.trans (min_le_right _ _)
    rw [heq]
    linarith
  obtain ⟨B_AP,hB_AP,hcommon⟩ := hAP T e h hT hh hsmallAP hscaleAP
  obtain ⟨a,F₀,ha,haT,hF₀,hdata⟩ :=
    smooth_local_solution_of_inputs hOriginal hRecovery hT hh hsmallOriginal hscaleOriginal
  obtain ⟨J,yi,hJ,hLip,hC1,hEq⟩ := continuation_original_block_extension ha haT hF₀
  obtain ⟨Ci,hCi,hTrace⟩ := continuation_c1_trace_bound hT hC1
  let B := 4*(B_AP+(J : ℝ)+Ci+1)
  have hB : 0 < B := by dsimp [B]; positivity
  have hB_AP4 : B_AP ≤ B/4 := by
    have := J.coe_nonneg
    dsimp [B]
    linarith
  have hJ4 : (J : ℝ) ≤ B/4 := by
    dsimp [B]
    linarith
  have hCi4 : Ci ≤ B/4 := by
    have := J.coe_nonneg
    dsimp [B]
    linarith
  have hTraceB : ∀ v ∈ Icc 0 T,
      ‖yi v‖ ≤ B/4 ∧ ‖derivWithin yi (Icc 0 T) v‖ ≤ B/4 := by
    intro v hv
    exact ⟨(hTrace v hv).1.trans hCi4,(hTrace v hv).2.trans hCi4⟩
  let ℓ := B⁻¹
  let Bc := 1+16*(B+1)*(1+ℓ⁻¹)+64*(B+1)^2*ℓ⁻¹^2
  have hℓ : 0 < ℓ := inv_pos.mpr hB
  have hBc : 1 ≤ Bc := by
    have hi : 0 ≤ ℓ⁻¹ := (inv_pos.mpr hℓ).le
    have h1 : 0 ≤ 16*(B+1)*(1+ℓ⁻¹) := by positivity
    have h2 : 0 ≤ 64*(B+1)^2*ℓ⁻¹^2 := by positivity
    dsimp only [Bc]
    linarith only [h1,h2]
  obtain ⟨τ,hτ,hlocal⟩ := short_cone_solution_of_inputs hShort hRecovery
    Bc (ℓ/2) e hBc (by positivity)
  refine ⟨a,F₀,J,yi,B_AP,Ci,B,Bc,ℓ,τ,ha,haT,hF₀,hdata,hJ,hLip,hC1,hEq,
    hB_AP,hCi,rfl,hB,hJ4,hCi4,hTrace,hTraceB,?_,rfl,hℓ,hBc,rfl,hτ,hlocal,?_⟩
  · intro s F hs hsT hF hd
    have hold := hcommon s F hs hsT hF hd
    exact ⟨hold,continuation_c1BoundOn_weaken hB_AP hB_AP4 hold⟩
  · intro q hq _hqT
    obtain ⟨η,hη,hηq,hητ,_hfit⟩ := continuation_corner_parameters hq hτ
    exact ⟨η,hη,hηq,hητ⟩

end EmcsfAcExtension.Local
