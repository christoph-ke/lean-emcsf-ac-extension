module

public import EmcsfAcExtension.Global.Interaction.ConnectorSources
public import EmcsfAcExtension.Global.Interaction.ElectricMixed
public import EmcsfAcExtension.Global.Interaction.BoundaryOpticalSum
import EmcsfAcExtension.Global.Interaction.ClosuresFinite
import EmcsfAcExtension.Global.Renormalized.WeakTransfer
import EmcsfAcExtension.Local.Api.Mono

/-! # Decomposition of the actual weighted interaction source

The seven estimated terms reconstruct the unchanged `weightedJSource`.
The incoming primitives are split only after proving their integrability.
Source: `charged_SF_new_version.tex:L3625–L3745`, approved internal project record.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global.InteractionEstimate

private theorem curvatureScalarSource_add_left (S : Fields) (u v : ℝ) (Y Z C : ℂ) :
    curvatureScalarSource S u v (Y + Z) C =
      curvatureScalarSource S u v Y C + curvatureScalarSource S u v Z C := by
  unfold curvatureScalarSource
  ring

private theorem curvatureScalarSource_add_right (S : Fields) (u v : ℝ) (Y C K : ℂ) :
    curvatureScalarSource S u v Y (C + K) =
      curvatureScalarSource S u v Y C + curvatureScalarSource S u v Y K := by
  simp only [curvatureScalarSource, map_add]
  ring

/-- [internal]
The full curvature primitive is the sum of its boundary, derivative and
electromagnetic incoming pieces. There are no constants or extra trace
assumptions; integrability follows from the frozen outgoing AC equation.
Source: `charged_SF_new_version.tex:L3633–L3638`, L3730–L3736. -/
theorem radial_curvature_source_split {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) :
    radialCurvatureSource S u a b =
      radialCurvatureWith S u a b (radialZBoundary S u a) +
      radialCurvatureWith S u a b (radialZSource S u a) +
      radialCurvatureWith S u a b (radialZEM e S u a) := by
  let A := fun v => (((1 - S.mu u v) * S.r u v / S.lam u v : ℝ) : ℂ)
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have cm : ContinuousOn (S.mu u) (Icc a b) := by
    simpa only [Fields.mu, Pi.mul_apply, Pi.div_apply] using!
      ((Calculus.continuousOn_out_section hS.cont_m hs).const_mul 2).div cr
        (fun v hv => (hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)).ne')
  have cA : ContinuousOn A (Icc a b) :=
    continuous_ofReal.comp_continuousOn
      (((continuousOn_const.sub cm).mul cr).div cl
        (fun v hv => (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)).ne'))
  have iW := Interaction.weightedJ_intervalIntegrable hS hua hab hs
  have hi (z : ℝ → ℂ) (hz : ContinuousOn z (Icc a b)) :
      IntervalIntegrable (fun v => A v * starRingEnd ℂ (z v) * weightedJ S u v)
        volume a b :=
    iW.continuousOn_mul (by simpa only [uIcc_of_le hab, Pi.mul_apply,
      starRingEnd_apply] using! cA.mul hz.star)
  have iB := hi _ (continuousOn_radialZBoundary_end hS hua hab hs)
  have iJ := hi _ (continuousOn_radialZSource_end hS hua hab hs)
  have iE := hi _ (continuousOn_radialZEM_end hS hua hab hs)
  have heq : (∫ v in a..b, A v * starRingEnd ℂ (S.xi u v / S.nu u v) * weightedJ S u v) =
      (∫ v in a..b, A v * starRingEnd ℂ (radialZBoundary S u a v) * weightedJ S u v) +
      (∫ v in a..b, A v * starRingEnd ℂ (radialZSource S u a v) * weightedJ S u v) +
      (∫ v in a..b, A v * starRingEnd ℂ (radialZEM e S u a v) * weightedJ S u v) := by
    rw [← intervalIntegral.integral_add iB iJ, ← intervalIntegral.integral_add (iB.add iJ) iE]
    apply intervalIntegral.integral_congr
    intro v hv
    have hv : v ∈ Icc a b := by simpa only [uIcc_of_le hab] using hv
    dsimp only
    rw [ct_z_split_identity hS hua hv.1
      (fun p hp => hs ⟨hp.1, hp.2.1, hp.2.2.trans hv.2⟩), map_add, map_add]
    ring
  unfold radialCurvatureSource radialCurvatureWith
  change (S.r u b : ℂ)⁻¹ * _ = _
  rw [heq]
  ring

/-- [internal]
Exact seven-term decomposition of the actual weighted source on a proper
closed row, including both endpoints. All coefficients are literal, with
no estimate constant. Source: `charged_SF_new_version.tex:L3625–L3745`. -/
theorem weightedJSource_seven_terms {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) :
    weightedJSource e S u b =
      curvatureScalarSource S u b (radialYBoundary S u a b) (radialCurvatureBoundary S u a b) +
      curvatureScalarSource S u b (radialYSource S u a b) (radialCurvatureBoundary S u a b) +
      curvatureScalarSource S u b (S.theta u b / S.lam u b)
        (radialCurvatureWith S u a b (radialZBoundary S u a)) +
      curvatureScalarSource S u b (S.theta u b / S.lam u b)
        (radialCurvatureWith S u a b (radialZSource S u a)) +
      curvatureScalarSource S u b (S.theta u b / S.lam u b)
        (radialCurvatureWith S u a b (radialZEM e S u a)) +
      curvatureScalarSource S u b (S.theta u b / S.lam u b) (radialCurvatureEM e S u a b) +
      ((S.lam u b / (1 - S.mu u b) : ℝ) : ℂ) * Local.emSourceJ e S u b := by
  rw [weightedJSource_eq_curvatureScalarSource e S u b
    (hS.lam_pos (u, b) (hs ⟨rfl, hab, le_rfl⟩)).ne',
    ct_c_reconstruction hS hua hab hs, radial_curvature_source_split hS hua hab hs]
  simp only [curvatureScalarSource_add_right]
  conv_lhs => arg 1; arg 1; arg 1; rw [ct_y_split_identity hS hua hab hs]
  rw [curvatureScalarSource_add_left]
  ring

end EmcsfAcExtension.Global.InteractionEstimate
