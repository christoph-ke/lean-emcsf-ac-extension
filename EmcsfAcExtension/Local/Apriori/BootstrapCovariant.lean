module

public import EmcsfAcExtension.Local.Defs.C1Class
public import EmcsfAcExtension.Frozen.CovVarIn
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Local.Apriori.Hardy
import EmcsfAcExtension.Infra.AC.Variation
import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # Finiteness and exact norm formula for covariant variation

A continuous real connection has a C¹ unitary primitive on each compact
section. Its transported normalized scalar is therefore AC, so the frozen
variation has no infinite value before taking its real part.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local

/-- The frozen covariant variation on a complete classical incoming
section is finite. This qualitative assertion imposes no uniform bound
on the connection or on any higher derivative. -/
theorem covariant_variation_ne_top {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) : covVarIn e S.A S.b u v v ≠ ⊤ := by
  have hs : MapsTo (fun x : ℝ => (x, v)) (Icc u v) (triangle 0 T) :=
    fun x hx => ⟨hu.trans hx.1, hx.2, hvT⟩
  have cA : ContinuousOn (fun x => S.A x v) (Icc u v) :=
    hS.c1_A.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn hs
  let B : ℝ → ℝ := fun t => S.A (projIcc u v huv t) v
  have cB : Continuous B := cA.domRestrict.comp continuous_projIcc
  have hBA : ∀ x ∈ Icc u v, B x = S.A x v := by
    intro x hx
    dsimp only [B]
    rw [projIcc_of_mem huv hx]
  let F : ℝ → ℝ := fun x => ∫ t in u..x, B t
  have hdF : ∀ x, HasDerivAt F (B x) x := fun x => (cB.integral_hasStrictDerivAt u x).hasDerivAt
  have cF : ContDiff ℝ 1 F := contDiff_one_iff_deriv.mpr
    ⟨fun x => (hdF x).differentiableAt,
      by convert cB using 1; funext x; exact (hdF x).deriv⟩
  let P : ℝ → ℂ := fun x => Complex.exp (I * e * F x)
  have cP : ContDiff ℝ 1 P :=
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp cF) :
      ContDiff ℝ 1 (fun x => (I * e) * (F x : ℂ))).cexp
  have hb : ContDiffOn ℝ 1 (fun x => P x * S.b x v) (Icc u v) :=
    cP.contDiffOn.mul (hS.c1_b.comp (contDiffOn_id.prodMk contDiffOn_const) hs)
  have hac : AbsolutelyContinuousOnInterval (fun x => P x * S.b x v) u v := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le huv] using hb
  have heq : covVarIn e S.A S.b u v v = eVariationOn (fun x => P x * S.b x v) (Icc u v) := by
    apply eVariationOn.congr
    intro x hx
    have hFx : F x = ∫ t in u..x, S.A t v := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hx.1] at ht
      exact hBA t ⟨ht.1, ht.2.trans hx.2⟩
    simp only [P, hFx]
  rw [heq]
  exact hac.boundedVariationOn_Icc huv

end EmcsfAcExtension.Local
