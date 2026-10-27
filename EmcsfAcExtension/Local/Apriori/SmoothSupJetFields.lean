module

public import EmcsfAcExtension.Local.Apriori.SmoothSupJet
public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Local.Calculus.Normalized
import EmcsfAcExtension.Local.Calculus.AxisCross
import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # Identifying the regular first-jet formulas with the fields

The only same-direction wave derivatives are recovered by differentiating
`θ = λ(a-φ)` and `ξ = ν(b-φ)`. The remaining entries are the literal
classical field equations and normalized cross transports.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local

/-- The numerical input for the regular first-jet formulas. Radius
quotients are used off axis; their bounds, rather than their raw axis
values, enter the closed-domain continuation argument. -/
@[expose] noncomputable def smoothJetInput (e T : ℝ) (S : Fields) (u v : ℝ) :
    (Fin 15 → ℝ) × (Fin 5 → ℂ) :=
  (![S.r u v, S.lam u v, S.nu u v, 1 - S.mu u v,
      S.Q u v / S.r u v ^ 3, S.mu u v / S.r u v ^ 2, S.A u v,
      pdU (triangle 0 T) S.lam u v, pdV (triangle 0 T) S.lam u v,
      pdU (triangle 0 T) S.nu u v, pdV (triangle 0 T) S.nu u v,
      pdU (triangle 0 T) S.A u v,
      (S.lam u v)⁻¹, (S.nu u v)⁻¹, (1 - S.mu u v)⁻¹],
    ![S.phi u v, S.theta u v / S.lam u v / S.r u v,
      S.xi u v / S.nu u v / S.r u v, pdV (triangle 0 T) S.a u v,
      pdU (triangle 0 T) S.b u v + I * e * S.A u v * S.b u v])

/-- The actual eleven field values and their partials, in the same
triple order as `smoothJetFormula`. This is a list of quantities, not
an assumed conclusion bundle. -/
@[expose] noncomputable def smoothActualJet (_e T : ℝ) (S : Fields) (u v : ℝ) : Fin 33 → ℂ :=
  ![(S.r u v : ℂ), ((pdU (triangle 0 T) S.r u v : ℝ) : ℂ), ((pdV (triangle 0 T) S.r u v : ℝ) : ℂ),
    S.lam u v, ((pdU (triangle 0 T) S.lam u v : ℝ) : ℂ), ((pdV (triangle 0 T) S.lam u v : ℝ) : ℂ),
    S.nu u v, ((pdU (triangle 0 T) S.nu u v : ℝ) : ℂ), ((pdV (triangle 0 T) S.nu u v : ℝ) : ℂ),
    S.m u v, ((pdU (triangle 0 T) S.m u v : ℝ) : ℂ), ((pdV (triangle 0 T) S.m u v : ℝ) : ℂ),
    S.Q u v, ((pdU (triangle 0 T) S.Q u v : ℝ) : ℂ), ((pdV (triangle 0 T) S.Q u v : ℝ) : ℂ),
    S.A u v, ((pdU (triangle 0 T) S.A u v : ℝ) : ℂ), ((pdV (triangle 0 T) S.A u v : ℝ) : ℂ),
    S.phi u v, pdU (triangle 0 T) S.phi u v, pdV (triangle 0 T) S.phi u v,
    S.theta u v, pdU (triangle 0 T) S.theta u v, pdV (triangle 0 T) S.theta u v,
    S.xi u v, pdU (triangle 0 T) S.xi u v, pdV (triangle 0 T) S.xi u v,
    S.a u v, pdU (triangle 0 T) S.a u v, pdV (triangle 0 T) S.a u v,
    S.b u v, pdU (triangle 0 T) S.b u v, pdV (triangle 0 T) S.b u v]

/-- Recover the outgoing scalar-wave derivative from the differentiated
normalized outgoing field, with no second derivative premise. -/
theorem smooth_theta_v_recovery_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    pdV (triangle 0 T) S.theta u v =
      pdV (triangle 0 T) S.lam u v * (S.theta u v / S.lam u v) +
        S.lam u v * (pdV (triangle 0 T) S.a u v - pdV (triangle 0 T) S.phi u v) := by
  have dl := (hasDerivWithinAt_v_aux hS.c1_lam hu huv.le hvT).ofReal_comp
  have da := hasDerivWithinAt_v_aux hS.c1_a hu huv.le hvT
  have dp := hasDerivWithinAt_v_aux hS.c1_phi hu huv.le hvT
  have he (x : ℝ) (hx : x ∈ Icc u T) :
      S.theta u x = (S.lam u x : ℂ) * (S.a u x - S.phi u x) := by
    have hl : (S.lam u x : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (hS.lam_pos (u, x) ⟨hu, hx.1, hx.2⟩).ne'
    dsimp only [Fields.a]
    field_simp [hl]; ring
  have dh := (dl.mul (da.sub dp)).congr he (he v ⟨huv.le, hvT⟩)
  have hθ := hasDerivWithinAt_v_aux hS.c1_theta hu huv.le hvT
  have hh := (uniqueDiffOn_Icc (huv.trans_le hvT) v ⟨huv.le, hvT⟩).eq_deriv _ hθ dh
  simpa only [Pi.sub_apply, Fields.a, add_sub_cancel_left] using hh

/-- Recover the incoming scalar-wave derivative from the differentiated
normalized incoming field, with no second derivative premise. -/
theorem smooth_xi_u_recovery_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    pdU (triangle 0 T) S.xi u v =
      pdU (triangle 0 T) S.nu u v * (S.xi u v / S.nu u v) +
        S.nu u v * (pdU (triangle 0 T) S.b u v - pdU (triangle 0 T) S.phi u v) := by
  have dn := (hasDerivWithinAt_u_aux hS.c1_nu hu huv.le hvT).ofReal_comp
  have db := hasDerivWithinAt_u_aux hS.c1_b hu huv.le hvT
  have dp := hasDerivWithinAt_u_aux hS.c1_phi hu huv.le hvT
  have he (x : ℝ) (hx : x ∈ Icc 0 v) :
      S.xi x v = (S.nu x v : ℂ) * (S.b x v - S.phi x v) := by
    have hn : (S.nu x v : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (hS.nu_neg (x, v) ⟨hx.1, hx.2, hvT⟩).ne
    dsimp only [Fields.b]
    field_simp [hn]; ring
  have dh := (dn.mul (db.sub dp)).congr he (he u ⟨hu, huv.le⟩)
  have hξ := hasDerivWithinAt_u_aux hS.c1_xi hu huv.le hvT
  have hh := (uniqueDiffOn_Icc (hu.trans_lt huv) u ⟨hu, huv.le⟩).eq_deriv _ hξ dh
  simpa only [Pi.sub_apply, Fields.b, add_sub_cancel_left] using hh

/-- Every actual first-jet entry is continuous on the closed nondegenerate
triangle. This uses only the classical class and its derived normalized
scalar regularity; no second derivative is asserted or needed. -/
theorem continuousOn_smoothActualJet_aux {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T)) :
    ContinuousOn (fun p : ℝ × ℝ => smoothActualJet e T S p.1 p.2) (triangle 0 T) := by
  have cr {f : ℝ → ℝ → ℝ} (hf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle 0 T)) :
      ContinuousOn (fun p : ℝ × ℝ => (f p.1 p.2 : ℂ)) (triangle 0 T) ∧
      ContinuousOn (fun p : ℝ × ℝ => ((pdU (triangle 0 T) f p.1 p.2 : ℝ) : ℂ)) (triangle 0 T) ∧
      ContinuousOn (fun p : ℝ × ℝ => ((pdV (triangle 0 T) f p.1 p.2 : ℝ) : ℂ)) (triangle 0 T) :=
    ⟨Complex.continuous_ofReal.comp_continuousOn hf.continuousOn,
      Complex.continuous_ofReal.comp_continuousOn
        (continuousOn_pdU hf (uniqueDiffOn_triangle hT)),
      Complex.continuous_ofReal.comp_continuousOn
        (continuousOn_pdV hf (uniqueDiffOn_triangle hT))⟩
  have cc {f : ℝ → ℝ → ℂ} (hf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle 0 T)) :
      ContinuousOn (Function.uncurry f) (triangle 0 T) ∧
      ContinuousOn (Function.uncurry (pdU (triangle 0 T) f)) (triangle 0 T) ∧
      ContinuousOn (Function.uncurry (pdV (triangle 0 T) f)) (triangle 0 T) :=
    ⟨hf.continuousOn, continuousOn_pdU hf (uniqueDiffOn_triangle hT),
      continuousOn_pdV hf (uniqueDiffOn_triangle hT)⟩
  have hR := cr hS.c1_r
  have hL := cr hS.c1_lam
  have hN := cr hS.c1_nu
  have hM := cr hS.c1_m
  have hQ := cr hS.c1_Q
  have hA := cr hS.c1_A
  have hP := cc hS.c1_phi
  have hTheta := cc hS.c1_theta
  have hXi := cc hS.c1_xi
  have hScalarA := cc hS.c1_a
  have hScalarB := cc hS.c1_b
  apply continuousOn_pi.mpr
  intro i
  fin_cases i <;> dsimp only [smoothActualJet, Matrix.cons_val_zero, Matrix.cons_val_succ]
  · exact hR.1
  · exact hR.2.1
  · exact hR.2.2
  · exact hL.1
  · exact hL.2.1
  · exact hL.2.2
  · exact hN.1
  · exact hN.2.1
  · exact hN.2.2
  · exact hM.1
  · exact hM.2.1
  · exact hM.2.2
  · exact hQ.1
  · exact hQ.2.1
  · exact hQ.2.2
  · exact hA.1
  · exact hA.2.1
  · exact hA.2.2
  · exact hP.1
  · exact hP.2.1
  · exact hP.2.2
  · exact hTheta.1
  · exact hTheta.2.1
  · exact hTheta.2.2
  · exact hXi.1
  · exact hXi.2.1
  · exact hXi.2.2
  · exact hScalarA.1
  · exact hScalarA.2.1
  · exact hScalarA.2.2
  · exact hScalarB.1
  · exact hScalarB.2.1
  · exact hScalarB.2.2

end EmcsfAcExtension.Local
