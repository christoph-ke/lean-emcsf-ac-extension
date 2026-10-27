module

public import EmcsfAcExtension.Local.Defs.C1Class
public import EmcsfAcExtension.Local.Defs.C1Bound
public import EmcsfAcExtension.Local.Broad.RectangleState
import Mathlib.Analysis.Normed.Operator.Prod

/-! # Product-norm first-jet bounds

The characteristic state uses maximum product norms. The complete
continuation bound controls its full derivative with coefficient one.
Conversely two directional jet bounds control that derivative with the
explicit factor two of the maximum norm on the null-label plane.
-/

public section

open Set

namespace EmcsfAcExtension.Local

open Broad

/-- The frozen primary continuation bound controls the full derivative
of the finite characteristic state. The same `B` is retained, with no
new constant depending on the domain or field. -/
theorem norm_fderiv_continuation_state_le {e B : ℝ} {F : Fields}
    {D : Set (ℝ × ℝ)} (hF : IsC1Solution e F D) (hU : UniqueDiffOn ℝ D)
    (hbound : C1BoundOn F D B) {p : ℝ × ℝ} (hp : p ∈ D) :
    ‖fderivWithin ℝ (rectangle_state F) D p‖ ≤ B := by
  obtain ⟨_, _, _, hr, hc⟩ := hbound p hp
  have dr := (hF.c1_r.differentiableOn (by norm_num) p hp).hasFDerivWithinAt
  have dl := (hF.c1_lam.differentiableOn (by norm_num) p hp).hasFDerivWithinAt
  have dn := (hF.c1_nu.differentiableOn (by norm_num) p hp).hasFDerivWithinAt
  have dm := (hF.c1_m.differentiableOn (by norm_num) p hp).hasFDerivWithinAt
  have dq := (hF.c1_Q.differentiableOn (by norm_num) p hp).hasFDerivWithinAt
  have da := (hF.c1_A.differentiableOn (by norm_num) p hp).hasFDerivWithinAt
  have dp := (hF.c1_phi.differentiableOn (by norm_num) p hp).hasFDerivWithinAt
  have dt := (hF.c1_theta.differentiableOn (by norm_num) p hp).hasFDerivWithinAt
  have dx := (hF.c1_xi.differentiableOn (by norm_num) p hp).hasFDerivWithinAt
  have hfull := (dl.prodMk dt).prodMk
    (dr.prodMk (dn.prodMk (dm.prodMk (dq.prodMk (da.prodMk (dp.prodMk dx))))))
  have hfull' := hfull.fderivWithin (hU p hp)
  simp only [Function.uncurry_def] at hfull'
  unfold rectangle_state
  rw [hfull']
  simp only [ContinuousLinearMap.opNorm_prod, Prod.norm_def]
  exact max_le (max_le (hr F.lam (by simp)).2 (hc F.theta (by simp)).2)
    (max_le (hr F.r (by simp)).2 (max_le (hr F.nu (by simp)).2
      (max_le (hr F.m (by simp)).2 (max_le (hr F.Q (by simp)).2
        (max_le (hr F.A (by simp)).2
          (max_le (hc F.phi (by simp)).2 (hc F.xi (by simp)).2))))))

/-- Two null-direction first-jet bounds control the full derivative in
the maximum norm on the label plane. The explicit coefficient two is
independent of the target normed space and configuration. -/
theorem norm_clm_le_two_mul_of_basis_bounds {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : (ℝ × ℝ) →L[ℝ] E) {C : ℝ} (hC : 0 ≤ C)
    (hu : ‖L (1, 0)‖ ≤ C) (hv : ‖L (0, 1)‖ ≤ C) : ‖L‖ ≤ 2*C := by
  apply ContinuousLinearMap.opNorm_le_bound L (by positivity)
  intro p
  have heq : p = p.1 • ((1,0) : ℝ × ℝ) + p.2 • ((0,1) : ℝ × ℝ) := by
    ext <;> simp
  calc ‖L p‖ = ‖p.1 • L (1,0) + p.2 • L (0,1)‖ := by
         conv_lhs => rw [heq, map_add, map_smul, map_smul]
       _ ≤ ‖p.1‖*‖L (1,0)‖ + ‖p.2‖*‖L (0,1)‖ := by
         simpa only [norm_smul] using norm_add_le (p.1 • L (1,0)) (p.2 • L (0,1))
       _ ≤ ‖p.1‖*C + ‖p.2‖*C := add_le_add
         (mul_le_mul_of_nonneg_left hu (norm_nonneg _))
         (mul_le_mul_of_nonneg_left hv (norm_nonneg _))
       _ ≤ ‖p‖*C + ‖p‖*C := add_le_add
         (mul_le_mul_of_nonneg_right (norm_fst_le p) hC)
         (mul_le_mul_of_nonneg_right (norm_snd_le p) hC)
       _ = (2*C)*‖p‖ := by ring

end EmcsfAcExtension.Local
