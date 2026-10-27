module

public import EmcsfAcExtension.Global.Observation.BoundaryCharts
import Mathlib

/-! # Global isomorphisms for the literal normalized clock maps

Affine clock change and positive length scaling preserve the actual
global C¹ null isomorphisms. Source: charged_SF_new_version.tex:L1980–2034;
approved internal project record (N), (D4).
-/

public section

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
The literal affine normalized clock maps are global increasing C¹
isomorphisms with C¹ inverses and positive derivatives. Their values
agree with the displayed source expressions on all labels, so the
domain remains the actual inverse image of the original development.
There are no estimate constants or solution-class assumptions. -/
theorem normalized_clock_orderIsos {s τ₀ : ℝ} (hs : 0 < s) (U V : ℝ ≃o ℝ)
    (hU : ContDiff ℝ 1 (U : ℝ → ℝ)) (hV : ContDiff ℝ 1 (V : ℝ → ℝ))
    (hUp : ∀ x, 0 < deriv (U : ℝ → ℝ) x) (hVp : ∀ x, 0 < deriv (V : ℝ → ℝ) x) :
    ∃ F G : ℝ ≃o ℝ,
      (∀ t, F t = U (τ₀ + s * t / 2) / s) ∧
      (∀ t, G t = V (τ₀ + s * t / 2) / s) ∧
      ContDiff ℝ 1 (F : ℝ → ℝ) ∧ ContDiff ℝ 1 (G : ℝ → ℝ) ∧
      ContDiff ℝ 1 (F.symm : ℝ → ℝ) ∧ ContDiff ℝ 1 (G.symm : ℝ → ℝ) ∧
      (∀ t, 0 < deriv (F : ℝ → ℝ) t) ∧ (∀ t, 0 < deriv (G : ℝ → ℝ) t) := by
  let affine := ((OrderIso.mulLeft₀ s hs).trans
    (OrderIso.divRight₀ (2 : ℝ) (by norm_num))).trans (OrderIso.addLeft τ₀)
  let F := (affine.trans U).trans (OrderIso.divRight₀ s hs)
  let G := (affine.trans V).trans (OrderIso.divRight₀ s hs)
  have ca : ContDiff ℝ 1 (affine : ℝ → ℝ) := by
    change ContDiff ℝ 1 (fun t : ℝ => τ₀ + s * t / 2)
    fun_prop
  have cF : ContDiff ℝ 1 (F : ℝ → ℝ) := (hU.comp ca).div_const s
  have cG : ContDiff ℝ 1 (G : ℝ → ℝ) := (hV.comp ca).div_const s
  have da (t : ℝ) : HasDerivAt (affine : ℝ → ℝ) (s / 2) t := by
    simpa only [affine, OrderIso.trans_apply, OrderIso.mulLeft₀_apply,
      OrderIso.divRight₀_apply, OrderIso.addLeft_apply, id_eq, mul_one,
      zero_mul, zero_add] using!
      (((hasDerivAt_id t).const_mul s).div_const 2).const_add τ₀
  have dF (t : ℝ) : HasDerivAt (F : ℝ → ℝ) (deriv (U : ℝ → ℝ) (affine t) / 2) t := by
    convert (((hU.differentiable (by norm_num) (affine t)).hasDerivAt.comp t (da t)).div_const s)
      using 1
    · rfl
    · field_simp
  have dG (t : ℝ) : HasDerivAt (G : ℝ → ℝ) (deriv (V : ℝ → ℝ) (affine t) / 2) t := by
    convert (((hV.differentiable (by norm_num) (affine t)).hasDerivAt.comp t (da t)).div_const s)
      using 1
    · rfl
    · field_simp
  have pF (t : ℝ) : 0 < deriv (F : ℝ → ℝ) t := by
    rw [(dF t).deriv]
    exact half_pos (hUp _)
  have pG (t : ℝ) : 0 < deriv (G : ℝ → ℝ) t := by
    rw [(dG t).deriv]
    exact half_pos (hVp _)
  refine ⟨F, G, fun _ => rfl, fun _ => rfl, cF, cG, ?_, ?_, pF, pG⟩
  · exact F.toHomeomorph.contDiff_symm_deriv (fun t => (pF t).ne')
      (fun t => (cF.differentiable (by norm_num) t).hasDerivAt) cF
  · exact G.toHomeomorph.contDiff_symm_deriv (fun t => (pG t).ne')
      (fun t => (cG.differentiable (by norm_num) t).hasDerivAt) cG

end EmcsfAcExtension.Global.Observation
