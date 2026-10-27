module

public import EmcsfAcExtension.Global.Observation.SourceEquations
import EmcsfAcExtension.Local.Api.Mono
import EmcsfAcExtension.Local.Calculus.Sections
import Mathlib

/-! # Joint radius regularity on proper source charts

Joint C¹ regularity comes from the frozen radius integral equations on a
proper triangle. The source chart is only a coordinate pullback; it is
not asserted to belong to the axis-normalized solution class.
Source: charged_SF_new_version.tex:L2782–2783; internal project record AC justification, item 1.
-/

public section

open Set Filter Topology

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
The original radius is jointly C¹ at each strict original interior point.
The enclosing proper triangle and both label margins are constructed
internally from that point. There are no quantitative constants. -/
theorem original_radius_contDiffAt {e ui u v : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (hi : ui < u) (huv : u < v) (hv : v < 0) :
    ContDiffAt ℝ 1 (Function.uncurry S.r) (u, v) := by
  let a := (ui + u) / 2
  let b := v / 2
  have hau : a < u := by dsimp only [a]; linarith only [hi]
  have hia : ui ≤ a := by dsimp only [a]; linarith only [hi]
  have hvb : v < b := by dsimp only [b]; linarith only [hv]
  have hb : b < 0 := by dsimp only [b]; linarith only [hv]
  have hab : a < b := hau.trans (huv.trans hvb)
  have hSt := Local.isSolution_mono hS (triangle_subset_origDomain hia hb)
  exact (Local.IsSolution.contDiffOn_r hSt hab).contDiffAt
    (mem_interior_iff_mem_nhds.mp (mem_interior_triangle_of_lt hau huv hvb))

private theorem full_derivative_of_partials {F : ℝ → ℝ → ℝ} {u v nu lam : ℝ}
    (hc : ContDiffAt ℝ 1 (Function.uncurry F) (u, v))
    (hnu : HasDerivAt (fun x => F x v) nu u)
    (hlam : HasDerivAt (F u) lam v) :
    HasFDerivAt (Function.uncurry F)
      (nu • ContinuousLinearMap.fst ℝ ℝ ℝ + lam • ContinuousLinearMap.snd ℝ ℝ ℝ) (u, v) := by
  let A := fderiv ℝ (Function.uncurry F) (u, v)
  have hF : HasFDerivAt (Function.uncurry F) A (u, v) :=
    (hc.differentiableAt (by norm_num)).hasFDerivAt
  have hU := hF.comp_hasDerivAt u ((hasDerivAt_id u).prodMk (hasDerivAt_const u v))
  have hV := hF.comp_hasDerivAt v ((hasDerivAt_const v u).prodMk (hasDerivAt_id v))
  change HasDerivAt (fun x => F x v) (A (1, 0)) u at hU
  change HasDerivAt (F u) (A (0, 1)) v at hV
  have hAu := hU.unique hnu
  have hAv := hV.unique hlam
  have hA : A = nu • ContinuousLinearMap.fst ℝ ℝ ℝ +
      lam • ContinuousLinearMap.snd ℝ ℝ ℝ := by
    apply DFunLike.ext
    rintro ⟨x, y⟩
    have hxy : (x, y) = x • ((1 : ℝ), 0) + y • ((0 : ℝ), 1) := by ext <;> simp
    have hh := congrArg A hxy
    rw [map_add, map_smul, map_smul, hAu, hAv] at hh
    simpa only [add_apply, smul_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', smul_eq_mul, mul_comm] using hh
  exact hA ▸ hF

/-- [internal]
At a strict original image point the actual normalized radius is jointly
C¹ with its two literal chart expansions as full derivative coefficients.
Only C¹ labels and a positive length scale are used; the gauge has no
effect on the radius and no chart solution assertion occurs. No constants
or optical comparison estimates enter this regularity result. -/
theorem chart_radius_contDiffAt_and_hasFDerivAt
    {e ui s u v : ℝ} {S : Fields} (hS : IsSolution e S (origDomain ui))
    (hs : 0 < s) (χ : ℝ → ℝ) (U V : ℝ → ℝ)
    (hU : ContDiff ℝ 1 U) (hV : ContDiff ℝ 1 V)
    (hi : ui < s * U u) (huv : s * U u < s * V v) (hv : s * V v < 0) :
    let P := nullPullback (rescaleFields (gaugeFields e S χ) s) U V
    ContDiffAt ℝ 1 (Function.uncurry P.r) (u, v) ∧
      HasFDerivAt (Function.uncurry P.r)
        (P.nu u v • ContinuousLinearMap.fst ℝ ℝ ℝ +
          P.lam u v • ContinuousLinearMap.snd ℝ ℝ ℝ) (u, v) := by
  let P := nullPullback (rescaleFields (gaugeFields e S χ) s) U V
  have hc := original_radius_contDiffAt hS hi huv hv
  have hmap : ContDiff ℝ 1 (fun p : ℝ × ℝ => (s * U p.1, s * V p.2)) :=
    (contDiff_const.mul (hU.comp contDiff_fst)).prodMk
      (contDiff_const.mul (hV.comp contDiff_snd))
  have hpc : ContDiffAt ℝ 1 (Function.uncurry P.r) (u, v) := by
    change ContDiffAt ℝ 1 (fun p : ℝ × ℝ => S.r (s * U p.1) (s * V p.2) / s) (u, v)
    exact (hc.comp (u, v) hmap.contDiffAt).div_const s
  have hd := original_characteristic_equations hS hi huv hv
  have hdU := (hU.differentiable (by norm_num) u).hasDerivAt.const_mul s
  have hdV := (hV.differentiable (by norm_num) v).hasDerivAt.const_mul s
  have hnu : HasDerivAt (fun x => P.r x v) (P.nu u v) u := by
    convert (hd.2.1.comp u hdU).div_const s using 1 <;>
      dsimp [P, nullPullback, rescaleFields, gaugeFields]
    field_simp [hs.ne']
  have hlam : HasDerivAt (P.r u) (P.lam u v) v := by
    convert (hd.1.1.comp v hdV).div_const s using 1 <;>
      dsimp [P, nullPullback, rescaleFields, gaugeFields]
    field_simp [hs.ne']
  exact ⟨hpc, full_derivative_of_partials hpc hnu hlam⟩

end EmcsfAcExtension.Global.Observation
