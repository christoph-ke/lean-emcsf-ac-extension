module

public import EmcsfAcExtension.Global.Observation.BoundaryCharts
import EmcsfAcExtension.Global.Observation.Gauge

/-! # Values and Jacobians of the actual affine clock chart

The normalizing factors are computed at the two actual cylinder endpoints,
not imposed as independent optical assumptions.
Source: charged_SF_new_version.tex:L1980–2034, L2145–2152.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
The actual affine clock pullback has the exact physical values and optical
normalizers at every pair of clock labels. Both chart derivatives are
computed from the constructed C¹ maps. The scalar ratios are unchanged
by positive null Jacobians; the residual gauge is retained explicitly.
There are no estimate constants. -/
theorem clock_chart_components
    {e ui b a z s τ₀ u v : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui))
    (γ : ClockCylinder S (origDomain ui) b a z) (hs : 0 < s)
    (χ : ℝ → ℝ) (U V : ℝ ≃o ℝ)
    (hu : τ₀ + s * u / 2 ∈ Icc a z) (hv : τ₀ + s * v / 2 ∈ Icc a z)
    (heq : ∀ τ ∈ Icc a z, U τ = γ.U τ ∧ V τ = γ.V τ)
    (hUd : ∀ τ ∈ Icc a z, HasDerivAt (U : ℝ → ℝ)
      ((-S.nu (U τ) (V τ))⁻¹) τ)
    (hVd : ∀ τ ∈ Icc a z, HasDerivAt (V : ℝ → ℝ)
      ((S.lam (U τ) (V τ))⁻¹) τ) :
    let f := fun t => τ₀ + s * t / 2
    let F := fun t => U (f t) / s
    let G := fun t => V (f t) / s
    let B := gaugeFields e S χ
    let P := nullPullback (rescaleFields B s) F G
    let x := γ.U (f u)
    let y := γ.V (f v)
    P.r u v = S.r x y / s ∧ P.m u v = S.m x y / s ∧
      P.Q u v = S.Q x y / s ∧ P.mu u v = S.mu x y ∧
      P.nu u v = (2 * (-S.nu x (γ.V (f u))))⁻¹ * S.nu x y ∧
      P.lam u v = (2 * S.lam (γ.U (f v)) y)⁻¹ * S.lam x y ∧
      P.phi u v = B.phi x y ∧
      P.theta u v / P.lam u v = B.theta x y / B.lam x y ∧
      P.xi u v / P.nu u v = B.xi x y / B.nu x y ∧
      P.a u v = B.a x y := by
  let f := fun t : ℝ => τ₀ + s * t / 2
  let F := fun t => U (f t) / s
  let G := fun t => V (f t) / s
  have df (t : ℝ) : HasDerivAt f (s / 2) t := by
    simpa only [f, id_eq, mul_one, zero_mul, zero_add] using!
      (((hasDerivAt_id t).const_mul s).div_const 2).const_add τ₀
  have hUu : U (f u) = γ.U (f u) := (heq _ hu).1
  have hVu : V (f u) = γ.V (f u) := (heq _ hu).2
  have hUv : U (f v) = γ.U (f v) := (heq _ hv).1
  have hVv : V (f v) = γ.V (f v) := (heq _ hv).2
  have hdU : HasDerivAt (U : ℝ → ℝ) ((-S.nu (U (f u)) (V (f u)))⁻¹) (f u) := hUd _ hu
  have hdV : HasDerivAt (V : ℝ → ℝ) ((S.lam (U (f v)) (V (f v)))⁻¹) (f v) := hVd _ hv
  have dF : HasDerivAt F ((-S.nu (U (f u)) (V (f u)))⁻¹ / 2) u := by
    convert ((hdU.comp u (df u)).div_const s) using 1
    · rfl
    · field_simp
  have dG : HasDerivAt G ((S.lam (U (f v)) (V (f v)))⁻¹ / 2) v := by
    convert ((hdV.comp v (df v)).div_const s) using 1
    · rfl
    · field_simp
  have hn : S.nu (U (f u)) (V (f u)) ≠ 0 := by
    rw [hUu, hVu]
    exact (hS.nu_neg _ (γ.mem _ hu)).ne
  have hl : S.lam (U (f v)) (V (f v)) ≠ 0 := by
    rw [hUv, hVv]
    exact (hS.lam_pos _ (γ.mem _ hv)).ne'
  have hrat := nullPullback_ratios (rescaleFields (gaugeFields e S χ) s) F G dF dG
    (div_ne_zero (inv_ne_zero (neg_ne_zero.mpr hn)) (by norm_num))
    (div_ne_zero (inv_ne_zero hl) (by norm_num))
  have hvalU (t : ℝ) : s * F t = U (f t) := by dsimp only [F]; field_simp
  have hvalV (t : ℝ) : s * G t = V (f t) := by dsimp only [G]; field_simp
  have hrat' :
      (nullPullback (rescaleFields (gaugeFields e S χ) s) F G).theta u v /
          (nullPullback (rescaleFields (gaugeFields e S χ) s) F G).lam u v =
        (gaugeFields e S χ).theta (γ.U (f u)) (γ.V (f v)) /
          (gaugeFields e S χ).lam (γ.U (f u)) (γ.V (f v)) ∧
      (nullPullback (rescaleFields (gaugeFields e S χ) s) F G).xi u v /
          (nullPullback (rescaleFields (gaugeFields e S χ) s) F G).nu u v =
        (gaugeFields e S χ).xi (γ.U (f u)) (γ.V (f v)) /
          (gaugeFields e S χ).nu (γ.U (f u)) (γ.V (f v)) := by
    simpa only [rescaleFields, hvalU, hvalV, hUu, hVv] using! hrat
  let B := gaugeFields e S χ
  let P := nullPullback (rescaleFields B s) F G
  change P.r u v = S.r (γ.U (f u)) (γ.V (f v)) / s ∧
    P.m u v = S.m (γ.U (f u)) (γ.V (f v)) / s ∧
    P.Q u v = S.Q (γ.U (f u)) (γ.V (f v)) / s ∧
    P.mu u v = S.mu (γ.U (f u)) (γ.V (f v)) ∧
    P.nu u v = (2 * (-S.nu (γ.U (f u)) (γ.V (f u))))⁻¹ * S.nu (γ.U (f u)) (γ.V (f v)) ∧
    P.lam u v = (2 * S.lam (γ.U (f v)) (γ.V (f v)))⁻¹ * S.lam (γ.U (f u)) (γ.V (f v)) ∧
    P.phi u v = B.phi (γ.U (f u)) (γ.V (f v)) ∧
    P.theta u v / P.lam u v = B.theta (γ.U (f u)) (γ.V (f v)) / B.lam (γ.U (f u)) (γ.V (f v)) ∧
    P.xi u v / P.nu u v = B.xi (γ.U (f u)) (γ.V (f v)) / B.nu (γ.U (f u)) (γ.V (f v)) ∧
    P.a u v = B.a (γ.U (f u)) (γ.V (f v))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hrat'.1, hrat'.2, ?_⟩
  · simp only [P, B, nullPullback, rescaleFields, gaugeFields, hvalU, hvalV,
      hUu, hVv]
  · simp only [P, B, nullPullback, rescaleFields, gaugeFields, hvalU, hvalV,
      hUu, hVv]
  · simp only [P, B, nullPullback, rescaleFields, gaugeFields, hvalU, hvalV,
      hUu, hVv]
  · dsimp only [Fields.mu, P, B, nullPullback, rescaleFields, gaugeFields]
    rw [hvalU, hvalV, hUu, hVv]
    field_simp
  · simp only [P, B, nullPullback, rescaleFields, gaugeFields, dF.deriv,
      hvalU, hvalV, hUu, hVu, hVv]
    ring
  · simp only [P, B, nullPullback, rescaleFields, gaugeFields, dG.deriv,
      hvalU, hvalV, hUu, hUv, hVv]
    ring
  · simp only [P, B, nullPullback, rescaleFields, hvalU, hvalV, hUu, hVv]
  · unfold Fields.a
    rw [hrat'.1]
    congr 1
    simp only [P, B, nullPullback, rescaleFields, hvalU, hvalV, hUu, hVv]

end EmcsfAcExtension.Global.Observation
