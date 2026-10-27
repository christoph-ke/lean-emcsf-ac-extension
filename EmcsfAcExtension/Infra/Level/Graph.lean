module

public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.ProjIcc
public import EmcsfAcExtension.Infra.AC.Intervals
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Radius level graphs on compact rectangles

The intermediate value construction needs only continuity and strict sectional
monotonicity. Boundary bracketing is explicit: a compact region by itself need
not contain a point of every requested level. C¹ regularity is obtained locally
from Mathlib's implicit function theorem and uniqueness of each sectional root.
All functions are abstract; no field equations or continuation theorem occur.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace EmcsfAcExtension.Global.Level

/-- [internal] The local C¹ implicit level curve, with its exact speed. The
partial derivatives are `nu` and `lam`; only the second must be nonzero. -/
theorem exists_contDiff_levelGraph_local {r : ℝ → ℝ → ℝ} {u v nu lam : ℝ}
    (hr : ContDiffAt ℝ 1 (Function.uncurry r) (u, v))
    (hd : HasFDerivAt (Function.uncurry r)
      (nu • ContinuousLinearMap.fst ℝ ℝ ℝ + lam • ContinuousLinearMap.snd ℝ ℝ ℝ) (u, v))
    (hlam : lam ≠ 0) :
    ∃ g : ℝ → ℝ, g u = v ∧ ContDiffAt ℝ 1 g u ∧ HasDerivAt g (-nu / lam) u ∧
      (∀ᶠ p : ℝ × ℝ in 𝓝 (u, v), r p.1 p.2 = r u v ↔ g p.1 = p.2) := by
  have h₂ : fderiv ℝ (Function.uncurry r) (u, v) ∘L
      ContinuousLinearMap.inr ℝ ℝ ℝ = lam • ContinuousLinearMap.id ℝ ℝ := by
    rw [hd.fderiv]
    ext
    simp
  have hi : (lam • ContinuousLinearMap.id ℝ ℝ).IsInvertible := by
    apply ContinuousLinearMap.IsInvertible.of_inverse
      (g := lam⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    · ext
      simp [hlam]
    · ext
      simp [hlam]
  have hinv : (lam • ContinuousLinearMap.id ℝ ℝ).inverse =
      lam⁻¹ • ContinuousLinearMap.id ℝ ℝ := by
    apply ContinuousLinearMap.inverse_eq
    · ext
      simp [hlam]
    · ext
      simp [hlam]
  have hp : (1 : ℕ∞ω) ≠ 0 := by simp
  let g := hr.implicitFunction hp (h₂ ▸ hi)
  refine ⟨g, hr.implicitFunction_apply_self hp _, hr.contDiffAt_implicitFunction hp _, ?_,
    hr.eventually_apply_eq_iff_implicitFunction hp _⟩
  have h := (hr.hasStrictFDerivAt_implicitFunction hp (h₂ ▸ hi)).hasFDerivAt.hasDerivAt
  simpa [g, h₂, hinv, hd.fderiv, ContinuousLinearMap.comp_apply, div_eq_mul_inv,
    mul_comm] using h

/-- [internal] The local level curve continues inside any open region containing
its base point when the outgoing derivative is nonzero. This is parametrization
of an existing radius, with no PDE continuation assumption. -/
theorem exists_levelGraph_in_open {r : ℝ → ℝ → ℝ} {D : Set (ℝ × ℝ)} {u v nu lam : ℝ}
    (hD : IsOpen D) (hmem : (u, v) ∈ D)
    (hr : ContDiffAt ℝ 1 (Function.uncurry r) (u, v))
    (hd : HasFDerivAt (Function.uncurry r)
      (nu • ContinuousLinearMap.fst ℝ ℝ ℝ + lam • ContinuousLinearMap.snd ℝ ℝ ℝ) (u, v))
    (hlam : lam ≠ 0) :
    ∃ g : ℝ → ℝ, g u = v ∧ ContDiffAt ℝ 1 g u ∧ HasDerivAt g (-nu / lam) u ∧
      (∀ᶠ x in 𝓝 u, (x, g x) ∈ D ∧ r x (g x) = r u v) := by
  obtain ⟨g, hg₀, hgc, hgd, heq⟩ := exists_contDiff_levelGraph_local hr hd hlam
  have hlim : Tendsto (fun x => (x, g x)) (𝓝 u) (𝓝 (u, v)) := by
    simpa only [hg₀, id_eq] using (continuousAt_id.prodMk hgc.continuousAt).tendsto
  refine ⟨g, hg₀, hgc, hgd, ?_⟩
  filter_upwards [hlim.eventually (hD.mem_nhds hmem), hlim.eventually heq] with x hx hi
  exact ⟨hx, hi.mpr rfl⟩

/-- [internal] The implicit C¹ curve and its speed agree with any continuous
existing level graph, using relative neighborhoods at boundary rows. -/
theorem contDiffWithinAt_levelGraph_of_continuousWithin
    {r : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {s : Set ℝ} {u nu lam : ℝ}
    (hr : ContDiffAt ℝ 1 (Function.uncurry r) (u, g u))
    (hd : HasFDerivAt (Function.uncurry r)
      (nu • ContinuousLinearMap.fst ℝ ℝ ℝ + lam • ContinuousLinearMap.snd ℝ ℝ ℝ) (u, g u))
    (hlam : lam ≠ 0) (hg : ContinuousWithinAt g s u)
    (he : ∀ᶠ x in 𝓝[s] u, r x (g x) = r u (g u)) :
    ContDiffWithinAt ℝ 1 g s u ∧ HasDerivWithinAt g (-nu / lam) s u := by
  obtain ⟨ψ, hψ₀, hψc, hψd, heq⟩ := exists_contDiff_levelGraph_local hr hd hlam
  have hi := (continuousWithinAt_id.prodMk hg).eventually heq
  have hsame : g =ᶠ[𝓝[s] u] ψ := by
    filter_upwards [hi, he] with x hx hroot
    exact (hx.mp hroot).symm
  exact ⟨hψc.contDiffWithinAt.congr_of_eventuallyEq hsame hψ₀.symm,
    hψd.hasDerivWithinAt.congr_of_eventuallyEq hsame hψ₀.symm⟩

/-- [internal] Relative implicit differentiation for an existing continuous
level graph. The radius derivative is required only within the existing region,
so this includes closed physical boundaries without an ambient extension. -/
theorem hasDerivWithinAt_levelGraph_of_fderivWithin
    {r : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {s : Set ℝ} {D : Set (ℝ × ℝ)} {u nu lam : ℝ}
    (hu : u ∈ s) (hg : ContinuousWithinAt g s u)
    (hmap : ∀ x ∈ s, (x, g x) ∈ D)
    (hlevel : ∀ x ∈ s, r x (g x) = r u (g u))
    (hd : HasFDerivWithinAt (Function.uncurry r)
      (nu • ContinuousLinearMap.fst ℝ ℝ ℝ + lam • ContinuousLinearMap.snd ℝ ℝ ℝ)
      D (u, g u)) (hlam : lam ≠ 0) :
    HasDerivWithinAt g (-nu / lam) s u := by
  let A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (nu • ContinuousLinearMap.fst ℝ ℝ ℝ + lam • ContinuousLinearMap.snd ℝ ℝ ℝ)
  let B : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (lam⁻¹ • (ContinuousLinearMap.snd ℝ ℝ ℝ - nu • ContinuousLinearMap.fst ℝ ℝ ℝ))
  have hBA : Function.LeftInverse B A := by
    intro p
    apply Prod.ext
    · simp [A, B]
    · simp [A, B, ← mul_assoc, inv_mul_cancel₀ hlam]
  have hF : HasFDerivWithinAt (fun p : ℝ × ℝ => (p.1, r p.1 p.2)) A D (u, g u) :=
    hasFDerivAt_fst.hasFDerivWithinAt.prodMk hd
  have hH : HasFDerivWithinAt (fun x : ℝ => (x, r u (g u)))
      ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ)) s u :=
    (hasFDerivWithinAt_id u s).prodMk (hasFDerivWithinAt_const (r u (g u)) u s)
  have hlim : Tendsto (fun x => (x, g x)) (𝓝[s] u) (𝓝[D] (u, g u)) :=
    by simpa only [id_eq] using (continuousWithinAt_id.prodMk hg).tendsto_nhdsWithin hmap
  have he : (fun p : ℝ × ℝ => (p.1, r p.1 p.2)) ∘ (fun x => (x, g x))
      =ᶠ[𝓝[s] u] (fun x => (x, r u (g u))) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact Prod.ext rfl (hlevel x hx)
  have h := HasFDerivWithinAt.of_comp_of_leftInverse hlim hF hH he hBA hu
  simpa [B, ContinuousLinearMap.comp_apply, div_eq_mul_inv, mul_comm] using
    h.snd.hasDerivWithinAt

end EmcsfAcExtension.Global.Level
