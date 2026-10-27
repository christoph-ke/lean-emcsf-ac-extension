module

public import EmcsfAcExtension.Local.Defs.C1Class
public import EmcsfAcExtension.Local.Defs.C1Bound
public import EmcsfAcExtension.Local.Broad.RectangleState
import EmcsfAcExtension.Local.Broad.RectangleLipschitz
import EmcsfAcExtension.Local.Broad.ScalarAverage
import EmcsfAcExtension.Local.Calculus.C1ToSolution2

/-! # Uniform state containers for positive-radius continuation

The rectangle uses the literal incoming `(λ,θ)` and outgoing
`(r,ν,m,Q,A,φ,ξ)` blocks. A fixed margin and norm bound give source
constants chosen before the old apex or its trace. These estimates are
components of the strip construction, not an existence theorem.
-/

public section

open scoped NNReal

open Set MeasureTheory

namespace EmcsfAcExtension.Local

open Broad

/-- A fixed compact convex state container. The third linear margin is
the numerator of the Hawking gap and keeps every source denominator
away from zero throughout line segments between states. -/
@[expose] def continuationStateBox (ρ B : ℝ) : Set RectangleState :=
  Metric.closedBall 0 B ∩
    {z | ρ ≤ z.2.1 ∧ ρ ≤ z.1.1 ∧ ρ ≤ z.2.1 - 2 * z.2.2.2.1}

/-- The fixed continuation state box is compact, including when empty. -/
theorem isCompact_continuationStateBox (ρ B : ℝ) :
    IsCompact (continuationStateBox ρ B) := by
  apply (isCompact_closedBall (0 : RectangleState) B).inter_right
  have hr : IsClosed {z : RectangleState | ρ ≤ z.2.1} :=
    isClosed_le continuous_const (by fun_prop)
  have hl : IsClosed {z : RectangleState | ρ ≤ z.1.1} :=
    isClosed_le continuous_const (by fun_prop)
  have hg : IsClosed {z : RectangleState | ρ ≤ z.2.1-2*z.2.2.2.1} :=
    isClosed_le continuous_const (by fun_prop)
  exact hr.inter (hl.inter hg)

/-- Linear geometric margins and a norm ball form a convex state set. -/
theorem convex_continuationStateBox (ρ B : ℝ) :
    Convex ℝ (continuationStateBox ρ B) := by
  apply (convex_closedBall (0 : RectangleState) B).inter
  intro x hx y hy a b ha hb hab
  have hr := (convex_Ici ρ) hx.1 hy.1 ha hb hab
  have hl := (convex_Ici ρ) hx.2.1 hy.2.1 ha hb hab
  have hg := (convex_Ici ρ) hx.2.2 hy.2.2 ha hb hab
  change ρ ≤ a * x.2.1 + b * y.2.1 ∧ ρ ≤ a * x.1.1 + b * y.1.1 ∧
    ρ ≤ (a * x.2.1 + b * y.2.1) - 2 * (a * x.2.2.2.1 + b * y.2.2.2.1)
  refine ⟨hr, hl, ?_⟩
  change ρ ≤ a * (x.2.1 - 2 * x.2.2.2.1) + b * (y.2.1 - 2 * y.2.2.2.1) at hg
  convert hg using 1; ring

/-- A positive fixed margin places the whole state box in the actual
nondegenerate region of the frozen characteristic sources. -/
theorem continuationStateBox_subset_region {ρ B : ℝ} (hρ : 0 < ρ) :
    continuationStateBox ρ B ⊆ rectangle_state_region := by
  intro z hz
  exact ⟨hρ.trans_le hz.2.1, hρ.trans_le hz.2.2.1, hρ.trans_le hz.2.2.2⟩

/-- Uniform finite size and Lipschitz bounds for both literal source
blocks on the fixed continuation box. The constants depend only on
`e,ρ,B`; they precede every state, old trace and apex coordinate. -/
theorem continuation_source_bounds (e ρ B : ℝ) (hρ : 0 < ρ) :
    ∃ (H : ℝ) (L : ℝ≥0), 0 < H ∧ 0 < L ∧
      (∀ z ∈ continuationStateBox ρ B,
        ‖rectangle_in_source e z‖ ≤ H ∧ ‖rectangle_out_source e z‖ ≤ H) ∧
      LipschitzOnWith L (rectangle_in_source e) (continuationStateBox ρ B) ∧
      LipschitzOnWith L (rectangle_out_source e) (continuationStateBox ρ B) := by
  have hK := isCompact_continuationStateBox ρ B
  have hreg := continuationStateBox_subset_region (B := B) hρ
  obtain ⟨L, hL, hLi, hLo⟩ := rectangle_sources_lipschitz e hK
    (convex_continuationStateBox ρ B) hreg
  have hi : ContinuousOn (rectangle_in_source e) (continuationStateBox ρ B) :=
    fun z hz => (contDiffAt_rectangle_in_source e (hreg hz)).continuousAt.continuousWithinAt
  have ho : ContinuousOn (rectangle_out_source e) (continuationStateBox ρ B) :=
    fun z hz => (contDiffAt_rectangle_out_source e (hreg hz)).continuousAt.continuousWithinAt
  obtain ⟨Hi, hHi⟩ := hK.bddAbove_image hi.norm
  obtain ⟨Ho, hHo⟩ := hK.bddAbove_image ho.norm
  let H := max 1 (max Hi Ho)
  refine ⟨H, L, lt_of_lt_of_le zero_lt_one (le_max_left _ _), hL, ?_, hLi, hLo⟩
  intro z hz
  exact ⟨(hHi (mem_image_of_mem _ hz)).trans
      ((le_max_left Hi Ho).trans (le_max_right 1 _)),
    (hHo (mem_image_of_mem _ hz)).trans
      ((le_max_right Hi Ho).trans (le_max_right 1 _))⟩

/-- The literal sources on a fixed nondegenerate box admit globally
Lipschitz extensions, for constructing a continuous rectangle Picard
map without evaluating an inverse radius outside its permitted region.
The common coefficient depends only on `e,ρ,B` and the fixed state
dimension, before the boundary traces or old apex are chosen.
Equality on the box is exact; no extension is used as a field equation. -/
theorem continuation_sources_global_extensions (e ρ B : ℝ) (hρ : 0 < ρ) :
    ∃ (L : ℝ≥0) (fi : RectangleState → RectangleIncoming)
        (fo : RectangleState → RectangleOutgoing),
      0 < L ∧ LipschitzWith L fi ∧ LipschitzWith L fo ∧
      EqOn (rectangle_in_source e) fi (continuationStateBox ρ B) ∧
      EqOn (rectangle_out_source e) fo (continuationStateBox ρ B) := by
  obtain ⟨_H, L₀, _hH, hL₀, _hsize, hLi, hLo⟩ := continuation_source_bounds e ρ B hρ
  obtain ⟨fi, hfi, heqi⟩ := hLi.extend_finite_dimension
  obtain ⟨fo, hfo, heqo⟩ := hLo.extend_finite_dimension
  let Li := lipschitzExtensionConstant RectangleIncoming * L₀
  let Lo := lipschitzExtensionConstant RectangleOutgoing * L₀
  let L := max Li Lo
  have hLi' : 0 < Li := mul_pos (lipschitzExtensionConstant_pos RectangleIncoming) hL₀
  refine ⟨L, fi, fo, hLi'.trans_le (le_max_left _ _),
    hfi.weaken (le_max_left _ _), hfo.weaken (le_max_right _ _), heqi, heqo⟩

/-- The primary values in the full continuation bound control the
literal characteristic state in its product norm, with coefficient one.
The same `B` and its original parameter dependence are retained. -/
theorem norm_continuation_state_le {F : Fields} {D : Set (ℝ × ℝ)} {B : ℝ}
    (hbound : C1BoundOn F D B) {p : ℝ × ℝ} (hp : p ∈ D) :
    ‖rectangle_state F p‖ ≤ B := by
  obtain ⟨_hl, _hn, _hg, hr, hc⟩ := hbound p hp
  change max (max ‖F.lam p.1 p.2‖ ‖F.theta p.1 p.2‖)
    (max ‖F.r p.1 p.2‖ (max ‖F.nu p.1 p.2‖
      (max ‖F.m p.1 p.2‖ (max ‖F.Q p.1 p.2‖
        (max ‖F.A p.1 p.2‖ (max ‖F.phi p.1 p.2‖ ‖F.xi p.1 p.2‖)))))) ≤ B
  exact max_le (max_le (hr F.lam (by simp)).1 (hc F.theta (by simp)).1)
    (max_le (hr F.r (by simp)).1 (max_le (hr F.nu (by simp)).1
      (max_le (hr F.m (by simp)).1 (max_le (hr F.Q (by simp)).1
        (max_le (hr F.A (by simp)).1
          (max_le (hc F.phi (by simp)).1 (hc F.xi (by simp)).1))))))

end EmcsfAcExtension.Local
