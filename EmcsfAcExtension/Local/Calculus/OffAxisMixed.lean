module

public import EmcsfAcExtension.Local.Calculus.MixedTriangle
public import EmcsfAcExtension.Local.Defs.C1Class
import EmcsfAcExtension.Infra.Calculus.PartialsC1
import EmcsfAcExtension.Infra.Calculus.Glue

/-! # Mixed derivatives with a C¹ transport source

Sources are C¹ only on the off-axis portion of the closed triangle. Their canonical
partials are continuous there and supply the differentiated source in the integral
mixed-derivative theorem. No global second derivative is used.
-/

public section

open Set Filter
open scoped Topology

namespace EmcsfAcExtension.Local

/-- The off-axis portion of a positive-time triangle has unique domain derivatives,
including its initial and terminal edges. -/
theorem uniqueDiffOn_off_triangle_aux {T : ℝ} (hT : 0 < T) :
    UniqueDiffOn ℝ {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ T} := by
  apply uniqueDiffOn_relative_patch (uniqueDiffOn_triangle hT)
    (fun p hp => ⟨hp.1, hp.2.1.le, hp.2.2⟩)
  intro p hp
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds ((isOpen_lt continuous_fst continuous_snd).mem_nhds hp.2.1)]
    with q hq hlt
  exact ⟨hq.1, hlt, hq.2.2⟩

/-- Extract a source's outgoing partial as a derivative on the complete triangle
section. The source need only be C¹ off the axis: locality discards the axis endpoint. -/
theorem hasDerivWithinAt_off_triangle_v_aux {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {T u v : ℝ} {G : ℝ → ℝ → E}
    (hG : ContDiffOn ℝ 1 (Function.uncurry G)
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ T})
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    HasDerivWithinAt (G u)
      (pdV {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ T} G u v) (Icc u T) v := by
  have h := hasDerivWithinAt_section_v hG ⟨hu, huv, hvT⟩
    (s := Ioc u T) (fun s hs => ⟨hu, hs.1, hs.2⟩)
  apply h.mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds huv)] with s hs hus
  exact ⟨hus, hs.2⟩

/-- Extract a source's incoming partial on the complete incoming triangle section.
Only C¹ regularity off the axis is used. -/
theorem hasDerivWithinAt_off_triangle_u_aux {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {T u v : ℝ} {G : ℝ → ℝ → E}
    (hG : ContDiffOn ℝ 1 (Function.uncurry G)
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ T})
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    HasDerivWithinAt (fun x => G x v)
      (pdU {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ T} G u v) (Icc 0 v) u := by
  have h := hasDerivWithinAt_section_u hG ⟨hu, huv, hvT⟩
    (s := Ico 0 v) (fun s hs => ⟨hs.1, hs.2, hvT⟩)
  apply h.mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds huv)] with s hs hsv
  exact ⟨hs.1, hsv⟩

/-- Incoming mixed derivative recovered by integration when the incoming transport
source is C¹ off the axis. The output is the source's canonical outgoing partial. -/
theorem mixed_u_pdV_triangle_of_c1_transport_aux {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {T : ℝ} {f G : ℝ → ℝ → E}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle 0 T))
    (hG : ContDiffOn ℝ 1 (Function.uncurry G)
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ T})
    (heq : ∀ x y, 0 ≤ x → x < y → y ≤ T → pdU (triangle 0 T) f x y = G x y)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    HasDerivWithinAt (fun x => pdV (triangle 0 T) f x v)
      (pdV {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ T} G u v) (Icc 0 v) u :=
  mixed_u_pdV_triangle_of_transport_aux (f := f) (G := G)
    (Gv := pdV {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ T} G) hf hG.continuousOn
    (continuousOn_partial_v hG (uniqueDiffOn_off_triangle_aux
      (hu.trans_lt (huv.trans_le hvT)))) heq
    (fun _ _ hx hxy hy => hasDerivWithinAt_off_triangle_v_aux hG hx hxy hy) hu huv hvT

/-- Outgoing mixed derivative recovered by integration when the outgoing transport
source is C¹ off the axis. The output is the source's canonical incoming partial. -/
theorem mixed_v_pdU_triangle_of_c1_transport_aux {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {T : ℝ} {f G : ℝ → ℝ → E}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle 0 T))
    (hG : ContDiffOn ℝ 1 (Function.uncurry G)
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ T})
    (heq : ∀ x y, 0 ≤ x → x < y → y ≤ T → pdV (triangle 0 T) f x y = G x y)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    HasDerivWithinAt (fun y => pdU (triangle 0 T) f u y)
      (pdU {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ T} G u v) (Icc u T) v :=
  mixed_v_pdU_triangle_of_transport_aux (f := f) (G := G)
    (Gu := pdU {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ T} G) hf hG.continuousOn
    (continuousOn_partial_u hG (uniqueDiffOn_off_triangle_aux
      (hu.trans_lt (huv.trans_le hvT)))) heq
    (fun _ _ hx hxy hy => hasDerivWithinAt_off_triangle_u_aux hG hx hxy hy) hu huv hvT

end EmcsfAcExtension.Local
