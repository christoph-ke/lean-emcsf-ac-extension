module

public import EmcsfAcExtension.Local.Construction.FullSystemDomain
public import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Infra.Calculus.WithinIntegral
import EmcsfAcExtension.Local.Calculus.MixedIdentity
import EmcsfAcExtension.Local.Construction.ReconBasic

/-! # Mixed derivatives recovered from first-order primitives

internal project record (21): a C¹ outgoing source supplies the outgoing derivative of
the incoming partial of its primitive. The primitive itself is only C¹.
The parameter interval includes both incoming sides of the closed wedge.
-/

public section

open Set MeasureTheory Filter
open scoped Topology

namespace EmcsfAcExtension.Local.Null

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Differentiate the actual incoming partial of an outgoing primitive.
The primitive and its outgoing source are C¹ on the wedge; no second
primary-field derivative is a premise. The incoming coordinate may be on
either incoming boundary. The outgoing point is strictly off the axis
and below the upper edge, exactly where an ordinary derivative is used
in the defect ODE. -/
theorem hasDerivAt_pdU_of_pdV_on_wedge {a b c u v : ℝ}
    {f g : ℝ → ℝ → E} (hac : a < c) (hcb : c ≤ b)
    (cf : ContDiffOn ℝ 1 (Function.uncurry f)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cg : ContDiffOn ℝ 1 (Function.uncurry g)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hfg : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      pdV (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) f p.1 p.2 = g p.1 p.2)
    (hu : u ∈ Icc a c) (huv : u < v) (hvb : v < b) :
    HasDerivAt (pdU (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) f u)
      (pdU (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) g u v) v := by
  let D := triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}
  let v₀ := (u + v) / 2
  have huv₀ : u < v₀ := by dsimp [v₀]; linarith
  have hv₀v : v₀ < v := by dsimp [v₀]; linarith
  have ha : a < min c v₀ := lt_min hac (hu.1.trans_lt huv₀)
  have huA : u ∈ Icc a (min c v₀) := ⟨hu.1, le_min hu.2 huv₀.le⟩
  have hb : v₀ ≤ b := hv₀v.le.trans hvb.le
  have hrect : Icc a (min c v₀) ×ˢ Icc v₀ b ⊆ D := by
    intro p hp
    exact ⟨⟨hp.1.1, ((le_min_iff.mp hp.1.2).2).trans hp.2.1, hp.2.2⟩,
      (le_min_iff.mp hp.1.2).1⟩
  have hD : UniqueDiffOn ℝ D := uniqueDiffOn_triangle_inter_fst_le hac hcb
  have cgu := continuousOn_pdU cg hD
  have hsU (x : ℝ) (hx : x ∈ Icc v₀ b) :
      MapsTo (fun y => (y, x)) (Icc a (min c v₀)) D :=
    fun y hy => hrect ⟨hy, hx⟩
  have hsV (y : ℝ) (hy : y ∈ Icc a (min c v₀)) :
      MapsTo (fun x => (y, x)) (Icc v₀ b) D :=
    fun x hx => hrect ⟨hy, hx⟩
  have hrep (x : ℝ) (hx : x ∈ Icc v₀ b) :
      EqOn (fun y => f y x) (fun y => f y v₀ + ∫ t in v₀..x, g y t)
        (Icc a (min c v₀)) := by
    intro y hy
    have h := integralForm_pdV cf hD hx.1
      (fun t ht => hsV y hy ⟨ht.1, ht.2.trans hx.2⟩)
    have he : (∫ t in v₀..x, pdV D f y t) = ∫ t in v₀..x, g y t := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact hfg (y, t) (hsV y hy (by
        rw [uIcc_of_le hx.1] at ht
        exact ⟨ht.1, ht.2.trans hx.2⟩))
    have hval : f y x - f y v₀ = ∫ t in v₀..x, pdV D f y t := h.2
    rw [he] at hval
    simpa only [add_comm] using (eq_add_of_sub_eq hval)
  have hform (x : ℝ) (hx : x ∈ Icc v₀ b) :
      pdU D f u x = pdU D f u v₀ + ∫ t in v₀..x, pdU D g u t := by
    have hsub : Icc a (min c v₀) ×ˢ uIcc v₀ x ⊆ D := by
      intro p hp
      rw [uIcc_of_le hx.1] at hp
      exact hrect ⟨hp.1, hp.2.1, hp.2.2.trans hx.2⟩
    have hd := hasDerivWithinAt_of_integral_representation_rectangle ha
      (cg.continuousOn.mono hsub) (cgu.mono hsub)
      (fun y hy t ht => hasDerivWithinAt_pdU cg (hsub ⟨hy, ht⟩)
        (fun z hz => hsub ⟨hz, ht⟩)) huA
      (hasDerivWithinAt_pdU cf (hsU v₀ ⟨le_rfl, hb⟩ huA) (hsU v₀ ⟨le_rfl, hb⟩))
      (hrep x hx)
    have hd' := hasDerivWithinAt_pdU cf (hsU x hx huA) (hsU x hx)
    exact (hd'.derivWithin (uniqueDiffOn_Icc ha u huA)).symm.trans
      (hd.derivWithin (uniqueDiffOn_Icc ha u huA))
  have ci : ContinuousOn (fun t => pdU D g u t) (Icc v₀ b) :=
    cgu.comp (continuousOn_const.prodMk continuousOn_id) (hsV u huA)
  have hd := (hasDerivAt_const v (pdU D f u v₀)).add
    ((Recon.hasDerivWithinAt_primitive ci ⟨hv₀v.le, hvb.le⟩).hasDerivAt
      (Icc_mem_nhds hv₀v hvb))
  simp only [zero_add] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds hv₀v hvb] with x hx
  exact hform x hx

/-- The mixed primitive derivative needs its transport identity only off
axis. A compact rectangle is chosen strictly inside the off-axis part of
the wedge, including either incoming boundary. This form is used for the
mass and charge sources before their incoming constraints are known. -/
theorem hasDerivAt_pdU_of_pdV_on_wedge_off_axis {a b c u v : ℝ}
    {f g : ℝ → ℝ → E} (hac : a < c) (hcb : c ≤ b)
    (cf : ContDiffOn ℝ 1 (Function.uncurry f)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cg : ContDiffOn ℝ 1 (Function.uncurry g)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hfg : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, p.1 < p.2 →
      pdV (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) f p.1 p.2 = g p.1 p.2)
    (hu : u ∈ Icc a c) (huv : u < v) (hvb : v < b) :
    HasDerivAt (pdU (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) f u)
      (pdU (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) g u v) v := by
  let D := triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}
  let v₀ := (u + v) / 2
  let U := min c ((u + v₀) / 2)
  have huv₀ : u < v₀ := by dsimp [v₀]; linarith only [huv]
  have hv₀v : v₀ < v := by dsimp [v₀]; linarith only [huv]
  have haU : a < U := lt_min hac (by linarith only [hu.1, huv₀])
  have huU : u ≤ U := le_min hu.2 (by linarith only [huv₀])
  have hUc : U ≤ c := min_le_left _ _
  have hUv₀ : U < v₀ := (min_le_right _ _).trans_lt (by linarith only [huv₀])
  have hrect : Icc a U ×ˢ Icc v₀ b ⊆ D :=
    fun p hp => ⟨⟨hp.1.1, (hp.1.2.trans hUv₀.le).trans hp.2.1, hp.2.2⟩,
      hp.1.2.trans hUc⟩
  have hD : UniqueDiffOn ℝ D := uniqueDiffOn_triangle_inter_fst_le hac hcb
  have hm := mixed_v_pdU_of_transport_aux haU (hv₀v.trans hvb) hrect cf
    (cg.continuousOn.mono hrect) ((continuousOn_pdU cg hD).mono hrect)
    (fun x hx y hy => hfg (x, y) (hrect ⟨hx, hy⟩) ((hx.2.trans_lt hUv₀).trans_le hy.1))
    (fun x hx t ht => hasDerivWithinAt_pdU cg (hrect ⟨hx, ht⟩)
      (fun z hz => hrect ⟨hz, ht⟩)) ⟨hu.1, huU⟩ ⟨hv₀v.le, hvb.le⟩
  exact hm.hasDerivAt (Icc_mem_nhds hv₀v hvb)


end EmcsfAcExtension.Local.Null
