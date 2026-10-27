module

public import EmcsfAcExtension.Local.Construction.CornerGlue
public import EmcsfAcExtension.Local.Construction.StripStateBounds
import EmcsfAcExtension.Local.Api.EqOn
import EmcsfAcExtension.Infra.Calculus.TriangleDiff
import EmcsfAcExtension.Local.Calculus.Partials

/-! # Primary bounds on a glued continuation strip

The characteristic state uses maximum product norms. Its value and full
derivative bounds therefore control each primary field without changing
the constant. Derivatives on either closed piece agree with the derivative
on the glued domain by unique differentiation.
-/

public section

open Set

namespace EmcsfAcExtension.Local

open Broad

/-- Finite-state value and derivative bounds control all nine primary
fields. The coefficient is exactly one,
independent of the configuration and domain. -/
theorem primary_field_bounds_of_state_bound {e C : ℝ} {F : Fields}
    {D : Set (ℝ × ℝ)} (hF : IsC1Solution e F D) (hU : UniqueDiffOn ℝ D)
    {p : ℝ × ℝ} (hp : p ∈ D)
    (hv : ‖rectangle_state F p‖ ≤ C)
    (hd : ‖fderivWithin ℝ (rectangle_state F) D p‖ ≤ C) :
    (∀ f ∈ ({F.r,F.lam,F.nu,F.m,F.Q,F.A} : Set (ℝ → ℝ → ℝ)),
      ‖f p.1 p.2‖ ≤ C ∧ ‖fderivWithin ℝ (Function.uncurry f) D p‖ ≤ C) ∧
    (∀ f ∈ ({F.phi,F.theta,F.xi} : Set (ℝ → ℝ → ℂ)),
      ‖f p.1 p.2‖ ≤ C ∧ ‖fderivWithin ℝ (Function.uncurry f) D p‖ ≤ C) := by
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
  have heq := hfull.fderivWithin (hU p hp)
  simp only [Function.uncurry_def] at heq
  change ‖fderivWithin ℝ
    (fun q : ℝ × ℝ => ((F.lam q.1 q.2,F.theta q.1 q.2),
      (F.r q.1 q.2,F.nu q.1 q.2,F.m q.1 q.2,F.Q q.1 q.2,
        F.A q.1 q.2,F.phi q.1 q.2,F.xi q.1 q.2))) D p‖ ≤ C at hd
  rw [heq] at hd
  simp only [ContinuousLinearMap.opNorm_prod, Prod.norm_def, max_le_iff] at hd
  simp only [rectangle_state, Prod.norm_def, max_le_iff] at hv
  constructor
  · intro f hf
    simp only [mem_insert_iff,mem_singleton_iff] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> tauto
  · intro f hf
    simp only [mem_insert_iff,mem_singleton_iff] at hf
    rcases hf with rfl | rfl | rfl <;> tauto

/-- Project the full primary state bound to the three fields needed
for the later-cone datum. The constant is retained exactly. -/
theorem primary_cone_bounds_of_state_bound {e C : ℝ} {F : Fields}
    {D : Set (ℝ × ℝ)} (hF : IsC1Solution e F D) (hU : UniqueDiffOn ℝ D)
    {p : ℝ × ℝ} (hp : p ∈ D)
    (hv : ‖rectangle_state F p‖ ≤ C)
    (hd : ‖fderivWithin ℝ (rectangle_state F) D p‖ ≤ C) :
    (‖F.lam p.1 p.2‖ ≤ C ∧
      ‖fderivWithin ℝ (Function.uncurry F.lam) D p‖ ≤ C) ∧
    (‖F.phi p.1 p.2‖ ≤ C ∧
      ‖fderivWithin ℝ (Function.uncurry F.phi) D p‖ ≤ C) ∧
    (‖F.theta p.1 p.2‖ ≤ C ∧
      ‖fderivWithin ℝ (Function.uncurry F.theta) D p‖ ≤ C) := by
  have hh := primary_field_bounds_of_state_bound hF hU hp hv hd
  exact ⟨hh.1 F.lam (by simp),hh.2 F.phi (by simp),hh.2 F.theta (by simp)⟩

/-- A bound on the finite-state value and derivative on each closed
piece passes to the glued solution. Unique differentiation of each
piece identifies its full derivative at the seam as well as away from
it. The constant is retained exactly. -/
theorem continuation_state_bound_on_union {e C : ℝ} {H F G : Fields}
    {A B : Set (ℝ × ℝ)} (hH : IsC1Solution e H (A ∪ B))
    (hUA : UniqueDiffOn ℝ A) (hUB : UniqueDiffOn ℝ B)
    (hHF : H.EqOn F A) (hHG : H.EqOn G B)
    (hF : ∀ p ∈ A, ‖rectangle_state F p‖ ≤ C ∧
      ‖fderivWithin ℝ (rectangle_state F) A p‖ ≤ C)
    (hG : ∀ p ∈ B, ‖rectangle_state G p‖ ≤ C ∧
      ‖fderivWithin ℝ (rectangle_state G) B p‖ ≤ C) :
    ∀ p ∈ A ∪ B, ‖rectangle_state H p‖ ≤ C ∧
      ‖fderivWithin ℝ (rectangle_state H) (A ∪ B) p‖ ≤ C := by
  have heqA : EqOn (rectangle_state H) (rectangle_state F) A :=
    fun p hp => (rectangle_state_eq_iff H F p).mpr (hHF p hp)
  have heqB : EqOn (rectangle_state H) (rectangle_state G) B :=
    fun p hp => (rectangle_state_eq_iff H G p).mpr (hHG p hp)
  intro p hp
  rcases hp with hp | hp
  · have hd := fderivWithin_subset subset_union_left (hUA p hp)
      (hH.c1_rectangle_state.differentiableOn (by norm_num) p (Or.inl hp))
    rw [← hd, fderivWithin_congr' heqA hp, heqA hp]
    exact hF p hp
  · have hd := fderivWithin_subset subset_union_right (hUB p hp)
      (hH.c1_rectangle_state.differentiableOn (by norm_num) p (Or.inr hp))
    rw [← hd, fderivWithin_congr' heqB hp, heqB hp]
    exact hG p hp

/-- The complete continuation bound, including both normalized
scalars and the inverse-gap margins, passes from two closed pieces to
their classical union. Unique differentiation on each piece identifies
the full derivative with its union derivative. The same constant is
retained, with no enlargement depending on either piece. -/
theorem c1BoundOn_union_of_classical {e C : ℝ} {H : Fields}
    {A B : Set (ℝ × ℝ)} (hH : IsC1Solution e H (A ∪ B))
    (hUA : UniqueDiffOn ℝ A) (hUB : UniqueDiffOn ℝ B)
    (hA : C1BoundOn H A C) (hB : C1BoundOn H B C) :
    C1BoundOn H (A ∪ B) C := by
  have hreal : ∀ f ∈ ({H.r,H.lam,H.nu,H.m,H.Q,H.A} : Set (ℝ → ℝ → ℝ)),
      ContDiffOn ℝ 1 (Function.uncurry f) (A ∪ B) := by
    intro f hf
    simp only [mem_insert_iff,mem_singleton_iff] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hH.c1_r
    · exact hH.c1_lam
    · exact hH.c1_nu
    · exact hH.c1_m
    · exact hH.c1_Q
    · exact hH.c1_A
  have hcomplex : ∀ f ∈ ({H.phi,H.theta,H.xi,H.a,H.b} : Set (ℝ → ℝ → ℂ)),
      ContDiffOn ℝ 1 (Function.uncurry f) (A ∪ B) := by
    intro f hf
    simp only [mem_insert_iff,mem_singleton_iff] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · exact hH.c1_phi
    · exact hH.c1_theta
    · exact hH.c1_xi
    · exact hH.c1_a
    · exact hH.c1_b
  have htransfer {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      (f : ℝ → ℝ → E) (hf : ContDiffOn ℝ 1 (Function.uncurry f) (A ∪ B))
      {D : Set (ℝ × ℝ)} (hD : D ⊆ A ∪ B) (hUD : UniqueDiffOn ℝ D)
      {p : ℝ × ℝ} (hp : p ∈ D)
      (hb : ‖f p.1 p.2‖ ≤ C ∧ ‖fderivWithin ℝ (Function.uncurry f) D p‖ ≤ C) :
      ‖f p.1 p.2‖ ≤ C ∧
        ‖fderivWithin ℝ (Function.uncurry f) (A ∪ B) p‖ ≤ C := by
    have he := fderivWithin_subset hD (hUD p hp)
      (hf.differentiableOn (by norm_num) p (hD hp))
    rw [← he]
    exact hb
  intro p hp
  rcases hp with hp | hp
  · obtain ⟨hl,hn,hg,hr,hc⟩ := hA p hp
    exact ⟨hl,hn,hg,
      fun f hf => htransfer f (hreal f hf) subset_union_left hUA hp (hr f hf),
      fun f hf => htransfer f (hcomplex f hf) subset_union_left hUA hp (hc f hf)⟩
  · obtain ⟨hl,hn,hg,hr,hc⟩ := hB p hp
    exact ⟨hl,hn,hg,
      fun f hf => htransfer f (hreal f hf) subset_union_right hUB hp (hr f hf),
      fun f hf => htransfer f (hcomplex f hf) subset_union_right hUB hp (hc f hf)⟩

/-- Glue an old triangle and a positive-radius rectangle using their
actual common-side values and full first jets. State bounds and the
outgoing expansion margin pass to the union with the same constants.
The rectangle has positive width and height, as required by internal project record. -/
theorem c1_triangle_strip_glue_with_bounds {e S d b C ℓ : ℝ}
    {F G : Fields} (hd : 0 < d) (hdS : d < S) (hSb : S < b)
    (hF : IsC1Solution e F (triangle 0 S))
    (hG : IsC1Solution e G (Icc 0 d ×ˢ Icc S b))
    (hseam : ∀ u ∈ Icc 0 d, rectangle_state F (u, S) = rectangle_state G (u, S))
    (hjet : ∀ u ∈ Icc 0 d,
      fderivWithin ℝ (rectangle_state F) (triangle 0 S) (u, S) =
      fderivWithin ℝ (rectangle_state G) (Icc 0 d ×ˢ Icc S b) (u, S))
    (hFb : ∀ p ∈ triangle 0 S, ‖rectangle_state F p‖ ≤ C ∧
      ‖fderivWithin ℝ (rectangle_state F) (triangle 0 S) p‖ ≤ C)
    (hGb : ∀ p ∈ Icc 0 d ×ˢ Icc S b, ‖rectangle_state G p‖ ≤ C ∧
      ‖fderivWithin ℝ (rectangle_state G) (Icc 0 d ×ˢ Icc S b) p‖ ≤ C)
    (hFl : ∀ p ∈ triangle 0 S, ℓ / 2 ≤ F.lam p.1 p.2)
    (hGl : ∀ p ∈ Icc 0 d ×ˢ Icc S b, ℓ / 2 ≤ G.lam p.1 p.2) :
    ∃ H : Fields,
      IsC1Solution e H (triangle 0 S ∪ (Icc 0 d ×ˢ Icc S b)) ∧
      H.EqOn F (triangle 0 S) ∧ H.EqOn G (Icc 0 d ×ˢ Icc S b) ∧
      (∀ p ∈ triangle 0 S ∪ (Icc 0 d ×ˢ Icc S b),
        ‖rectangle_state H p‖ ≤ C ∧
        ‖fderivWithin ℝ (rectangle_state H)
          (triangle 0 S ∪ (Icc 0 d ×ˢ Icc S b)) p‖ ≤ C) ∧
      ∀ p ∈ triangle 0 S ∪ (Icc 0 d ×ˢ Icc S b), ℓ/2 ≤ H.lam p.1 p.2 := by
  have hS : 0 < S := hd.trans hdS
  have hmatch : F.EqOn G (triangle 0 S ∩ (Icc 0 d ×ˢ Icc S b)) := by
    intro p hp
    have hv : p.2 = S := le_antisymm hp.1.2.2 hp.2.2.1
    have he : p = (p.1,S) := Prod.ext rfl hv
    exact (rectangle_state_eq_iff F G p).mp (by
      rw [he]
      exact hseam p.1 hp.2.1)
  have hj : ∀ p ∈ triangle 0 S ∩ (Icc 0 d ×ˢ Icc S b),
      fderivWithin ℝ (rectangle_state F) (triangle 0 S) p =
        fderivWithin ℝ (rectangle_state G) (Icc 0 d ×ˢ Icc S b) p := by
    intro p hp
    have hv : p.2 = S := le_antisymm hp.1.2.2 hp.2.2.1
    have he : p = (p.1,S) := Prod.ext rfl hv
    rw [he]
    exact hjet p.1 hp.2.1
  have hUA := uniqueDiffOn_triangle hS
  have hUB := uniqueDiffOn_rectangle hd hSb
  let H := continuationGlue (triangle 0 S) F G
  have hH : IsC1Solution e H (triangle 0 S ∪ (Icc 0 d ×ˢ Icc S b)) :=
    c1_continuationGlue_of_matching_jets (isClosed_triangle 0 S)
      (isClosed_Icc.prod isClosed_Icc) hUA hUB hF hG hmatch hj
  have hHF : H.EqOn F (triangle 0 S) := continuationGlue_eqOn_left _ F G
  have hHG : H.EqOn G (Icc 0 d ×ˢ Icc S b) := continuationGlue_eqOn_right hmatch
  refine ⟨H,hH,hHF,hHG,continuation_state_bound_on_union hH hUA hUB hHF hHG hFb hGb,?_⟩
  intro p hp
  rcases hp with hp | hp
  · rw [hHF.lam hp]
    exact hFl p hp
  · rw [hHG.lam hp]
    exact hGl p hp

end EmcsfAcExtension.Local
