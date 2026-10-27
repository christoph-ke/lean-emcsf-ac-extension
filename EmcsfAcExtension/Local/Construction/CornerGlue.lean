module

public import EmcsfAcExtension.Local.Defs.C1Class
public import EmcsfAcExtension.Local.Construction.TraceExtension
public import EmcsfAcExtension.Local.Broad.RectangleState
import EmcsfAcExtension.Local.Api.EqOn

/-! # Gluing classical fields across matching first jets

The old triangle and the appended rectangle have a closed common side.
Equality of their first jets, supplied by the rectangle construction,
allows gluing across that side. An open-overlap hypothesis is unnecessary.
-/

public section

open Set Filter Topology

namespace EmcsfAcExtension.Local

open Broad

/-- Choose the first configuration on `A` and the second elsewhere.
Only values on the requested union are used by the gluing theorem. -/
@[expose] noncomputable def continuationGlue (A : Set (ℝ × ℝ)) (F G : Fields) : Fields := by
  classical
  exact {
    r := fun u v => if (u, v) ∈ A then F.r u v else G.r u v
    lam := fun u v => if (u, v) ∈ A then F.lam u v else G.lam u v
    nu := fun u v => if (u, v) ∈ A then F.nu u v else G.nu u v
    m := fun u v => if (u, v) ∈ A then F.m u v else G.m u v
    Q := fun u v => if (u, v) ∈ A then F.Q u v else G.Q u v
    phi := fun u v => if (u, v) ∈ A then F.phi u v else G.phi u v
    A := fun u v => if (u, v) ∈ A then F.A u v else G.A u v
    theta := fun u v => if (u, v) ∈ A then F.theta u v else G.theta u v
    xi := fun u v => if (u, v) ∈ A then F.xi u v else G.xi u v }

/-- The chosen representative agrees with the first configuration on
the first closed piece, without a compatibility premise. -/
theorem continuationGlue_eqOn_left (A : Set (ℝ × ℝ)) (F G : Fields) :
    (continuationGlue A F G).EqOn F A := by
  intro p hp
  simp [continuationGlue, hp]

/-- Compatibility of values on the intersection gives equality with
the second configuration on the entire second closed piece. -/
theorem continuationGlue_eqOn_right {A B : Set (ℝ × ℝ)} {F G : Fields}
    (hFG : F.EqOn G (A ∩ B)) : (continuationGlue A F G).EqOn G B := by
  intro p hp
  by_cases hpA : p ∈ A
  · simpa only [continuationGlue, ite_eq_left hpA] using hFG p ⟨hpA, hp⟩
  · simp [continuationGlue, hpA]

/-- Joint C¹ regularity of the characteristic state is the product of
the nine primary regularities, in the literal Goursat block order. -/
theorem IsC1Solution.c1_rectangle_state {e : ℝ} {F : Fields} {D : Set (ℝ × ℝ)}
    (hF : IsC1Solution e F D) : ContDiffOn ℝ 1 (rectangle_state F) D :=
  (hF.c1_lam.prodMk hF.c1_theta).prodMk
    (hF.c1_r.prodMk (hF.c1_nu.prodMk (hF.c1_m.prodMk (hF.c1_Q.prodMk
      (hF.c1_A.prodMk (hF.c1_phi.prodMk hF.c1_xi))))))


private theorem continuation_fderiv_subset {A B : Set (ℝ × ℝ)} {E : Type*}
      [NormedAddCommGroup E] [NormedSpace ℝ E]
      {f : ℝ → ℝ → E} (hf : ContDiffOn ℝ 1 (Function.uncurry f) (A ∪ B))
      {C : Set (ℝ × ℝ)} (hsub : C ⊆ A ∪ B) (hUC : UniqueDiffOn ℝ C)
      {p : ℝ × ℝ} (hp : p ∈ C) :
      fderivWithin ℝ (Function.uncurry f) (A ∪ B) p =
        fderivWithin ℝ (Function.uncurry f) C p :=
    (fderivWithin_subset hsub (hUC p hp)
      (hf.differentiableOn (by norm_num) p (hsub hp))).symm

/-- Glue two classical full-system configurations across a closed
common side with matching first state jets. The jet premise is the
actual output required from (47), not a replacement for its proof.
Every primary regularity and equation on the union is proved here;
the scalar and gauge values on each piece are retained exactly. -/
theorem c1_continuationGlue_of_matching_jets
    {e : ℝ} {F G : Fields} {A B : Set (ℝ × ℝ)}
    (hA : IsClosed A) (hB : IsClosed B)
    (hUA : UniqueDiffOn ℝ A) (hUB : UniqueDiffOn ℝ B)
    (hF : IsC1Solution e F A) (hG : IsC1Solution e G B)
    (hFG : F.EqOn G (A ∩ B))
    (hjet : ∀ p ∈ A ∩ B,
      fderivWithin ℝ (rectangle_state F) A p = fderivWithin ℝ (rectangle_state G) B p) :
    IsC1Solution e (continuationGlue A F G) (A ∪ B) := by
  let H := continuationGlue A F G
  change IsC1Solution e H (A ∪ B)
  have hHF : H.EqOn F A := continuationGlue_eqOn_left A F G
  have hHG : H.EqOn G B := continuationGlue_eqOn_right hFG
  have hHA : IsC1Solution e H A := hF.congr hHF
  have hHB : IsC1Solution e H B := hG.congr hHG
  have hstateF : EqOn (rectangle_state H) (rectangle_state F) A :=
    fun p hp => (rectangle_state_eq_iff H F p).mpr (hHF p hp)
  have hstateG : EqOn (rectangle_state H) (rectangle_state G) B :=
    fun p hp => (rectangle_state_eq_iff H G p).mpr (hHG p hp)
  have hstate : ContDiffOn ℝ 1 (rectangle_state H) (A ∪ B) := by
    apply contDiffOn_one_union_of_matching_jets hA hB hUA hUB
      hHA.c1_rectangle_state hHB.c1_rectangle_state
    intro p hp
    rw [fderivWithin_congr' hstateF hp.1, fderivWithin_congr' hstateG hp.2]
    exact hjet p hp
  have cr : ContDiffOn ℝ 1 (Function.uncurry H.r) (A ∪ B) := hstate.snd.fst
  have cl : ContDiffOn ℝ 1 (Function.uncurry H.lam) (A ∪ B) := hstate.fst.fst
  have ct : ContDiffOn ℝ 1 (Function.uncurry H.theta) (A ∪ B) := hstate.fst.snd
  have cn : ContDiffOn ℝ 1 (Function.uncurry H.nu) (A ∪ B) := hstate.snd.snd.fst
  have cm : ContDiffOn ℝ 1 (Function.uncurry H.m) (A ∪ B) := hstate.snd.snd.snd.fst
  have cq : ContDiffOn ℝ 1 (Function.uncurry H.Q) (A ∪ B) := hstate.snd.snd.snd.snd.fst
  have ca : ContDiffOn ℝ 1 (Function.uncurry H.A) (A ∪ B) := hstate.snd.snd.snd.snd.snd.fst
  have cp : ContDiffOn ℝ 1 (Function.uncurry H.phi) (A ∪ B) :=
    hstate.snd.snd.snd.snd.snd.snd.fst
  have cx : ContDiffOn ℝ 1 (Function.uncurry H.xi) (A ∪ B) :=
    hstate.snd.snd.snd.snd.snd.snd.snd
  refine {
    subset := union_subset hHA.subset hHB.subset
    r_pos := fun p hp => hp.elim (hHA.r_pos p) (hHB.r_pos p)
    lam_pos := fun p hp => hp.elim (hHA.lam_pos p) (hHB.lam_pos p)
    nu_neg := fun p hp => hp.elim (hHA.nu_neg p) (hHB.nu_neg p)
    one_sub_mu_pos := fun p hp => hp.elim (hHA.one_sub_mu_pos p) (hHB.one_sub_mu_pos p)
    c1_r := cr
    c1_lam := cl
    c1_nu := cn
    c1_m := cm
    c1_Q := cq
    c1_phi := cp
    c1_A := ca
    c1_theta := ct
    c1_xi := cx
    eq_v := ?_
    eq_u := ?_
    axis := fun t ht => ht.elim (hHA.axis t) (hHB.axis t) }
  · intro p hp huv
    rcases hp with hp | hp
    · simpa only [pdV,
        continuation_fderiv_subset cr subset_union_left hUA hp,
        continuation_fderiv_subset cn subset_union_left hUA hp,
        continuation_fderiv_subset cm subset_union_left hUA hp,
        continuation_fderiv_subset cq subset_union_left hUA hp,
        continuation_fderiv_subset ca subset_union_left hUA hp,
        continuation_fderiv_subset cp subset_union_left hUA hp,
        continuation_fderiv_subset cx subset_union_left hUA hp]
        using hHA.eq_v p hp huv
    · simpa only [pdV,
        continuation_fderiv_subset cr subset_union_right hUB hp,
        continuation_fderiv_subset cn subset_union_right hUB hp,
        continuation_fderiv_subset cm subset_union_right hUB hp,
        continuation_fderiv_subset cq subset_union_right hUB hp,
        continuation_fderiv_subset ca subset_union_right hUB hp,
        continuation_fderiv_subset cp subset_union_right hUB hp,
        continuation_fderiv_subset cx subset_union_right hUB hp]
        using hHB.eq_v p hp huv
  · intro p hp huv
    rcases hp with hp | hp
    · simpa only [pdU,
        continuation_fderiv_subset cr subset_union_left hUA hp,
        continuation_fderiv_subset cl subset_union_left hUA hp,
        continuation_fderiv_subset cm subset_union_left hUA hp,
        continuation_fderiv_subset cq subset_union_left hUA hp,
        continuation_fderiv_subset cp subset_union_left hUA hp,
        continuation_fderiv_subset ct subset_union_left hUA hp] using hHA.eq_u p hp huv
    · simpa only [pdU,
        continuation_fderiv_subset cr subset_union_right hUB hp,
        continuation_fderiv_subset cl subset_union_right hUB hp,
        continuation_fderiv_subset cm subset_union_right hUB hp,
        continuation_fderiv_subset cq subset_union_right hUB hp,
        continuation_fderiv_subset cp subset_union_right hUB hp,
        continuation_fderiv_subset ct subset_union_right hUB hp] using hHB.eq_u p hp huv

/-- Full-dimensional overlaps determine the matching first jets from
equality of values. This is the second gluing step, between the old
triangle/strip union and the axis corner. It applies at their closed
outer boundaries as well as inside the positive-width overlap. -/
theorem c1_continuationGlue_of_uniqueDiff_overlap
    {e : ℝ} {F G : Fields} {A B : Set (ℝ × ℝ)}
    (hA : IsClosed A) (hB : IsClosed B)
    (hUA : UniqueDiffOn ℝ A) (hUB : UniqueDiffOn ℝ B)
    (hUAB : UniqueDiffOn ℝ (A ∩ B))
    (hF : IsC1Solution e F A) (hG : IsC1Solution e G B)
    (hFG : F.EqOn G (A ∩ B)) :
    IsC1Solution e (continuationGlue A F G) (A ∪ B) := by
  apply c1_continuationGlue_of_matching_jets hA hB hUA hUB hF hG hFG
  intro p hp
  have heq : EqOn (rectangle_state F) (rectangle_state G) (A ∩ B) :=
    fun q hq => (rectangle_state_eq_iff F G q).mpr (hFG q hq)
  have hf := fderivWithin_subset inter_subset_left (hUAB p hp)
    (hF.c1_rectangle_state.differentiableOn (by norm_num) p hp.1)
  have hg := fderivWithin_subset inter_subset_right (hUAB p hp)
    (hG.c1_rectangle_state.differentiableOn (by norm_num) p hp.2)
  rw [← hf, ← hg]
  exact fderivWithin_congr' heq hp

end EmcsfAcExtension.Local
