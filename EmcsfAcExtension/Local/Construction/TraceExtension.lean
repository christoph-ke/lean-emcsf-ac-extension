module

public import Mathlib

/-! # C¹ extension of closed-interval characteristic data

Linear continuation by the endpoint derivatives supplies genuine global
C¹ representatives without assuming a Lipschitz derivative of the data.
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- A C¹ function on two closed sets is C¹ on their union when the
within-domain derivatives agree on the common side. Every derivative
domain is required to have unique derivatives. -/
theorem contDiffOn_one_union_of_matching_jets {E₀ E : Type*}
    [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B : Set E₀} {f : E₀ → E}
    (hA : IsClosed A) (hB : IsClosed B)
    (hUA : UniqueDiffOn ℝ A) (hUB : UniqueDiffOn ℝ B)
    (hfA : ContDiffOn ℝ 1 f A) (hfB : ContDiffOn ℝ 1 f B)
    (hjet : ∀ p ∈ A ∩ B, fderivWithin ℝ f A p = fderivWithin ℝ f B p) :
    ContDiffOn ℝ 1 f (A ∪ B) := by
  have hUU : UniqueDiffOn ℝ (A ∪ B) := by
    intro p hp
    exact hp.elim (fun hpA => (hUA p hpA).mono subset_union_left)
      (fun hpB => (hUB p hpB).mono subset_union_right)
  have hdA := hfA.differentiableOn (by norm_num)
  have hdB := hfB.differentiableOn (by norm_num)
  have hd : DifferentiableOn ℝ f (A ∪ B) := by
    intro p hp
    by_cases hpA : p ∈ A
    · have hderivA := (hdA p hpA).hasFDerivWithinAt
      have hderivB : HasFDerivWithinAt f (fderivWithin ℝ f A p) B p := by
        by_cases hpB : p ∈ B
        · rw [hjet p ⟨hpA, hpB⟩]
          exact (hdB p hpB).hasFDerivWithinAt
        · exact HasFDerivWithinAt.of_notMem_closure (by simpa only [hB.closure_eq] using hpB)
      exact (hderivA.union hderivB).differentiableWithinAt
    · have hpB := hp.resolve_left hpA
      have hderivA : HasFDerivWithinAt f (fderivWithin ℝ f B p) A p :=
        HasFDerivWithinAt.of_notMem_closure (by simpa only [hA.closure_eq] using hpA)
      exact (hderivA.union (hdB p hpB).hasFDerivWithinAt).differentiableWithinAt
  have hfdA p (hp : p ∈ A) :
      fderivWithin ℝ f (A ∪ B) p = fderivWithin ℝ f A p :=
    (fderivWithin_subset subset_union_left (hUA p hp) (hd p (Or.inl hp))).symm
  have hfdB p (hp : p ∈ B) :
      fderivWithin ℝ f (A ∪ B) p = fderivWithin ℝ f B p :=
    (fderivWithin_subset subset_union_right (hUB p hp) (hd p (Or.inr hp))).symm
  have hcA : ContinuousOn (fderivWithin ℝ f (A ∪ B)) A :=
    (hfA.continuousOn_fderivWithin hUA (by norm_num)).congr hfdA
  have hcB : ContinuousOn (fderivWithin ℝ f (A ∪ B)) B :=
    (hfB.continuousOn_fderivWithin hUB (by norm_num)).congr hfdB
  apply (contDiffOn_succ_iff_fderivWithin (n := 0) hUU).mpr
  exact ⟨hd, by simp, contDiffOn_zero.mpr (hcA.union_of_isClosed hcB hA hB)⟩


/-- C¹ data on a nondegenerate closed interval have a global C¹
extension. No bound on second derivatives is assumed. -/
theorem exists_contDiff_one_extension_Icc {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} {f : ℝ → E} (hab : a < b)
    (hf : ContDiffOn ℝ 1 f (Icc a b)) :
    ∃ g : ℝ → E, ContDiff ℝ 1 g ∧ EqOn g f (Icc a b) := by
  classical
  let da := derivWithin f (Icc a b) a
  let db := derivWithin f (Icc a b) b
  let left := fun x : ℝ => f a + (x - a) • da
  let right := fun x : ℝ => f b + (x - b) • db
  let g := fun x : ℝ => if x ≤ a then left x else if x ≤ b then f x else right x
  have hga : EqOn g left (Iic a) := by
    intro x hx
    have hxa : x ≤ a := hx
    simp [g, hxa]
  have hgf : EqOn g f (Icc a b) := by
    intro x hx
    by_cases hxa : x ≤ a
    · have hx' : x = a := le_antisymm hxa hx.1
      subst x
      simp [g, left]
    · simp [g, hxa, hx.2]
  have hgb : EqOn g right (Ici b) := by
    intro x hx
    by_cases hxb : x ≤ b
    · have hx' : x = b := le_antisymm hxb hx
      subst x
      simp [g, right, not_le.mpr hab]
    · have hxa : ¬x ≤ a := not_le.mpr (hab.trans_le hx)
      simp [g, hxa, hxb]
  have hleft : ContDiff ℝ 1 left := by dsimp [left]; fun_prop
  have hright : ContDiff ℝ 1 right := by dsimp [right]; fun_prop
  have hca : ContDiffOn ℝ 1 g (Iic a) := hleft.contDiffOn.congr hga
  have hcf : ContDiffOn ℝ 1 g (Icc a b) := hf.congr hgf
  have hcb : ContDiffOn ℝ 1 g (Ici b) := hright.contDiffOn.congr hgb
  have hda : HasDerivWithinAt f da (Icc a b) a :=
    (hf.differentiableOn (by norm_num) a ⟨le_rfl, hab.le⟩).hasDerivWithinAt
  have hdb : HasDerivWithinAt f db (Icc a b) b :=
    (hf.differentiableOn (by norm_num) b ⟨hab.le, le_rfl⟩).hasDerivWithinAt
  have hla : HasDerivAt left da a := by
    simpa [left] using (((hasDerivAt_id a).sub_const a).smul_const da).const_add (f a)
  have hrb : HasDerivAt right db b := by
    simpa [right] using (((hasDerivAt_id b).sub_const b).smul_const db).const_add (f b)
  have hgaDer : HasDerivWithinAt g da (Iic a) a :=
    hla.hasDerivWithinAt.congr hga (hga le_rfl)
  have hgaMid : HasDerivWithinAt g da (Icc a b) a :=
    hda.congr hgf (hgf ⟨le_rfl, hab.le⟩)
  have hgbMid : HasDerivWithinAt g db (Icc a b) b :=
    hdb.congr hgf (hgf ⟨hab.le, le_rfl⟩)
  have hgbDer : HasDerivWithinAt g db (Ici b) b :=
    hrb.hasDerivWithinAt.congr hgb (hgb le_rfl)
  have hfirst : ContDiffOn ℝ 1 g (Iic a ∪ Icc a b) := by
    apply contDiffOn_one_union_of_matching_jets isClosed_Iic isClosed_Icc
      (uniqueDiffOn_Iic a) (uniqueDiffOn_Icc hab) hca hcf
    intro x hx
    have hx' : x = a := le_antisymm hx.1 hx.2.1
    subst x
    rw [hgaDer.hasFDerivWithinAt.fderivWithin (uniqueDiffOn_Iic a a le_rfl),
      hgaMid.hasFDerivWithinAt.fderivWithin
        (uniqueDiffOn_Icc hab a ⟨le_rfl, hab.le⟩)]
  have hset : Iic a ∪ Icc a b = Iic b := by
    ext x
    simp only [mem_union, mem_Iic, mem_Icc]
    constructor
    · intro hx
      exact hx.elim (fun h => h.trans hab.le) And.right
    · intro hx
      by_cases h : x ≤ a
      · exact Or.inl h
      · exact Or.inr ⟨(lt_of_not_ge h).le, hx⟩
  rw [hset] at hfirst
  have hlast : ContDiffOn ℝ 1 g (Iic b ∪ Ici b) := by
    apply contDiffOn_one_union_of_matching_jets isClosed_Iic isClosed_Ici
      (uniqueDiffOn_Iic b) (uniqueDiffOn_Ici b) hfirst hcb
    intro x hx
    have hx' : x = b := le_antisymm hx.1 hx.2
    subst x
    have hsub : Icc a b ⊆ Iic b := fun _ h => h.2
    have hd := fderivWithin_subset hsub
      (uniqueDiffOn_Icc hab b ⟨hab.le, le_rfl⟩)
      (hfirst.differentiableOn (by norm_num) b le_rfl)
    rw [← hd, hgbMid.hasFDerivWithinAt.fderivWithin
      (uniqueDiffOn_Icc hab b ⟨hab.le, le_rfl⟩),
      hgbDer.hasFDerivWithinAt.fderivWithin (uniqueDiffOn_Ici b b le_rfl)]
  have huniv : Iic b ∪ Ici b = (univ : Set ℝ) := by ext x; simp
  rw [huniv] at hlast
  exact ⟨g, contDiffOn_univ.mp hlast, hgf⟩

end EmcsfAcExtension.Local
