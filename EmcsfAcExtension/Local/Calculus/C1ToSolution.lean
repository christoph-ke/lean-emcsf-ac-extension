module

public import EmcsfAcExtension.Local.Defs.C1Class
public import EmcsfAcExtension.Frozen.Fields.EqOn
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Local.Api.EqOn
import EmcsfAcExtension.Infra.Calculus.Glue

/-! # Locality of the classical solution class

Within-domain equations restrict to subdomains with unique differentiation,
and glue on relatively open patches. No frozen predicate is changed.
-/

public section

open Set Filter Topology

namespace EmcsfAcExtension.Local

variable {e : ℝ} {S S' : Fields} {D D' : Set (ℝ × ℝ)}

-- `IsC1Solution.mono` and `IsC1Solution.congr` live in `Local/Defs/C1Class.lean` (internal project
-- record
-- landing).

/-- Glue two classical solutions for the same fields on a relatively open cover.
The relative-neighborhood conditions include points on the outer boundary. -/
theorem IsC1Solution.union (hS : IsC1Solution e S D) (hS' : IsC1Solution e S D')
    (hD : ∀ p ∈ D, D ∈ 𝓝[D ∪ D'] p)
    (hD' : ∀ p ∈ D', D' ∈ 𝓝[D ∪ D'] p)
    (huniq : UniqueDiffOn ℝ (D ∪ D')) : IsC1Solution e S (D ∪ D') := by
  have cover : ∀ p ∈ D ∪ D', ∃ i : Bool,
      p ∈ (if i then D else D') ∧ (if i then D else D') ∈ 𝓝[D ∪ D'] p := by
    intro p hp
    rcases hp with hp | hp
    · exact ⟨true, hp, hD p hp⟩
    · exact ⟨false, hp, hD' p hp⟩
  have c1 {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {f : ℝ × ℝ → E} (hf : ContDiffOn ℝ 1 f D) (hf' : ContDiffOn ℝ 1 f D') :
      ContDiffOn ℝ 1 f (D ∪ D') :=
    contDiffOn_of_relative_cover cover (by intro i; cases i <;> assumption)
  have locU {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {f : ℝ → ℝ → E} {C : Set (ℝ × ℝ)} (hf : ContDiffOn ℝ 1 (Function.uncurry f) C)
      {p : ℝ × ℝ} (hp : p ∈ C) (hp' : p ∈ D ∪ D') (hC : C ∈ 𝓝[D ∪ D'] p) :
      pdU (D ∪ D') f p.1 p.2 = pdU C f p.1 p.2 := by
    exact congrArg (fun L => L (1, 0))
      (fderivWithin_eq_on_relative_patch huniq hp' hC
        (hf.differentiableOn (by norm_num) p hp)).symm
  have locV {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {f : ℝ → ℝ → E} {C : Set (ℝ × ℝ)} (hf : ContDiffOn ℝ 1 (Function.uncurry f) C)
      {p : ℝ × ℝ} (hp : p ∈ C) (hp' : p ∈ D ∪ D') (hC : C ∈ 𝓝[D ∪ D'] p) :
      pdV (D ∪ D') f p.1 p.2 = pdV C f p.1 p.2 := by
    exact congrArg (fun L => L (0, 1))
      (fderivWithin_eq_on_relative_patch huniq hp' hC
        (hf.differentiableOn (by norm_num) p hp)).symm
  refine {
    subset := union_subset hS.subset hS'.subset
    r_pos := fun p hp => hp.elim (hS.r_pos p) (hS'.r_pos p)
    lam_pos := fun p hp => hp.elim (hS.lam_pos p) (hS'.lam_pos p)
    nu_neg := fun p hp => hp.elim (hS.nu_neg p) (hS'.nu_neg p)
    one_sub_mu_pos := fun p hp => hp.elim (hS.one_sub_mu_pos p) (hS'.one_sub_mu_pos p)
    c1_r := c1 hS.c1_r hS'.c1_r
    c1_lam := c1 hS.c1_lam hS'.c1_lam
    c1_nu := c1 hS.c1_nu hS'.c1_nu
    c1_m := c1 hS.c1_m hS'.c1_m
    c1_Q := c1 hS.c1_Q hS'.c1_Q
    c1_phi := c1 hS.c1_phi hS'.c1_phi
    c1_A := c1 hS.c1_A hS'.c1_A
    c1_theta := c1 hS.c1_theta hS'.c1_theta
    c1_xi := c1 hS.c1_xi hS'.c1_xi
    eq_v := ?_
    eq_u := ?_
    axis := fun t ht => ht.elim (hS.axis t) (hS'.axis t) }
  · intro p hp huv
    rcases hp with hp | hp
    · simpa only [
        locV hS.c1_r hp (Or.inl hp) (hD p hp),
        locV hS.c1_nu hp (Or.inl hp) (hD p hp),
        locV hS.c1_m hp (Or.inl hp) (hD p hp),
        locV hS.c1_Q hp (Or.inl hp) (hD p hp),
        locV hS.c1_A hp (Or.inl hp) (hD p hp),
        locV hS.c1_phi hp (Or.inl hp) (hD p hp),
        locV hS.c1_xi hp (Or.inl hp) (hD p hp)] using hS.eq_v p hp huv
    · simpa only [
        locV hS'.c1_r hp (Or.inr hp) (hD' p hp),
        locV hS'.c1_nu hp (Or.inr hp) (hD' p hp),
        locV hS'.c1_m hp (Or.inr hp) (hD' p hp),
        locV hS'.c1_Q hp (Or.inr hp) (hD' p hp),
        locV hS'.c1_A hp (Or.inr hp) (hD' p hp),
        locV hS'.c1_phi hp (Or.inr hp) (hD' p hp),
        locV hS'.c1_xi hp (Or.inr hp) (hD' p hp)] using hS'.eq_v p hp huv
  · intro p hp huv
    rcases hp with hp | hp
    · simpa only [
        locU hS.c1_r hp (Or.inl hp) (hD p hp),
        locU hS.c1_lam hp (Or.inl hp) (hD p hp),
        locU hS.c1_m hp (Or.inl hp) (hD p hp),
        locU hS.c1_Q hp (Or.inl hp) (hD p hp),
        locU hS.c1_phi hp (Or.inl hp) (hD p hp),
        locU hS.c1_theta hp (Or.inl hp) (hD p hp)] using hS.eq_u p hp huv
    · simpa only [
        locU hS'.c1_r hp (Or.inr hp) (hD' p hp),
        locU hS'.c1_lam hp (Or.inr hp) (hD' p hp),
        locU hS'.c1_m hp (Or.inr hp) (hD' p hp),
        locU hS'.c1_Q hp (Or.inr hp) (hD' p hp),
        locU hS'.c1_phi hp (Or.inr hp) (hD' p hp),
        locU hS'.c1_theta hp (Or.inr hp) (hD' p hp)] using hS'.eq_u p hp huv

end EmcsfAcExtension.Local
