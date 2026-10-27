module

public import EmcsfAcExtension.Global.Observation.Domains
public import EmcsfAcExtension.Global.Api.Definitions
import Mathlib

/-! # Optical upper bounds in the retained inner normalization

The mixed radius equation is nonpositive before either comparison stop.
The two normalized boundary expansions therefore bound their respective
characteristic sections from above.
Source: charged_SF_new_version.tex:L2587–2608; approved internal project record (C3), (N0).
-/

public section

open Set

namespace EmcsfAcExtension.Global.Observation

private theorem section_nonincrease {f w : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (cf : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (w x) x)
    (hw : ∀ x ∈ Ioo a b, w x ≤ 0) : f b ≤ f a := by
  have hh : f b - f a ≤ (0 : ℝ) * (b - a) := by
    apply (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le cf
      (fun x hx => by
        rw [interior_Icc] at hx
        exact (hd x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => by
        rw [interior_Icc] at hx
        rw [(hd x hx).deriv]
        exact hw x hx)
      a (left_mem_Icc.mpr hab) b (right_mem_Icc.mpr hab) hab
  linarith only [hh]

/-- [internal]
Both inner expansions have upper bound one half, from the actual
component equations and nonpositive mixed radius source on the complete
inner region. These differential and domain inputs are discharged by
the source-window consumer. Boundary normalization is used only at the
correct same-label endpoints. The coefficient is universal, independent
of the solution, coupling, background and both radial cutoffs. -/
theorem inner_expansion_upper_of_component_equations
    {S : Fields} {D : Set (ℝ × ℝ)} {a b rho Lzero : ℝ}
    (cn : ContinuousOn (Function.uncurry S.nu) (sidewaysTruncation S D a b rho Lzero))
    (cl : ContinuousOn (Function.uncurry S.lam) (sidewaysTruncation S D a b rho Lzero))
    (htri : ∀ p ∈ sidewaysTruncation S D a b rho Lzero,
      sidewaysTriangle p.2 p.1 ⊆ sidewaysTruncation S D a b rho Lzero)
    (hdn : ∀ p ∈ sidewaysTruncation S D a b rho Lzero,
      HasDerivAt (S.nu p.1) (S.rUV p.1 p.2) p.2)
    (hdl : ∀ p ∈ sidewaysTruncation S D a b rho Lzero,
      HasDerivAt (fun u => S.lam u p.2) (S.rUV p.1 p.2) p.1)
    (hmixed : ∀ p ∈ sidewaysTruncation S D a b rho Lzero, S.rUV p.1 p.2 ≤ 0)
    (hboundary : ∀ t ∈ Icc a b, S.nu t t = -1 / 2 ∧ S.lam t t = 1 / 2) :
    ∀ p ∈ sidewaysTruncation S D a b rho Lzero,
      -S.nu p.1 p.2 ≤ 1 / 2 ∧ S.lam p.1 p.2 ≤ 1 / 2 := by
  intro p hp
  have hIn (x) (hx : x ∈ Icc p.2 p.1) :
      (x, p.2) ∈ sidewaysTruncation S D a b rho Lzero :=
    htri p hp (sidewaysTriangle_incoming hx)
  have hOut (x) (hx : x ∈ Icc p.2 p.1) :
      (p.1, x) ∈ sidewaysTruncation S D a b rho Lzero :=
    htri p hp (sidewaysTriangle_outgoing hx)
  have hnu := section_nonincrease hp.1.2.2.1
    (cn.comp (continuous_const.prodMk continuous_id).continuousOn hOut)
    (fun x hx => hdn (p.1, x) (hOut x (Ioo_subset_Icc_self hx)))
    (fun x hx => hmixed (p.1, x) (hOut x (Ioo_subset_Icc_self hx)))
  have hlam := section_nonincrease hp.1.2.2.1
    (cl.comp (continuous_id.prodMk continuous_const).continuousOn hIn)
    (fun x hx => hdl (x, p.2) (hIn x (Ioo_subset_Icc_self hx)))
    (fun x hx => hmixed (x, p.2) (hIn x (Ioo_subset_Icc_self hx)))
  have hbNu := (hboundary p.1 ⟨hp.1.2.1.trans hp.1.2.2.1, hp.1.2.2.2⟩).1
  have hbLam := (hboundary p.2 ⟨hp.1.2.1, hp.1.2.2.1.trans hp.1.2.2.2⟩).2
  change S.nu p.1 p.1 ≤ S.nu p.1 p.2 at hnu
  change S.lam p.1 p.2 ≤ S.lam p.2 p.2 at hlam
  rw [hbNu] at hnu
  rw [hbLam] at hlam
  exact ⟨by linarith only [hnu], hlam⟩

end EmcsfAcExtension.Global.Observation
