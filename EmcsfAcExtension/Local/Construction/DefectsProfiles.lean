module

public import EmcsfAcExtension.Local.Defs.Recon
public import EmcsfAcExtension.Frozen.Triangle
import EmcsfAcExtension.Local.Construction.FullSystemCoefficients
import EmcsfAcExtension.Local.Construction.DefectsAxis

import EmcsfAcExtension.Local.Construction.ReconBasic

/-! # Axis defect evaluation for the actual C¹ reconstructions

The quadratic C¹ charge and mass profiles make the outgoing axis jets
zero, including at a collapsed top section. The closed-wedge diagonal
chain rule then evaluates the incoming jets, as in internal project record (29).
-/

public section

open Set

namespace EmcsfAcExtension.Local.Null

/-- A quadratic profile has zero outgoing differential at every zero of
its radius factor. This is a domain differential argument and includes
vertices where the outgoing section itself has no unique derivative. -/
theorem pdV_zero_of_quadratic_profile {D : Set (ℝ × ℝ)} {f r K : ℝ → ℝ → ℝ}
    (hD : UniqueDiffOn ℝ D) (cr : ContDiffOn ℝ 1 (Function.uncurry r) D)
    (cK : ContDiffOn ℝ 1 (Function.uncurry K) D)
    (hprofile : ∀ p ∈ D, f p.1 p.2 = r p.1 p.2 ^ 2 * K p.1 p.2)
    {p : ℝ × ℝ} (hp : p ∈ D) (hr : r p.1 p.2 = 0) : pdV D f p.1 p.2 = 0 := by
  have hR := (cr.differentiableOn (by norm_num) p hp).hasFDerivWithinAt
  have hK := (cK.differentiableOn (by norm_num) p hp).hasFDerivWithinAt
  have he : EqOn (Function.uncurry f)
      ((Function.uncurry r * Function.uncurry r) * Function.uncurry K) D := by
    intro q hq
    simpa only [pow_two, Pi.mul_apply, Function.uncurry] using hprofile q hq
  have hd := ((hR.mul hR).mul hK).congr he (he hp)
  change fderivWithin ℝ (Function.uncurry f) D p (0, 1) = 0
  rw [hd.fderivWithin (hD p hp)]
  simp [Function.uncurry_def, hr]

/-- The raw incoming defects of the actual reconstruction vanish at every
axis point of the nondegenerate closed wedge. Outgoing zero jets come from
the proved charge and mass profiles; incoming zero jets use the diagonal
chain rule. No incoming constraint, C² premise, or smallness estimate is
assumed. The sole bound `l` is fixed before the candidate. -/
theorem defects_axis_values_of_c1_reconstruction {a b c l e : ℝ}
    (hac : a < c) (hcb : c ≤ b) {lam : ℝ → ℝ → ℝ} {hh : ℝ → ℝ → ℂ}
    (hl : 0 < l)
    (cl : ContDiffOn ℝ 1 (Function.uncurry lam)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (ch : ContDiffOn ℝ 1 (Function.uncurry hh)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hlo : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, l ≤ lam p.1 p.2) :
    ∀ t ∈ Icc a c,
      defectQ e (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) (Recon.toFields e lam hh) t t = 0 ∧
        defectM (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) (Recon.toFields e lam hh) t t = 0 := by
  let D := triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}
  have hD : UniqueDiffOn ℝ D := uniqueDiffOn_triangle_inter_fst_le hac hcb
  obtain ⟨cr, _, _, _⟩ := contDiffOn_radial_scalar_fields hac hcb hl cl ch hlo
  obtain ⟨K, cK, hK, _⟩ := exists_c1_charge_profile (e := e) hac hcb hl cl ch hlo
  obtain ⟨V, cV, hV, _⟩ := exists_c1_mass_profile (e := e) hac hcb hl cl ch hlo
  have cQ := ((cr.pow 2).mul cK).congr hK
  have cm := (((cr.pow 2).mul cV).div_const 2).congr hV
  have hQv (t : ℝ) (ht : t ∈ Icc a c) : pdV D (Recon.Q e lam hh) t t = 0 :=
    pdV_zero_of_quadratic_profile (p := (t, t)) hD cr cK hK
      ⟨⟨ht.1, le_rfl, ht.2.trans hcb⟩, ht.2⟩ Recon.r_axis
  have hmv (t : ℝ) (ht : t ∈ Icc a c) : pdV D (Recon.m e lam hh) t t = 0 := by
    apply pdV_zero_of_quadratic_profile (p := (t, t)) hD cr (cV.div_const 2)
      (K := fun u v => V u v / 2)
      (fun p hp => by rw [hV p hp]; ring)
      ⟨⟨ht.1, le_rfl, ht.2.trans hcb⟩, ht.2⟩ Recon.r_axis
  exact defects_axis_values_on_wedge_of_outgoing_axis hac hcb cQ cm
    (fun _ _ => Recon.Q_axis) (fun _ _ => Recon.m_axis) hQv hmv
    (fun _ _ => Recon.r_axis) (fun _ _ => by simp [Recon.toFields])

end EmcsfAcExtension.Local.Null
