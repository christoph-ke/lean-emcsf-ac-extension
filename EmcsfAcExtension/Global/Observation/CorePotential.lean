module

public import EmcsfAcExtension.Global.Observation.InnerPotential
public import EmcsfAcExtension.Global.Observation.Domains
import Mathlib

/-! # The retained potential from the global core estimates

The relative-charge inequality controls the full outgoing primitive,
including the part outside the fixed inner annulus. Source:
charged_SF_new_version.tex:L2390–2404, L2587–2608; approved internal project record (A), (N0).
-/

public section

open Set Complex

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
Discharge the potential primitive's charge bound using the global core
relative-charge inequality and mass bound on every complete outgoing
section. The exact coefficient depends only on `δ,rStar`, uniformly in
all fields, outer radius, coupling and scalar background. The source
consumer discharges the component equations, continuity and core box.
-/
theorem potential_of_core_on_complete_region
    {S : Fields} {D : Set (ℝ × ℝ)} {a b rStar L δ e eta : ℝ} {H : ℂ}
    (hδ : 0 < δ) (hrStar : 0 < rStar) (hL : 1 ≤ L)
    (hscale : |e| * L * (1 + ‖H‖) = eta)
    (htri : ∀ p ∈ sidewaysTruncation S D a b rStar L,
      sidewaysTriangle p.2 p.1 ⊆ sidewaysTruncation S D a b rStar L)
    (hfields :
      let R := sidewaysTruncation S D a b rStar L
      ContinuousOn (Function.uncurry S.r) R ∧ ContinuousOn (Function.uncurry S.lam) R ∧
      ContinuousOn (Function.uncurry S.A) R ∧ ContinuousOn (Function.uncurry S.nu) R ∧
      ContinuousOn (Function.uncurry S.Q) R ∧ ContinuousOn (Function.uncurry S.m) R)
    (heq : ∀ p ∈ sidewaysTruncation S D a b rStar L,
      HasDerivAt (S.r p.1) (S.lam p.1 p.2) p.2 ∧
      HasDerivAt (S.A p.1) (S.AV p.1 p.2) p.2)
    (hdiag : ∀ t, (t, t) ∈ sidewaysTruncation S D a b rStar L → S.A t t = 0)
    (hbox : ∀ p ∈ sidewaysTruncation S D a b rStar L,
      S.m p.1 p.2 ∈ Icc 0 2 ∧ δ ≤ 1 - S.mu p.1 p.2 ∧
      0 ≤ S.lam p.1 p.2 ∧ |S.nu p.1 p.2| ≤ 1 / 2 ∧
      S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 ≤ S.mu p.1 p.2) :
    ∀ p ∈ sidewaysTruncation S D a b rStar L,
      |e * S.A p.1 p.2| * (1 + ‖H‖) ≤ (2 / (δ * rStar)) * eta := by
  intro p hp
  let R := sidewaysTruncation S D a b rStar L
  have hsec {E : Type} [TopologicalSpace E] {f : ℝ → ℝ → E}
      (hc : ContinuousOn (Function.uncurry f) R) :=
    continuousOn_outgoing_of_subtriangle hc (htri p hp)
  have hOut (t) (ht : t ∈ Icc p.2 p.1) : (p.1,t) ∈ R :=
    htri p hp (sidewaysTriangle_outgoing ht)
  have hQ (t) (ht : t ∈ Icc p.2 p.1) : |S.Q p.1 t| ≤ 2 * Real.sqrt L := by
    have hm := (hbox _ (hOut t ht)).1
    have hr : 0 < S.r p.1 t := hrStar.trans_le (hOut t ht).2.1
    have hrel := (hbox _ (hOut t ht)).2.2.2.2
    have hsq : S.Q p.1 t ^ 2 ≤ 2 * S.m p.1 t * S.r p.1 t := by
      have hh := (div_le_iff₀ (sq_pos_of_pos hr)).mp hrel
      change S.Q p.1 t ^ 2 ≤ 2 * S.m p.1 t / S.r p.1 t * S.r p.1 t ^ 2 at hh
      convert hh using 1
      field_simp
    have hfour : S.Q p.1 t ^ 2 ≤ 4 * L := hsq.trans
      ((mul_le_mul_of_nonneg_right (by linarith only [hm.2] : 2 * S.m p.1 t ≤ 4) hr.le).trans
        (mul_le_mul_of_nonneg_left (hOut t ht).2.2 (by norm_num)))
    have hsqrt := Real.sq_sqrt (zero_le_one.trans hL)
    have habs := sq_abs (S.Q p.1 t)
    have hsqrt0 := Real.sqrt_nonneg L
    nlinarith only [hfour, hsqrt, habs, hsqrt0, abs_nonneg (S.Q p.1 t)]
  have hA := potential_on_outgoing_of_mass_charge_bounds δ (2 * Real.sqrt L) hδ
    (by positivity) S hp.1.2.2.1 (hsec hfields.1) (hsec hfields.2.1)
    (hsec hfields.2.2.1) (hsec hfields.2.2.2.1)
    (hsec hfields.2.2.2.2.1) (hsec hfields.2.2.2.2.2)
    (fun t ht => (heq _ (hOut t (Ioo_subset_Icc_self ht))).1)
    (fun t ht => (heq _ (hOut t (Ioo_subset_Icc_self ht))).2)
    (hdiag p.1 (hOut p.1 (right_mem_Icc.mpr hp.1.2.2.1)))
    (fun t ht => ⟨hrStar.trans_le (hOut t ht).2.1,
      (hbox _ (hOut t ht)).2.2.1, (hbox _ (hOut t ht)).2.2.2.1,
      hQ t ht, (hbox _ (hOut t ht)).2.1⟩)
  exact charged_potential_of_sqrt_scale_bound hδ hrStar hp.2.1 hL hscale hA

end EmcsfAcExtension.Global.Observation
