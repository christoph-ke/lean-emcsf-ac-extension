module

public import EmcsfAcExtension.Global.Exterior.OpticsFrontier
public import EmcsfAcExtension.Global.Exterior.OpticsSpeed
public import EmcsfAcExtension.Infra.Level.Graph
import EmcsfAcExtension.Local.Calculus.Sections

/-! # The incoming-label speed of a proper radius cylinder

The speed is derived from the actual radius level identity, without an
assumed derivative of its label. This is the geometric input for the
separate cylinder exit-tail argument (`charged_SF_new_version.tex:L1393–L1395`).
No cylinder exit or covariant variation tail is claimed in this file.
-/

public section

open Set Filter Topology MeasureTheory

namespace EmcsfAcExtension.Global.Exterior

variable {ui e : ℝ} {S : Fields}

/-- [internal]
The actual radius level orders its outgoing labels strictly. This uses
only positive outgoing and negative incoming expansions, with no assumed
monotonicity or derivative of the cylinder graph. No constants occur. -/
theorem cylinder_label_strictMono_of_graph (h : OriginalData ui e S)
    {a b ρ : ℝ} {V : ℝ → ℝ} (hia : ui ≤ a) (hb : b < 0)
    (hroot : ∀ u ∈ Icc a b, u < V u ∧ V u ≤ 0 ∧ S.r u (V u) = ρ) :
    StrictMonoOn V (Icc a b) := by
  intro u hu w hw huw
  have hru := hroot u hu
  have hrw := hroot w hw
  have hs : inSeg u w (V w) ⊆ origDomain ui :=
    (inSeg_subset_origDomain_iff huw.le).2
      ⟨hia.trans hu.1, hw.2.trans_lt hb, hrw.1.le, hrw.2.1⟩
  have hf := (h.solution.eq_in u w (V w) huw.le hrw.1 hs).1
  have hi : 0 < ∫ x in u..w, -S.nu x (V w) := intervalIntegral.integral_pos huw
    (Calculus.continuousOn_in_section h.solution.cont_nu hs).neg
    (fun x hx => (neg_pos.mpr (h.solution.nu_neg (x, V w)
      (hs ⟨hx.1.le, hx.2, rfl⟩))).le)
    ⟨u, ⟨le_rfl, huw.le⟩, neg_pos.mpr (h.solution.nu_neg (u, V w)
      (hs ⟨le_rfl, huw.le, rfl⟩))⟩
  rw [intervalIntegral.integral_neg, ← hf.2] at hi
  change 0 < -(S.r w (V w) - S.r u (V w)) at hi
  rw [hrw.2.2] at hi
  have hm := (outgoing_radius_strictMono h
    (show u ∈ Ico ui 0 from ⟨hia.trans hu.1, hu.2.trans_lt hb⟩)).monotoneOn
  by_contra hn
  have hle := hm ⟨huw.le.trans hrw.1.le, hrw.2.1⟩
    ⟨hru.1.le, hru.2.1⟩ (le_of_not_gt hn)
  rw [hru.2.2] at hle
  linarith only [hi, hle]

/-- [node c:exterior#cylinder-speed]
A proper continuous constant-radius graph has the literal positive speed
`v_b' = (-ν_b)/λ_b` at every interior parameter, hence a.e. on the segment.
The graph's differentiability and strict increase are derived from the
radius equations. No terminal optical or density estimate is assumed.
No constants occur. -/
theorem cylinder_speed_of_graph (h : OriginalData ui e S)
    {a b ρ : ℝ} {V : ℝ → ℝ} (hia : ui ≤ a) (hb : b < 0)
    (hV : ContinuousOn V (Icc a b))
    (hroot : ∀ u ∈ Icc a b, u < V u ∧ V u ≤ 0 ∧ S.r u (V u) = ρ) :
    StrictMonoOn V (Icc a b) ∧
      ∀ᵐ u ∂volume.restrict (Icc a b),
        HasDerivAt V (-S.nu u (V u) / S.lam u (V u)) u ∧
          deriv V u = -S.nu u (V u) / S.lam u (V u) ∧ 0 < deriv V u := by
  have hm := cylinder_label_strictMono_of_graph h hia hb hroot
  refine ⟨hm, ?_⟩
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  have hum : u ∈ Icc a b := Ioo_subset_Icc_self hu
  have hr := hroot u hum
  have hv0 : V u < 0 := (hm hum ⟨hu.1.le.trans hu.2.le, le_rfl⟩ hu.2).trans_le
    (hroot b ⟨hu.1.le.trans hu.2.le, le_rfl⟩).2.1
  have hp : (u, V u) ∈ origDomain ui :=
    ⟨hia.trans hum.1, hum.2.trans_lt hb, hr.1.le, hr.2.1⟩
  have hd := radius_hasFDerivAt_of_interior h (hia.trans_lt hu.1) hr.1 hv0
  have hl := h.solution.lam_pos (u, V u) hp
  have hn := h.solution.nu_neg (u, V u) hp
  have hdV : HasDerivWithinAt V (-S.nu u (V u) / S.lam u (V u)) (Icc a b) u := by
    apply Level.hasDerivWithinAt_levelGraph_of_fderivWithin
      (D := Set.univ) hum (hV u hum) (fun _ _ => Set.mem_univ _)
      (fun x hx => (hroot x hx).2.2.trans hr.2.2.symm) hd.hasFDerivWithinAt hl.ne'
  have hdVa := hdV.hasDerivAt (Icc_mem_nhds hu.1 hu.2)
  exact ⟨hdVa, hdVa.deriv, by rw [hdVa.deriv]; exact div_pos (neg_pos.mpr hn) hl⟩

end EmcsfAcExtension.Global.Exterior
