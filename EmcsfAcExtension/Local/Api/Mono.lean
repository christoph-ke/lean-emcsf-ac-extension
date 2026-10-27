module

public import EmcsfAcExtension.Local.Defs.Params
public import EmcsfAcExtension.Local.Defs.Box
public import EmcsfAcExtension.Frozen.IsSolution

/-! # Restrictions of the local solution class and data

These API lemmas restrict literal source objects and compare the numerical boxes.
-/

public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- Restrict a frozen solution to any smaller domain. -/
theorem isSolution_mono {e : ℝ} {S : Fields} {D D' : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hD : D' ⊆ D) : IsSolution e S D' where
  subset := hD.trans hS.subset
  r_pos := fun p hp => hS.r_pos p (hD hp)
  lam_pos := fun p hp => hS.lam_pos p (hD hp)
  nu_neg := fun p hp => hS.nu_neg p (hD hp)
  one_sub_mu_pos := fun p hp => hS.one_sub_mu_pos p (hD hp)
  cont_r := hS.cont_r.mono hD
  cont_lam := hS.cont_lam.mono hD
  cont_nu := hS.cont_nu.mono hD
  cont_m := hS.cont_m.mono hD
  cont_Q := hS.cont_Q.mono hD
  cont_phi := hS.cont_phi.mono hD
  cont_A := hS.cont_A.mono hD
  cont_theta := hS.cont_theta.mono hD
  cont_xi := hS.cont_xi.mono hD
  eq_out := fun u v₁ v₂ huv hv hseg => hS.eq_out u v₁ v₂ huv hv (hseg.trans hD)
  eq_in := fun u₁ u₂ v hu huv hseg => hS.eq_in u₁ u₂ v hu huv (hseg.trans hD)
  ac_out := fun u v₁ v₂ hv hseg => hS.ac_out u v₁ v₂ hv (hseg.trans hD)
  ac_in := fun u₁ u₂ v hu hseg => hS.ac_in u₁ u₂ v hu (hseg.trans hD)
  bv_loc := fun K hK => hS.bv_loc K (hK.trans hD)
  axis_small_var := by
    intro t ht η hη
    obtain ⟨δ, hδ, hout, hin⟩ := hS.axis_small_var t (hD ht) η hη
    exact ⟨δ, hδ, fun u v₁ v₂ hs => hout u v₁ v₂
      (hs.trans (inter_subset_inter_left _ hD)), fun u₁ u₂ v hs => hin u₁ u₂ v
      (hs.trans (inter_subset_inter_left _ hD))⟩
  axis := fun t ht => hS.axis t (hD ht)
  axis_mu := fun t ht => (hS.axis_mu t (hD ht)).mono_left
    (nhdsWithin_mono _ (inter_subset_inter_left _ hD))

/-- A triangle with later initial and earlier final labels lies in the larger triangle. -/
theorem triangle_mono {a a' b b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b) :
    triangle a' b' ⊆ triangle a b := by
  rintro ⟨u, v⟩ ⟨hau, huv, hvb⟩
  exact ⟨ha.trans hau, huv, hvb.trans hb⟩

/-- Restrict a restart triangle by decreasing its terminal label. -/
theorem triangle_subset_triangle {T' T : ℝ} (h : T' ≤ T) :
    triangle 0 T' ⊆ triangle 0 T := triangle_mono le_rfl h

/-- Restrict the two initial-cone data clauses and the axis gauge. -/
theorem isRestartData_mono {S : Fields} {h : ℝ → ℂ} {T' T : ℝ}
    (hd : IsRestartData S h T) (hT : T' ≤ T) : IsRestartData S h T' :=
  ⟨fun v hv => hd.1 v ⟨hv.1, hv.2.trans hT⟩,
    fun t ht => hd.2 t ⟨ht.1, ht.2.trans hT⟩⟩

/-- Restrict the temporary bootstrap box. -/
theorem BootBox.mono {S : Fields} {ε M : ℝ} {D D' : Set (ℝ × ℝ)}
    (h : BootBox S ε M D) (hD : D' ⊆ D) : BootBox S ε M D' :=
  fun p hp => h p (hD hp)

/-- Restrict the stability box. -/
theorem StabBox.mono {S : Fields} {c₀ C₀ ε M : ℝ} {D D' : Set (ℝ × ℝ)}
    (h : StabBox S c₀ C₀ ε M D) (hD : D' ⊆ D) : StabBox S c₀ C₀ ε M D' :=
  ⟨h.1, fun p hp => h.2 p (hD hp)⟩

end EmcsfAcExtension.Local
