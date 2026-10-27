module

public import EmcsfAcExtension.Local.Limit.Existence
public import EmcsfAcExtension.Local.Limit.Stability
import EmcsfAcExtension.Local.Broad.Propagation
import EmcsfAcExtension.Local.Api.EqOn

/-! # Broad identification after the constructed limit estimates

This is the order required by internal project record item 7 and internal project record. Actual AC
existence and constructed-pair stability precede broad identification.
Equality transports the frozen derivative representatives sectionwise a.e.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

/-- Transport a strong-limit witness along equality of all primary fields
on the triangle. Frozen j/k agree a.e. on each actual characteristic section,
so the same measurable envelopes and their masses are retained unchanged. -/
theorem StrongLimit.congr_of_eqOn {e T : ℝ} {Sn : ℕ → Fields} {S S' : Fields}
    (hlim : StrongLimit e T Sn S') (he : S.EqOn S' (triangle 0 T)) : StrongLimit e T Sn S := by
  refine ⟨hlim.unif_r.congr_right (fun _ hp => (he.r hp).symm),
    hlim.unif_lam.congr_right (fun _ hp => (he.lam hp).symm),
    hlim.unif_nu.congr_right (fun _ hp => (he.nu hp).symm),
    hlim.unif_m.congr_right (fun _ hp => (he.m hp).symm),
    hlim.unif_Q.congr_right (fun _ hp => (he.Q hp).symm),
    hlim.unif_phi.congr_right (fun _ hp => (he.phi hp).symm),
    hlim.unif_A.congr_right (fun _ hp => (he.A hp).symm),
    hlim.unif_theta.congr_right (fun _ hp => (he.theta hp).symm),
    hlim.unif_xi.congr_right (fun _ hp => (he.xi hp).symm), ?_, ?_⟩
  · obtain ⟨D, hDm, hDl, hD⟩ := hlim.env_j
    refine ⟨D, hDm, hDl, ?_⟩
    intro n u hu
    filter_upwards [hD n u hu, he.jOut_ae (fun v hv => ⟨hu.1, hv.1, hv.2⟩)] with v hv heq
    rwa [heq]
  · obtain ⟨D, hDm, hDl, hD⟩ := hlim.env_k
    refine ⟨D, hDm, hDl, ?_⟩
    intro n v hv
    filter_upwards [hD n v hv, he.kIn_ae (e := e) (fun u hu => ⟨hu.1, hu.2, hv.2⟩)] with u hu heq
    rwa [heq]

/-- Equality on the triangle transports the entire constructed-limit witness,
with the same classical approximants, datum variation errors and envelopes.
No regularity is imposed outside that triangle. -/
theorem IsConstructedLimit.congr_of_eqOn {e T : ℝ} {h : ℝ → ℂ} {S S' : Fields}
    (hlim : IsConstructedLimit e T h S') (he : S.EqOn S' (triangle 0 T)) :
    IsConstructedLimit e T h S := by
  obtain ⟨Sn, hn, hv, herr, hc1, hl⟩ := hlim
  exact ⟨Sn, hn, hv, herr, hc1, hl.congr_of_eqOn he⟩

/-- Identify every broad AC integral solution with the constructed solution
for the same admissible datum. All three positive constants are universal,
before time, coupling, datum and competitor. The returned bounds and strong
approximation apply to the competitor itself. This is the broad-identification
step of internal project record item 7, not a full general-sequence stability node. -/
theorem ac_identification_of_inputs (hex : WholeTriangleExistenceStmt) (hstab : StabExtendedStmt) :
    ∃ ε δ C : ℝ, 0 < ε ∧ 0 < δ ∧ 0 < C ∧
      ∀ (T e : ℝ) (h : ℝ → ℂ) (S : Fields), 0 < T →
        AbsolutelyContinuousOnInterval h 0 T → datumVar h T ≤ ε → chargedScale e h T ≤ δ →
        IsSolution e S (triangle 0 T) → IsRestartData S h T →
        IsConstructedLimit e T h S ∧ ExistenceBounds C e T h S := by
  obtain ⟨ε, δ, C, hε, hδ, hC, hexists⟩ := ac_data_existence_of_inputs hex hstab
  refine ⟨ε, δ, C, hε, hδ, hC, ?_⟩
  intro T e h S hT hac hd hscale hS hdata
  obtain ⟨S', hS', hdata', hcon, hb⟩ := hexists T e h hT hac hd hscale
  have he : S.EqOn S' (triangle 0 T) := broad_uniqueness hT hS hS'
    (fun v hv => ⟨((hdata.1 v hv).1).trans ((hdata'.1 v hv).1).symm,
      ((hdata.1 v hv).2).trans ((hdata'.1 v hv).2).symm⟩)
    (fun t ht => ⟨hdata.2 t ht, hdata'.2 t ht⟩)
  exact ⟨hcon.congr_of_eqOn he, hb.congr hT.le he⟩

end EmcsfAcExtension.Local
