module

public import EmcsfAcExtension.Global.Exterior.VariationTailsTerminal
public import EmcsfAcExtension.Global.Exterior.CylinderTailsGeometry
public import EmcsfAcExtension.Global.Exterior.FrontierIntegrability

/-! # The literal uniform radius-cylinder exit tail

The radius equation supplies each cylinder's label regularity and speed.
The common bound is independent of the radius and admissible final time.
Source: `charged_SF_new_version.tex:L1393–L1402`, L1413–L1416;
approved internal project record (M5), (D3).
-/

public section

open Set MeasureTheory Filter Topology

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
One vanishing tail bounds the exit costs of every continuous proper
constant-radius cylinder that remains in the adaptive exterior. The
local bi-Lipschitz constants and the positive cylinder speed are derived
from its radius-level identity. The common tail is fixed before choosing
the cylinder radius, initial row, or final time. -/
theorem cylinder_exit_tail_of_terminal {ui e C k₀ R₀ : ℝ} {S : Fields}
    (h : OriginalData ui e S) (M ell : ℝ → ℝ) (hR : 0 < R₀) (hC : 0 < C)
    (hk₀ : 0 < k₀ ∧ k₀ < 1 / 8)
    (hLip : LipschitzOnWith (Real.toNNReal k₀) ell (Ioc 0 R₀))
    (hMc : ContinuousOn M (Ioc 0 R₀)) (hM : ∀ R ∈ Ioc 0 R₀, 0 ≤ M R)
    (hAfinite : (∫⁻ R in Ioc 0 R₀, ENNReal.ofReal (M R / ell R ^ 2)) < ⊤)
    (hcollapse : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0))
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0))
    (hphi : ∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
      C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) :
    ∃ c ∈ Ioo ui 0, ∃ E : ℝ → ℝ, Tendsto E (𝓝[<] 0) (𝓝 0) ∧
      ∀ (a b ρ : ℝ) (γ : ℝ → ℝ), c ≤ a → a ≤ b → b < 0 →
        ContinuousOn γ (Icc a b) →
        (∀ u ∈ Icc a b, u < γ u ∧ γ u ≤ 0 ∧ S.r u (γ u) = ρ) →
        (∀ u ∈ Icc a b, ell (S.r u 0) ≤ ρ) →
        (∫ u in a..b, deriv γ u * ‖densityRepresentative e S a u (γ u)‖) ≤ E a := by
  obtain ⟨c, hc, t, E, hroot, hm, htt, hV, hF, hsegments, hE, hexit⟩ :=
    variation_and_boundary_exit_tails_of_terminal h M ell hR hC hk₀ hLip hMc hM hAfinite
      hcollapse hmass hell hellsmall hsmall hphi
  refine ⟨c, hc, E, hE, ?_⟩
  intro a b ρ γ ha hab hb hγ hγroot hheight
  obtain ⟨K, hK, m, hmpos, hL, hdist, hspeed⟩ := cylinder_bilipschitz_of_graph h
    (hc.1.le.trans ha) hab hb hγ hγroot
  have hmono := (cylinder_label_strictMono_of_graph h (hc.1.le.trans ha) hb hγroot).monotoneOn
  have hA := boundary_antilipschitz_of_inverse_distance (a := a) (b := b) (V := γ) hmpos
    (by simpa only [uIcc_of_le hab] using hdist)
  apply hexit a b γ (Real.toNNReal K) (Real.toNNReal m⁻¹) ha hab hb
    (by simpa only [uIcc_of_le hab] using hL)
    (by simpa only [uIcc_of_le hab] using hmono) hA
  intro u hu
  have hul : u ∈ Ico c 0 := ⟨ha.trans hu.1, hu.2.trans_lt hb⟩
  have hr := hroot u hul
  refine ⟨?_, (hγroot u hu).2.1⟩
  apply le_of_not_gt
  intro hv
  have hrad := outgoing_radius_strictMono h ⟨hc.1.le.trans hul.1, hul.2⟩
    ⟨(hγroot u hu).1.le, (hγroot u hu).2.1⟩ ⟨hr.1.le, hr.2.1.le⟩ hv
  rw [(hγroot u hu).2.2, hr.2.2] at hrad
  exact (not_lt_of_ge (hheight u hu)) hrad

end EmcsfAcExtension.Global.Exterior
