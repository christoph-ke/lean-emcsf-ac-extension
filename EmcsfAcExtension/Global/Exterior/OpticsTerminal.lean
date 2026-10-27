module

public import EmcsfAcExtension.Global.Exterior.OpticsFrontier
public import EmcsfAcExtension.Global.Exterior.OpticsSpeed
import EmcsfAcExtension.Global.Exterior.OpticsInverse

/-! # Terminal consumer for the adaptive frontier speed

This conditional consumer uses precisely the terminal outputs specified
in the Root A architecture. It assembles the actual frontier, its
almost-everywhere speed and its local inverse estimates. The terminal
packet discharges the terminal inputs at assembly time.
-/

public section

open Set Filter Topology MeasureTheory

namespace EmcsfAcExtension.Global

variable {ui e : ℝ} {S : Fields}

/-- [internal]
Conditional terminal consumer of `charged_SF_new_version.tex:L1215–L1223`.
The frontier label tends to zero and is locally bi-Lipschitz, with the
literal speed identity and the numerical positive lower factor
`1/2-k` almost everywhere. Constants `L,m` may depend on the original
solution, prescribed slope and proper interval, and precede every pair
of labels in that interval. All terminal premises are discharged by
the terminal packet in the final assembly. -/
theorem charged_frontier_speed_of_terminal {C k : ℝ}
    (h : OriginalData ui e S) (M ell : ℝ → ℝ) {R₀ : ℝ} (hR : 0 < R₀) (hC : 0 < C)
    (hk : 0 < k ∧ k < 1 / 8)
    (hLip : LipschitzOnWith (Real.toNNReal k) ell (Ioc 0 R₀))
    (hcollapse : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0))
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0))
    (hphi : ∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
      C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) :
    ∃ u₀ ∈ Ioo ui 0, ∃ V : ℝ → ℝ,
      (∀ u ∈ Ico u₀ 0, u < V u ∧ V u < 0 ∧ S.r u (V u) = ell (S.r u 0)) ∧
      StrictMonoOn V (Ico u₀ 0) ∧ Tendsto V (𝓝[<] 0) (𝓝 0) ∧
      (∀ a b, u₀ ≤ a → a ≤ b → b < 0 →
        ∃ L > 0, ∃ m > 0,
          LipschitzOnWith (Real.toNNReal L) V (Icc a b) ∧
          (∀ u ∈ Icc a b, ∀ w ∈ Icc a b, m * dist u w ≤ dist (V u) (V w)) ∧
          (∀ᵐ u ∂volume.restrict (Icc a b),
            S.lam u (V u) * deriv V u =
                -S.nu u (V u) - deriv ell (S.r u 0) * (-S.nu u 0) ∧
              (1 / 2 - k) * (-S.nu u 0) ≤ S.lam u (V u) * deriv V u ∧
              0 < S.lam u (V u) * deriv V u)) := by
  obtain ⟨u₀, hu₀, V, hroot, hRange, hmono, hVt, hratio, hVLip⟩ :=
    Exterior.frontier_geometry_of_terminal h M ell hR hC hk hLip
      hcollapse hmass hell hellsmall hsmall hphi
  have hsegments (a b : ℝ) (hia : u₀ ≤ a) (hab : a ≤ b) (hb : b < 0) :
      ∃ L > 0, ∃ m > 0,
        LipschitzOnWith (Real.toNNReal L) V (Icc a b) ∧
        (∀ u ∈ Icc a b, ∀ w ∈ Icc a b, m * dist u w ≤ dist (V u) (V w)) ∧
        (∀ᵐ u ∂volume.restrict (Icc a b),
          S.lam u (V u) * deriv V u =
              -S.nu u (V u) - deriv ell (S.r u 0) * (-S.nu u 0) ∧
            (1 / 2 - k) * (-S.nu u 0) ≤ S.lam u (V u) * deriv V u ∧
            0 < S.lam u (V u) * deriv V u) := by
    obtain ⟨L, hL, hLipV⟩ := hVLip a b hia hab hb
    have hspeed := Exterior.frontier_speed_ae_of_graph h ell V hu₀ hia hab hb hk.1.le
      (show k < 1 / 2 by linarith [hk.2]) hLip hLipV
      (fun u hu => hRange u ⟨hia.trans hu.1, hu.2.trans_lt hb⟩) hroot hratio
    obtain ⟨c, hc, B, hB, hbounds⟩ := Exterior.proper_row_optical_bounds h
      (hu₀.1.le.trans hia) hab hb
    let m := (1 / 2 - k) * c / B
    have hm : 0 < m := div_pos (mul_pos (by linarith [hk.2]) hc) hB
    have hd : ∀ᵐ u ∂volume.restrict (Icc a b), m ≤ deriv V u := by
      filter_upwards [hspeed, ae_restrict_mem measurableSet_Icc] with u hs hu
      have huLate : u ∈ Ico u₀ 0 := ⟨hia.trans hu.1, hu.2.trans_lt hb⟩
      have hr := hroot u huLate
      have hbd := hbounds u hu (V u) ⟨hr.1.le, hr.2.1.le⟩
      have hbd0 := hbounds u hu 0 ⟨huLate.2.le, le_rfl⟩
      have hl : 0 < S.lam u (V u) := hc.trans_le hbd.1
      have hdpos : 0 < deriv V u := by
        by_contra hn
        have hnprod := mul_nonpos_of_nonneg_of_nonpos hl.le (le_of_not_gt hn)
        exact (not_lt_of_ge hnprod) hs.2.2
      have h₁ := mul_le_mul_of_nonneg_right hbd.2.1 hdpos.le
      have h₂ := mul_le_mul_of_nonneg_left hbd0.2.2.1
        (show 0 ≤ 1 / 2 - k by linarith [hk.2])
      dsimp [m]
      apply (div_le_iff₀ hB).mpr
      nlinarith only [h₁, h₂, hs.2.1]
    have hmV : MonotoneOn V (Icc a b) := hmono.mono
      (fun u hu => ⟨hia.trans hu.1, hu.2.trans_lt hb⟩)
    exact ⟨L, hL, m, hm, hLipV,
      Exterior.inverse_distance_le_of_ae_deriv hab hLipV hmV hd, hspeed⟩
  have hstrict : StrictMonoOn V (Ico u₀ 0) := by
    intro u hu w hw huw
    obtain ⟨L, hL, m, hm, hVL, hdist, hspeed⟩ := hsegments u w hu.1 huw.le hw.2
    have hlow := hdist u ⟨le_rfl, huw.le⟩ w ⟨huw.le, le_rfl⟩
    have hpos : 0 < dist (V u) (V w) :=
      (mul_pos hm (dist_pos.mpr (ne_of_lt huw))).trans_le hlow
    have hle := hmono hu hw huw.le
    exact lt_of_le_of_ne hle (fun heq => (ne_of_gt hpos) (by simp [heq]))
  exact ⟨u₀, hu₀, V, hroot, hstrict, hVt, hsegments⟩

end EmcsfAcExtension.Global
