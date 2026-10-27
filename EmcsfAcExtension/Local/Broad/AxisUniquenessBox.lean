module

public import EmcsfAcExtension.Local.Broad.GeometryContinuity

/-! # A fixed geometric box on a compact comparison domain

The qualitative box and finite BV budget are fixed before the oscillation
threshold and the axis neighborhood are chosen.
-/

public section

open Set

namespace EmcsfAcExtension.Local.Broad

private theorem compact_box_one {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hD : IsCompact D) (hne : D.Nonempty) :
    ∃ c C : ℝ, 0 < c ∧ 1 ≤ C ∧ ∀ p ∈ D,
      c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C ∧
      c ≤ -S.nu p.1 p.2 ∧ -S.nu p.1 p.2 ≤ C ∧
      c ≤ 1 - S.mu p.1 p.2 ∧ ‖S.phi p.1 p.2‖ ≤ C := by
  let f := fun p : ℝ × ℝ => min (S.lam p.1 p.2)
    (min (-S.nu p.1 p.2) (1 - S.mu p.1 p.2))
  have cf : ContinuousOn f D := hS.cont_lam.inf
    (hS.cont_nu.neg.inf (continuousOn_const.sub (continuousOn_mu hS)))
  obtain ⟨p, hp, hmin⟩ := hD.exists_isMinOn hne cf
  have hfp : 0 < f p := lt_min (hS.lam_pos p hp)
    (lt_min (neg_pos.mpr (hS.nu_neg p hp)) (hS.one_sub_mu_pos p hp))
  let H := fun p : ℝ × ℝ => |S.lam p.1 p.2| + |S.nu p.1 p.2| + ‖S.phi p.1 p.2‖ + 1
  have cH : ContinuousOn H D := ((hS.cont_lam.abs.add hS.cont_nu.abs).add hS.cont_phi.norm).add
    continuousOn_const
  obtain ⟨q, hq, hmax⟩ := hD.exists_isMaxOn hne cH
  refine ⟨f p, max (H q) 1, hfp, le_max_right _ _, ?_⟩
  intro x hx
  have hl := hmin hx
  have hu : H x ≤ max (H q) 1 := (hmax hx).trans (le_max_left _ _)
  have hl₁ := hl.trans (min_le_left _ _)
  have hl₂ := hl.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hl₃ := hl.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hu₁ := le_abs_self (S.lam x.1 x.2)
  have hu₂ := neg_le_abs (S.nu x.1 x.2)
  have hn₁ := abs_nonneg (S.lam x.1 x.2)
  have hn₂ := abs_nonneg (S.nu x.1 x.2)
  have hn₃ := norm_nonneg (S.phi x.1 x.2)
  dsimp [H] at hu
  exact ⟨hl₁, by linarith, hl₂, by linarith, hl₃, by linarith⟩

/-- Two solutions on a fixed nonempty compact domain admit a common
positive geometric box and a scalar bound at least one. These qualitative
bounds depend on the solutions and the parent compact domain, before
any later oscillation threshold or subtriangle is chosen. -/
theorem compact_solution_box {e : ℝ} {S₁ S₂ : Fields} {D : Set (ℝ × ℝ)}
    (hS₁ : IsSolution e S₁ D) (hS₂ : IsSolution e S₂ D)
    (hD : IsCompact D) (hne : D.Nonempty) :
    ∃ c C M : ℝ, 0 < c ∧ 0 ≤ C ∧ 1 ≤ M ∧
      ∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ D,
        c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C ∧
        c ≤ -S.nu p.1 p.2 ∧ -S.nu p.1 p.2 ≤ C ∧
        c ≤ 1 - S.mu p.1 p.2 ∧ ‖S.phi p.1 p.2‖ ≤ M := by
  obtain ⟨c₁, C₁, hc₁, hC₁, h₁⟩ := compact_box_one hS₁ hD hne
  obtain ⟨c₂, C₂, hc₂, hC₂, h₂⟩ := compact_box_one hS₂ hD hne
  have hC₁0 : 0 ≤ C₁ := zero_le_one.trans hC₁
  have hC₂0 : 0 ≤ C₂ := zero_le_one.trans hC₂
  refine ⟨min c₁ c₂, C₁ + C₂, C₁ + C₂, lt_min hc₁ hc₂, by positivity,
    by linarith, ?_⟩
  intro S hm p hp
  rcases Set.mem_insert_iff.mp hm with rfl | hm
  · rcases h₁ p hp with ⟨hl, hl', hn, hn', hg, hφ⟩
    exact ⟨(min_le_left _ _).trans hl, by linarith, (min_le_left _ _).trans hn,
      by linarith, (min_le_left _ _).trans hg, by linarith⟩
  · have he : S = S₂ := Set.mem_singleton_iff.mp hm
    subst S
    rcases h₂ p hp with ⟨hl, hl', hn, hn', hg, hφ⟩
    exact ⟨(min_le_right _ _).trans hl, by linarith, (min_le_right _ _).trans hn,
      by linarith, (min_le_right _ _).trans hg, by linarith⟩

end EmcsfAcExtension.Local.Broad
