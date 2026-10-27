module

public import EmcsfAcExtension.Local.Construction.PicardPolynomial
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Uniform estimates for finite dimensional profile formulas

Normalized radial formulas are smooth functions of finitely many bounded
profiles and reciprocal denominators. Compactness supplies constants before
the domain and candidates, without selecting constants by `Classical.choose`.
-/

public section

open Set Metric

namespace EmcsfAcExtension.Local

/-- Extract one coordinate from a continuous finite vector of profiles. -/
@[expose] def picardProfileCoordinate {A E : Type*} [TopologicalSpace A]
    [TopologicalSpace E] {n : ℕ} (F : C(A, Fin n → E)) (i : Fin n) : C(A, E) :=
  ⟨fun p => F p i, (continuous_apply i).comp F.continuous⟩

/-- Coordinate extraction has universal sup-norm bound one. -/
theorem picardProfileCoordinate_norm_le {A E : Type*} [TopologicalSpace A]
    [CompactSpace A] [NormedAddCommGroup E] {n : ℕ}
    (F : C(A, Fin n → E)) (i : Fin n) : ‖picardProfileCoordinate F i‖ ≤ ‖F‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro p
  exact (norm_le_pi_norm (F p) i).trans (F.norm_coe_le_norm p)

/-- Coordinate extraction has universal Lipschitz constant one. -/
theorem picardProfileCoordinate_dist_le {A E : Type*} [TopologicalSpace A]
    [CompactSpace A] [NormedAddCommGroup E] {n : ℕ}
    (F G : C(A, Fin n → E)) (i : Fin n) :
    dist (picardProfileCoordinate F i) (picardProfileCoordinate G i) ≤ dist F G := by
  apply (ContinuousMap.dist_le dist_nonneg).mpr
  intro p
  have h : ‖F p - G p‖ ≤ dist F G := by
    simpa only [dist_eq_norm] using (ContinuousMap.dist_apply_le_dist (f := F) (g := G) p)
  simpa only [dist_eq_norm, picardProfileCoordinate, ContinuousMap.coe_mk, Pi.sub_apply]
    using (norm_le_pi_norm (F p - G p) i).trans h

/-- A fixed smooth finite dimensional formula has a positive size and
Lipschitz bound on every norm ball. The constant depends only on the formula
and radius `B`, uniformly in its arguments. -/
theorem picard_finite_profile_bound_aux {X E : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : X → E) (hF : ContDiff ℝ 1 F) (B : ℝ) :
    ∃ C > 0, (∀ x, ‖x‖ ≤ B → ‖F x‖ ≤ C) ∧
      ∀ x y, ‖x‖ ≤ B → ‖y‖ ≤ B → dist (F x) (F y) ≤ C * dist x y := by
  obtain ⟨A, hA⟩ := (isCompact_closedBall (0 : X) B).exists_bound_of_continuousOn
    hF.continuous.continuousOn
  obtain ⟨K, hK⟩ := hF.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall (0 : X) B) (isCompact_closedBall (0 : X) B)
  refine ⟨1 + |A| + (K : ℝ), by positivity, ?_, ?_⟩
  · intro x hx
    exact (hA x (by simpa only [mem_closedBall, dist_zero_right] using hx)).trans
      ((le_abs_self A).trans (by have hK0 := K.coe_nonneg; linarith))
  · intro x y hx hy
    exact (hK.dist_le_mul x (by simpa only [mem_closedBall, dist_zero_right] using hx)
      y (by simpa only [mem_closedBall, dist_zero_right] using hy)).trans
      (mul_le_mul_of_nonneg_right (by have hA0 := abs_nonneg A; linarith) dist_nonneg)

/-- The same finite dimensional estimate on a convex coordinate half-space.
The constant depends only on `F,B,κ,i`; a positive coordinate lower bound
can therefore control rational formulas uniformly before the candidates. -/
theorem picard_finite_profile_pos_bound_aux {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : (Fin n → ℝ) → E) (κ B : ℝ) (i : Fin n)
    (hF : ContDiffOn ℝ 1 F {v | κ ≤ v i}) :
    ∃ C > 0, (∀ x, ‖x‖ ≤ B → κ ≤ x i → ‖F x‖ ≤ C) ∧
      ∀ x y, ‖x‖ ≤ B → κ ≤ x i → ‖y‖ ≤ B → κ ≤ y i →
        dist (F x) (F y) ≤ C * dist x y := by
  let s : Set (Fin n → ℝ) := closedBall 0 B ∩ {v | κ ≤ v i}
  have hs : IsCompact s := (isCompact_closedBall 0 B).inter_right
    (isClosed_le continuous_const (continuous_apply i))
  have hc : Convex ℝ s := by
    apply (convex_closedBall 0 B).inter
    intro x hx y hy b d hb hd hbd
    change κ ≤ b * x i + d * y i
    calc
      κ = b * κ + d * κ := by rw [←add_mul, hbd, one_mul]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hx hb)
        (mul_le_mul_of_nonneg_left hy hd)
  have hf : ContDiffOn ℝ 1 F s := hF.mono inter_subset_right
  obtain ⟨A, hA⟩ := hs.exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨K, hK⟩ := hf.exists_lipschitzOnWith (by norm_num) hc hs
  refine ⟨1 + |A| + (K : ℝ), by positivity, ?_, ?_⟩
  · intro x hx hxκ
    exact (hA x ⟨by simpa only [mem_closedBall, dist_zero_right] using hx, hxκ⟩).trans
      ((le_abs_self A).trans (by have hK0 := K.coe_nonneg; linarith))
  · intro x y hx hxκ hy hyκ
    exact (hK.dist_le_mul x ⟨by simpa only [mem_closedBall, dist_zero_right] using hx, hxκ⟩
      y ⟨by simpa only [mem_closedBall, dist_zero_right] using hy, hyκ⟩).trans
      (mul_le_mul_of_nonneg_right (by have hA0 := abs_nonneg A; linarith) dist_nonneg)

end EmcsfAcExtension.Local
