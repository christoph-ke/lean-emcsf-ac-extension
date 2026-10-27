module

public import EmcsfAcExtension.Global.Cooling.Endpoint

/-! # Energy comparison with separate weak-regime bounds

The two separate source hypotheses of `charged_SF_new_version.tex:L2973–L2983`
suffice. The joint-bound theorem in `Endpoint` remains available to its
existing consumers.
-/

public section

namespace EmcsfAcExtension.Global.Cooling

/-- [node prop:charged-cool#weak-regime-energy-comparison]
Normalized energy and ordinary mass under the separate weak bounds.
All displayed constants are universal, uniformly for thresholds at most
`1/2`, independently of radius, coupling, and scalar background. -/
theorem weak_regime_energy_comparison_of_separate_bounds (S : Fields) (b u v δ : ℝ)
    (hb : 0 < b) (hr : S.r u v = b) (hmu : 0 ≤ S.mu u v)
    (hδ : δ ≤ 1 / 2) (hμbound : S.mu u v ≤ δ)
    (hybound : ‖S.theta u v / (S.lam u v : ℂ)‖ ≤ δ) :
    (‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 + S.mu u v) / 2 ≤
        cylinderEnergy S b u v / b ∧
      cylinderEnergy S b u v / b ≤
        ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 + S.mu u v ∧
      (cylinderEnergy S b u v / b) ^ 2 ≤
        2 * (‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 + S.mu u v ^ 2) ∧
      S.m u v / b = S.mu u v / 2 ∧
      S.m u v / b ≤ cylinderEnergy S b u v / b := by
  let y := ‖S.theta u v / (S.lam u v : ℂ)‖
  let μ := S.mu u v
  let q := cylinderEnergy S b u v / b
  have hyn : 0 ≤ y := norm_nonneg _
  have hy : y ≤ 1 / 2 := by dsimp only [y]; linarith
  have hμ : μ ≤ 1 / 2 := by dsimp only [μ]; linarith [norm_nonneg (S.theta u v / (S.lam u v : ℂ))]
  have hg : 0 < 1 - μ := by linarith
  have hlogup := Real.log_le_sub_one_of_pos hg
  have hloglo := Real.one_sub_inv_le_log_of_pos hg
  have hinv : (1 - μ)⁻¹ ≤ 1 + 2 * μ := by
    rw [← one_div]
    apply (div_le_iff₀ hg).2
    dsimp only [μ] at *
    nlinarith only [hmu, hμ]
  have heq : q = (y ^ 2 - Real.log (1 - μ)) / 2 := by
    dsimp only [q, y, μ]
    rw [cylinderEnergy_def]
    field_simp
  have hlo : (y ^ 2 + μ) / 2 ≤ q := by linarith
  have hqn : 0 ≤ q := by dsimp only [μ] at *; nlinarith only [hlo, hmu, sq_nonneg y]
  have hup : q ≤ y ^ 2 + μ := by nlinarith only [heq, hloglo, hinv, sq_nonneg y]
  have hysq : y ^ 2 ≤ 1 := by nlinarith only [hyn, hy]
  have hq2 : q ^ 2 ≤ 2 * (y ^ 2 + μ ^ 2) := by
    have hp := sq_le_sq₀ hqn (by dsimp only [μ]; positivity : 0 ≤ y ^ 2 + μ) |>.2 hup
    nlinarith only [hp, sq_nonneg (y ^ 2 - μ), mul_nonneg (sq_nonneg y) (sub_nonneg.mpr hysq)]
  have hm : S.m u v / b = μ / 2 := by
    dsimp only [μ]
    rw [Fields.mu, hr]
    ring
  exact ⟨hlo, hup, hq2, hm, by rw [hm]; nlinarith only [hlo, sq_nonneg y]⟩

end EmcsfAcExtension.Global.Cooling
