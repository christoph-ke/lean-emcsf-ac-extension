/- Copyright (c) 2026. All rights reserved. -/

module

public import EmcsfAcExtension.Frozen.IsSolution
public import EmcsfAcExtension.Global.Defs.Interaction
import EmcsfAcExtension.Global.Calculus.Endpoint
import EmcsfAcExtension.Global.Interaction.PairKernel
import EmcsfAcExtension.Global.Interaction.PairSource
import EmcsfAcExtension.Global.Interaction.RadialY
import Mathlib.Tactic

/-!
# Incoming connector clock and final boundary kernel

These are the exact geometric steps of the connector comparison at
`charged_SF_new_version.tex:L3695–L3704` and internal project record's connector-geometry formula.
The
clock is obtained from the frozen incoming radius equation. The full three
source comparisons additionally require the radial source reconstruction.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Global.InteractionEstimate

private theorem outgoing_radius_le {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v s : ℝ} (huv : u ≤ v) (hvs : v ≤ s)
    (hs : outSeg u v s ⊆ D) : S.r u v ≤ S.r u s := by
  have he := (Calculus.out_integralForm hS huv hvs hs).1.2
  have hp : 0 ≤ ∫ w in v..s, S.lam u w :=
    intervalIntegral.integral_nonneg hvs (fun w hw =>
      (hS.lam_pos (u, w) (hs ⟨rfl, hw.1, hw.2⟩)).le)
  rw [← he] at hp
  exact sub_nonneg.mp hp

end EmcsfAcExtension.Global.InteractionEstimate

namespace EmcsfAcExtension.Global.InteractionEstimate

/-- [internal]
The incoming boundary Cauchy--Schwarz kernel over any measurable portion
of a stage with radii in `[ρB,B]`. Its exact coefficient is `1/ρ`, uniform
in stage radius, solution, label, and duration. The expansion ratio is
derived from the stops before cancellation; no connectedness is assumed.
For a constant-radius cylinder take `ρ = 1`.
Source: charged_SF_new_version.tex:L3692–L3704; internal project record `(K1)`. -/
theorem stage_incoming_boundary_kernel {e δ c Λ F ε : ℝ} {S : Fields}
    {D : Set (ℝ × ℝ)} (hS : IsSolution e S D)
    (hstop : ExteriorStops S D δ c Λ F ε) {a b s ρ B : ℝ}
    (hab : a ≤ b) (hbs : b ≤ s) (hin : inSeg a b s ⊆ D)
    {U : Set ℝ} (hU : MeasurableSet U) (hsub : U ⊆ Icc a b)
    (hρ : 0 < ρ) (hB : 0 < B) (vb : ℝ → ℝ)
    (hrows : ∀ u ∈ U, u < vb u ∧ vb u ≤ s ∧ outSeg u (vb u) s ⊆ D)
    (hrange : ∀ u ∈ U, ρ * B ≤ S.r u (vb u) ∧ S.r u (vb u) ≤ B) :
    (∫⁻ u in U, ENNReal.ofReal
      (S.r u (vb u) * (-S.nu u (vb u)) / S.r u s ^ 2)) ≤ ENNReal.ofReal ρ⁻¹ := by
  have hpoint (u : ℝ) (hu : u ∈ U) :
      S.r u (vb u) * (-S.nu u (vb u)) / S.r u s ^ 2 ≤
        B * ((-S.nu u s) / S.r u s ^ 2) := by
    obtain ⟨huv, hvs, hs⟩ := hrows u hu
    have hn := neg_pos.mpr (hS.nu_neg (u, vb u) (hs ⟨rfl, le_rfl, hvs⟩))
    have hns := neg_pos.mpr (hS.nu_neg (u, s) (hs ⟨rfl, hvs, le_rfl⟩))
    have hexp := (Interaction.radial_expansion_control hS hstop huv hvs hs).2.1
    have hnu : -S.nu u (vb u) ≤ -S.nu u s := by
      simpa only [one_mul] using (le_div_iff₀ hn).mp hexp
    have hprod := mul_le_mul (hrange u hu).2 hnu hn.le hB.le
    exact (div_le_div_of_nonneg_right hprod (sq_nonneg _)).trans_eq (by ring)
  have hradius (u : ℝ) (hu : u ∈ U) : ρ * B ≤ S.r u s := by
    obtain ⟨huv, hvs, hs⟩ := hrows u hu
    exact (hrange u hu).1.trans
      ((outgoing_radius_calculus hS huv.le hvs hs).2.monotoneOn
        ⟨le_rfl, hvs⟩ ⟨hvs, le_rfl⟩ hvs)
  calc
    _ ≤ ∫⁻ u in U, ENNReal.ofReal B * ENNReal.ofReal ((-S.nu u s) / S.r u s ^ 2) := by
      apply setLIntegral_mono' hU
      intro u hu
      rw [← ENNReal.ofReal_mul hB.le]
      exact ENNReal.ofReal_le_ofReal (hpoint u hu)
    _ = ENNReal.ofReal B * ∫⁻ u in U, ENNReal.ofReal ((-S.nu u s) / S.r u s ^ 2) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal B * ENNReal.ofReal (1 / (ρ * B)) := by
      gcongr
      exact incoming_inverse_square_kernel hS hab hbs hin hU hsub (mul_pos hρ hB) hradius
    _ = _ := by
      rw [← ENNReal.ofReal_mul hB.le]
      congr 1
      field_simp

private theorem boundary_power_factor {r R ε : ℝ} (hr : 0 < r) (hR : 0 < R) :
    r ^ 3 * (R / r) ^ ε / R ^ 4 = r ^ (3 - ε) * R ^ (ε - 4) := by
  rw [Real.div_rpow hR.le hr.le, Real.rpow_sub hr, Real.rpow_sub hR]
  have hr3 : r ^ (3 : ℝ) = r ^ (3 : ℕ) := Real.rpow_natCast r 3
  have hR4 : R ^ (4 : ℝ) = R ^ (4 : ℕ) := Real.rpow_natCast R 4
  simp only [hr3, hR4, div_eq_mul_inv]
  ring

/-- [internal]
The source/boundary curvature Cauchy--Schwarz kernel on an arbitrary
measurable stage history. The coefficient is exactly
`ρ^(ε-3)/(3-ε)`, depending only on fixed `ρ,ε`, uniformly in radius,
fields, labels, and duration. A cylinder has the source coefficient
`1/(3-ε)` by taking `ρ = 1`; connectors have the stated fixed-ratio loss.
Source: charged_SF_new_version.tex:L3679–L3686; internal project record `(K3)`. -/
theorem stage_source_boundary_kernel {e δ c Λ F ε : ℝ} {S : Fields}
    {D : Set (ℝ × ℝ)} (hS : IsSolution e S D)
    (hstop : ExteriorStops S D δ c Λ F ε) {a b s ρ B : ℝ}
    (hab : a ≤ b) (hbs : b ≤ s) (hin : inSeg a b s ⊆ D)
    {U : Set ℝ} (hU : MeasurableSet U) (hsub : U ⊆ Icc a b)
    (hρ : 0 < ρ) (hB : 0 < B) (hε : ε < 3) (vb : ℝ → ℝ)
    (hrows : ∀ u ∈ U, u < vb u ∧ vb u ≤ s ∧ outSeg u (vb u) s ⊆ D)
    (hrange : ∀ u ∈ U, ρ * B ≤ S.r u (vb u) ∧ S.r u (vb u) ≤ B) :
    (∫⁻ u in U, ENNReal.ofReal
      (S.r u (vb u) ^ 3 / S.r u s ^ 4 *
        ((-S.nu u s) / (-S.nu u (vb u))) ^ 2 * (-S.nu u (vb u)))) ≤
      ENNReal.ofReal (ρ ^ (ε - 3) / (3 - ε)) := by
  have hpoint (u : ℝ) (hu : u ∈ U) :
      S.r u (vb u) ^ 3 / S.r u s ^ 4 *
        ((-S.nu u s) / (-S.nu u (vb u))) ^ 2 * (-S.nu u (vb u)) ≤
      B ^ (3 - ε) * ((-S.nu u s) * S.r u s ^ (ε - 4)) := by
    obtain ⟨huv, hvs, hs⟩ := hrows u hu
    have hr := hS.r_pos (u, vb u) (hs ⟨rfl, le_rfl, hvs⟩) huv
    have hR := hS.r_pos (u, s) (hs ⟨rfl, hvs, le_rfl⟩) (huv.trans_le hvs)
    have hn := neg_pos.mpr (hS.nu_neg (u, vb u) (hs ⟨rfl, le_rfl, hvs⟩))
    have hN := neg_pos.mpr (hS.nu_neg (u, s) (hs ⟨rfl, hvs, le_rfl⟩))
    have hexp := (Interaction.radial_expansion_control hS hstop huv hvs hs).2.2
    calc
      _ = (-S.nu u s) * (S.r u (vb u) ^ 3 / S.r u s ^ 4) *
          ((-S.nu u s) / (-S.nu u (vb u))) := by field_simp
      _ ≤ (-S.nu u s) * (S.r u (vb u) ^ 3 / S.r u s ^ 4) *
          (S.r u s / S.r u (vb u)) ^ ε :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = S.r u (vb u) ^ (3 - ε) * ((-S.nu u s) * S.r u s ^ (ε - 4)) := by
        calc
          _ = (-S.nu u s) *
              (S.r u (vb u) ^ 3 * (S.r u s / S.r u (vb u)) ^ ε / S.r u s ^ 4) := by ring
          _ = _ := by rw [boundary_power_factor hr hR]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hr.le (hrange u hu).2 (sub_pos.mpr hε).le) (by positivity)
  have hradius (u : ℝ) (hu : u ∈ U) : ρ * B ≤ S.r u s := by
    obtain ⟨huv, hvs, hs⟩ := hrows u hu
    exact (hrange u hu).1.trans
      ((outgoing_radius_calculus hS huv.le hvs hs).2.monotoneOn
        ⟨le_rfl, hvs⟩ ⟨hvs, le_rfl⟩ hvs)
  calc
    _ ≤ ∫⁻ u in U, ENNReal.ofReal (B ^ (3 - ε)) *
        ENNReal.ofReal ((-S.nu u s) * S.r u s ^ (ε - 4)) := by
      apply setLIntegral_mono' hU
      intro u hu
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hB.le _)]
      exact ENNReal.ofReal_le_ofReal (hpoint u hu)
    _ = ENNReal.ofReal (B ^ (3 - ε)) *
        (∫⁻ u in U, ENNReal.ofReal ((-S.nu u s) * S.r u s ^ (ε - 4))) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (B ^ (3 - ε)) *
        ENNReal.ofReal ((ρ * B) ^ ((ε - 4) + 1) / (-(ε - 4) - 1)) := by
      gcongr
      exact incoming_power_tail hS hab hbs hin hU hsub (mul_pos hρ hB)
        (by linarith only [hε]) hradius
    _ = _ := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hB.le _)]
      congr 1
      rw [show ε - 4 + 1 = ε - 3 by ring, show -(ε - 4) - 1 = 3 - ε by ring,
        Real.mul_rpow hρ.le hB.le]
      have hh : B ^ (3 - ε) * B ^ (ε - 3) = 1 := by
        rw [← Real.rpow_add hB, show 3 - ε + (ε - 3) = 0 by ring, Real.rpow_zero]
      calc
        _ = (B ^ (3 - ε) * B ^ (ε - 3)) * (ρ ^ (ε - 3) / (3 - ε)) := by ring
        _ = _ := by rw [hh, one_mul]

end EmcsfAcExtension.Global.InteractionEstimate

namespace EmcsfAcExtension.Global.InteractionEstimate

/-- [internal]
Cauchy--Schwarz for nonnegative square factors, including zero budgets.
The exact coefficient is one, uniformly in the measure and densities.
Consumers supply the literal pointwise factorization and prove both
square-moment bounds from the field budget and geometric radius kernel. -/
theorem lintegral_cauchy_of_square_factorization {U : Set ℝ}
    (hU : MeasurableSet U) (h f g : ℝ → ℝ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : AEMeasurable (fun u => ENNReal.ofReal (f u)) (volume.restrict U))
    (hg : AEMeasurable (fun u => ENNReal.ofReal (g u)) (volume.restrict U))
    (hpoint : ∀ u ∈ U, 0 ≤ h u ∧ 0 ≤ f u ∧ 0 ≤ g u ∧ h u ^ 2 = f u * g u)
    (hif : (∫⁻ u in U, ENNReal.ofReal (f u)) ≤ ENNReal.ofReal A)
    (hig : (∫⁻ u in U, ENNReal.ofReal (g u)) ≤ ENNReal.ofReal B) :
    (∫⁻ u in U, ENNReal.ofReal (h u)) ≤ ENNReal.ofReal (Real.sqrt A * Real.sqrt B) := by
  calc
    _ = ∫⁻ u in U, ENNReal.ofReal (f u) ^ (1 / 2 : ℝ) *
        ENNReal.ofReal (g u) ^ (1 / 2 : ℝ) := by
      apply setLIntegral_congr_fun hU
      intro u hu
      obtain ⟨hh, hf0, hg0, heq⟩ := hpoint u hu
      change ENNReal.ofReal (h u) = ENNReal.ofReal (f u) ^ (1 / 2 : ℝ) *
        ENNReal.ofReal (g u) ^ (1 / 2 : ℝ)
      rw [ENNReal.ofReal_rpow_of_nonneg hf0 (by norm_num),
        ENNReal.ofReal_rpow_of_nonneg hg0 (by norm_num), ← Real.sqrt_eq_rpow,
        ← Real.sqrt_eq_rpow, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
        ← Real.sqrt_mul hf0, ← heq, Real.sqrt_sq hh]
    _ ≤ (∫⁻ u in U, ENNReal.ofReal (f u)) ^ (1 / 2 : ℝ) *
        (∫⁻ u in U, ENNReal.ofReal (g u)) ^ (1 / 2 : ℝ) :=
      ENNReal.lintegral_mul_norm_pow_le hf hg (by norm_num) (by norm_num) (by norm_num)
    _ ≤ ENNReal.ofReal A ^ (1 / 2 : ℝ) * ENNReal.ofReal B ^ (1 / 2 : ℝ) := by
      gcongr
    _ = _ := by
      rw [ENNReal.ofReal_rpow_of_nonneg hA (by norm_num),
        ENNReal.ofReal_rpow_of_nonneg hB (by norm_num), ← Real.sqrt_eq_rpow,
        ← Real.sqrt_eq_rpow, ENNReal.ofReal_mul (Real.sqrt_nonneg _)]

end EmcsfAcExtension.Global.InteractionEstimate
