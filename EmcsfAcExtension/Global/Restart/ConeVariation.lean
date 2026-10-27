module

public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Defs.Stages
import EmcsfAcExtension.Global.Calculus.Normalized
import EmcsfAcExtension.Global.Terminal.Mass
import EmcsfAcExtension.Infra.BV.Semicontinuity
import EmcsfAcExtension.Infra.Sequence.EnergyRecurrence

/-! # Boundary decay and variation on the limiting complete cone

Summable budgets control all cylinder and connector pieces. Pointwise
continuity and variation semicontinuity then give only the variation bound;
closed-cone AC is proved separately in `ConeAC`.
Source: charged_SF_new_version.tex:L4122–4131.
-/

public section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global.Restart

/-- [internal] The actual recursive energy envelopes and boundary variation
errors tend to zero when the latter have uniformly bounded nonnegative
finite sums. The recurrence coefficients precede all sequences and entry
energies. This supplies the `ε_n,σ_n` part of charged_SF_new_version.tex:L4122–4124. -/
theorem energyEnvelope_decay_of_closure (χ C : ℝ) (hχ : 0 ≤ χ ∧ χ < 1)
    (hC : 0 ≤ C) {ε₀ L : ℝ} (he : 0 ≤ ε₀) (σ : ℕ → ℝ)
    (hσ : ∀ n, 0 ≤ σ n) (hsum : ∀ N, ∑ n ∈ Finset.range N, σ n ≤ L) :
    Tendsto (energyEnvelope χ C ε₀ σ) atTop (𝓝 0) ∧ Tendsto σ atTop (𝓝 0) := by
  have ha (n : ℕ) : 0 ≤ energyEnvelope χ C ε₀ σ n := by
    induction n with
    | zero => exact he
    | succ n ih => exact add_nonneg (mul_nonneg hχ.1 ih) (mul_nonneg hC (sq_nonneg _))
  have hL : 0 ≤ L := by simpa using hsum 0
  have hbound (N : ℕ) : ∑ n ∈ Finset.range N, energyEnvelope χ C ε₀ σ n ≤
      (ε₀ + C * L ^ 2) / (1 - χ) := by
    have hh := (energy_sums_le_of_le_recurrence hχ.1 hχ.2 hC
      (energyEnvelope χ C ε₀ σ) σ N (fun n _ => ha n)
      (fun n _ => hσ n) (fun n _ => le_rfl)).1
    have hn : 0 ≤ ∑ n ∈ Finset.range N, σ n := Finset.sum_nonneg (fun n _ => hσ n)
    have hsq : (∑ n ∈ Finset.range N, σ n) ^ 2 ≤ L ^ 2 := by
      nlinarith only [hsum N, hn, hL]
    exact hh.trans (div_le_div_of_nonneg_right
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hsq hC)) (sub_pos.mpr hχ.2).le)
  exact ⟨(summable_of_sum_range_le ha hbound).tendsto_atTop_zero,
    (summable_of_sum_range_le hσ hsum).tendsto_atTop_zero⟩

/-- [internal] The supremum part of a finite boundary budget bounds the
scalar ratio everywhere in its stage, including its connector. The coefficient
is exactly one, independent of all fields, stages and durations. -/
theorem boundary_scalar_norm_le_sqrt_of_budget (ui e : ℝ) (S : Fields)
    (h : OriginalData ui e S) {u₀ u₁ v₀ ρ : ℝ} {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) (E : Fin N → ℝ)
    (hE : BoundaryBudgets S ui u₀ u₁ v₀ ρ vb N B E)
    (i : Fin N) {u : ℝ} (hu : u ∈ Icc (B.cuts i.castSucc) (B.cuts i.succ)) :
    ‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖ ≤ Real.sqrt (E i) := by
  have hleft : u₀ ≤ B.cuts i.castSucc := B.first.ge.trans (B.ordered (Fin.zero_le _))
  have hright : B.cuts i.succ ≤ u₁ := (B.ordered (Fin.le_last _)).trans B.last.le
  have hp := B.mem u ⟨hleft.trans hu.1, hu.2.trans hright⟩
  have hm := (Terminal.mass_monotonicity h.solution (u, vb u) hp).1
  have hr := h.solution.r_pos (u, vb u) hp
    (B.off_axis u ⟨hleft.trans hu.1, hu.2.trans hright⟩)
  have hh := (hE i).2.1 u hu
  exact (Real.le_sqrt (norm_nonneg _) (hE i).1).2
    (by linarith only [hh, div_nonneg hm hr.le])

/-- [internal]
Conditional support for `sec:charged-closure#boundary-scalar-decay`.
Uniform finite sums imply vanishing energies and variation errors, and
decay of the scalar ratio along every choice of points in the successive
boundary pieces. `K,L` are supplied uniform bounds, independent of the
finite cutoff; no new constant is selected (charged_SF_new_version.tex:L4122–4124). -/
theorem boundary_scalar_decay_of_closure (ui e : ℝ) (S : Fields)
    (h : OriginalData ui e S) {u₀ v₀ ρ K L : ℝ} (U : ℕ → ℝ) (vb : ℝ → ℝ)
    (B : ∀ N, FiniteBoundary S ui u₀ (U N) v₀ ρ vb N)
    (E σ : ℕ → ℝ) (hσ : ∀ n, 0 ≤ σ n)
    (hbudget : ∀ N, BoundaryBudgets S ui u₀ (U N) v₀ ρ vb N (B N)
      (fun i => E i))
    (hEsum : ∀ N, ∑ n ∈ Finset.range N, E n ≤ K)
    (hσsum : ∀ N, ∑ n ∈ Finset.range N, σ n ≤ L) :
    Tendsto E atTop (𝓝 0) ∧ Tendsto σ atTop (𝓝 0) ∧
      ∀ w : ℕ → ℝ,
        (∀ n, w n ∈ Icc ((B (n + 1)).cuts ⟨n, by omega⟩)
          ((B (n + 1)).cuts ⟨n + 1, by omega⟩)) →
        Tendsto (fun n => S.theta (w n) (vb (w n)) /
          (S.lam (w n) (vb (w n)) : ℂ)) atTop (𝓝 0) := by
  have hE (n : ℕ) : 0 ≤ E n := (hbudget (n + 1) ⟨n, by omega⟩).1
  have htE := (summable_of_sum_range_le hE hEsum).tendsto_atTop_zero
  have htσ := (summable_of_sum_range_le hσ hσsum).tendsto_atTop_zero
  refine ⟨htE, htσ, ?_⟩
  intro w hw
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) ?_
    (by simpa only [Real.sqrt_zero] using htE.sqrt)
  intro n
  exact boundary_scalar_norm_le_sqrt_of_budget ui e S h (B (n + 1))
    (fun i => E i) (hbudget (n + 1)) ⟨n, by omega⟩ (hw n)

/-- [internal] A moving exterior row bound passes to the full closed
limiting cone. The real bounds may converge rather than being uniformly
constant. This is a variation statement only; its coefficient is the given
limit `C`, independent of the sequence index (charged_SF_new_version.tex:L4124–4131). -/
theorem complete_cone_variation_of_bounds (ui e : ℝ) (S : Fields)
    (h : OriginalData ui e S) {us C : ℝ} (hus : us ∈ Ioo ui 0)
    (U V R : ℕ → ℝ) (hU : Tendsto U atTop (𝓝 us))
    (hlabel : ∀ n, ui ≤ U n ∧ U n < 0 ∧ U n ≤ V n ∧ V n ≤ us)
    (hR : Tendsto R atTop (𝓝 C))
    (hbound : ∀ n, eVariationOn (S.a (U n)) (Icc (V n) 0) ≤ ENNReal.ofReal (R n)) :
    eVariationOn (S.a us) (Icc us 0) ≤ ENNReal.ofReal C := by
  have hpoint (v : ℝ) (hv : v ∈ Icc us 0) :
      Tendsto (fun n => S.a (U n) v) atTop (𝓝 (S.a us v)) := by
    have hseq : Tendsto (fun n => (U n, v)) atTop (𝓝[origDomain ui] (us, v)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨hU.prodMk_nhds tendsto_const_nhds, Eventually.of_forall ?_⟩
      intro n
      exact ⟨(hlabel n).1, (hlabel n).2.1,
        ((hlabel n).2.2.1.trans (hlabel n).2.2.2).trans hv.1, hv.2⟩
    exact ((Calculus.continuousOn_a h.solution) (us, v)
      ⟨hus.1.le, hus.2, hv⟩).tendsto.comp hseq
  calc
    _ ≤ liminf (fun n => eVariationOn (S.a (U n)) (Icc us 0)) atTop :=
      eVariationOn.le_liminf_of_tendsto hpoint
    _ ≤ liminf (fun n => ENNReal.ofReal (R n)) atTop := by
      exact liminf_le_liminf (Eventually.of_forall (fun n =>
        (eVariationOn.mono _ (Icc_subset_Icc (hlabel n).2.2.2 le_rfl)).trans (hbound n)))
    _ = _ := (ENNReal.tendsto_ofReal hR).liminf_eq

/-- [internal]
Conditional support for `eq:cc-complete-cone`.
The radial row inequality and the uniform closed interaction estimate
give the quantitative complete-cone variation bound. The displayed
coefficient `c⁻¹ * A / (1 - F²)` depends only on fixed stopping and
absorption constants, uniformly in entry errors, stages and durations.
The vanishing boundary term is supplied by the budget theorem above.
Source: charged_SF_new_version.tex:L3994–4129, L4124–4131. -/
theorem complete_cone_variation_of_closure (c F A : ℝ) (hc : 0 < c) (hF : F ^ 2 < 1)
    (ui e : ℝ) (S : Fields) (h : OriginalData ui e S) {us D₀ ε₀ ζ₂ : ℝ}
    (hus : us ∈ Ioo ui 0)
    (U V J : ℕ → ℝ) (hU : Tendsto U atTop (𝓝 us))
    (hlabel : ∀ n, ui ≤ U n ∧ U n < 0 ∧ U n ≤ V n ∧ V n ≤ us)
    (hdecay : Tendsto (fun n => ‖S.theta (U n) (V n) /
      (S.lam (U n) (V n) : ℂ)‖) atTop (𝓝 0))
    (hclosed : ∀ n, J n ≤ A * (D₀ + ε₀ + ζ₂))
    (hrow : ∀ n, (1 - F ^ 2) *
      (eVariationOn (S.a (U n)) (Icc (V n) 0)).toReal ≤ c⁻¹ * J n +
        F ^ 2 * ‖S.theta (U n) (V n) / (S.lam (U n) (V n) : ℂ)‖) :
    eVariationOn (S.a us) (Icc us 0) ≤
      ENNReal.ofReal ((c⁻¹ * A / (1 - F ^ 2)) * (D₀ + ε₀ + ζ₂)) := by
  have hd : 0 < 1 - F ^ 2 := sub_pos.mpr hF
  apply complete_cone_variation_of_bounds ui e S h hus U V
    (fun n => (c⁻¹ * (A * (D₀ + ε₀ + ζ₂)) +
      F ^ 2 * ‖S.theta (U n) (V n) / (S.lam (U n) (V n) : ℂ)‖) /
        (1 - F ^ 2)) hU hlabel
  · have ht : Tendsto (fun n => (c⁻¹ * (A * (D₀ + ε₀ + ζ₂)) +
        F ^ 2 * ‖S.theta (U n) (V n) / (S.lam (U n) (V n) : ℂ)‖) /
          (1 - F ^ 2)) atTop
        (𝓝 ((c⁻¹ * (A * (D₀ + ε₀ + ζ₂)) + F ^ 2 * 0) / (1 - F ^ 2))) :=
      (tendsto_const_nhds.add (hdecay.const_mul (F ^ 2))).div_const (1 - F ^ 2)
    simpa only [mul_zero, add_zero, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      using ht
  · intro n
    have hs : outSeg (U n) (V n) 0 ⊆ origDomain ui := by
      rintro ⟨x, y⟩ ⟨rfl, hlow, hhigh⟩
      exact ⟨(hlabel n).1, (hlabel n).2.1, (hlabel n).2.2.1.trans hlow, hhigh⟩
    have hv : V n ≤ 0 := (hlabel n).2.2.2.trans hus.2.le
    have hfinite := (h.solution.ac_out (U n) (V n) 0 hv hs).2.2.2.2.boundedVariationOn
    rw [uIcc_of_le hv] at hfinite
    rw [← ENNReal.ofReal_toReal hfinite]
    apply ENNReal.ofReal_le_ofReal
    apply (le_div_iff₀ hd).2
    have hh := mul_le_mul_of_nonneg_left (hclosed n) (inv_nonneg.mpr hc.le)
    linarith only [hrow n, hh]

end EmcsfAcExtension.Global.Restart
