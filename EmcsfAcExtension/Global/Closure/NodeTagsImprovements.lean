module

public import EmcsfAcExtension.Global.Closure.NodeTagsFinite
import EmcsfAcExtension.Global.Closure.Optics
import EmcsfAcExtension.Global.Closure.StageSums
import EmcsfAcExtension.Global.Closure.Continuation
import Mathlib.Tactic

/-! # Optical, scalar and mass improvements from stopped stage energies

The incoming optical supremum is strictly below `log 2`. The same parameter
choice improves the scalar/mass stops and compares the boundary and terminal
clocks. The actual field budgets are produced inside the proof.
Source: `charged_SF_new_version.tex:L4061–L4072`.
-/

public section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace EmcsfAcExtension.Global

/-- [node eq:cc-optics]
The exact quantitative incoming optical bound, strictly below `log 2`,
from an available finite stopped prefix and its propagated stage energies.
The observation thresholds depend only on `δ`; all remaining constants
and the small stop/entry tolerance depend only on the fixed geometric,
recurrence and stopping parameters, before physical data, scales, stage
number and duration. Both strict field improvements are retained, as is
clock comparison when the entry expansion margin holds.
Source: charged_SF_new_version.tex:L4061–L4072. -/
theorem cc_optics (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    ∃ Ts δs ηs : ℝ, 0 < Ts ∧ 0 < δs ∧ 0 < ηs ∧
      ∀ (εweak ρ χ C₁ c Λ F : ℝ),
      ExteriorBox δ c Λ F εweak ρ → 0 < ρ →
      0 ≤ χ → χ < 1 → 0 ≤ C₁ → F + εweak ≤ δs → 0 < F → 0 < εweak →
      ∃ Cbudget Csum C η : ℝ, 0 < Cbudget ∧ 0 < Csum ∧ 0 < C ∧ 0 < η ∧
      ∀ (ui e : ℝ) (S : Fields), OriginalData ui e S → SignedTerminalBound ui S →
      ∃ a ∈ Ioo ui 0,
      ∀ (u₀ u₁ v₀ R₀ εentry : ℝ) (vb : ℝ → ℝ) (σ : ℕ → ℝ)
        (N : ℕ) (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) (T : Fin N → ℝ),
      a ≤ u₀ → 0 < N → 0 ≤ εentry → (∀ n, 0 ≤ σ n) →
      ExteriorStops S (exteriorDomain ui u₀ u₁ vb) δ c Λ F εweak →
      S.r u₀ 0 = R₀ → (∀ u ∈ Icc u₀ u₁, R₀ / 2 ≤ S.r u 0) →
      (∀ p ∈ origDomain ui, u₀ ≤ p.1 → 0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) →
      (∀ n, B.radii n < R₀ / 2) → (∀ n, 0 < T n) →
      ∀ γ : ∀ n, ClockCylinder S (origDomain ui) (B.radii n) 0 (T n),
      (∀ n, (γ n).U 0 = B.cuts n.castSucc ∧ (γ n).U (T n) = B.cool n) →
      (∀ n, ∀ τ ∈ Icc 0 (T n), vb ((γ n).U τ) = (γ n).V τ) →
      (∀ n : Fin N, σ n = (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal) →
      (∀ n, cylinderEnergy S (B.radii n) ((γ n).U 0) ((γ n).V 0) / B.radii n ≤
        energyEnvelope χ C₁ εentry σ n) →
      let J := (interactionNorm e S (exteriorDomain ui u₀ u₁ vb) u₀ v₀).toReal
      let V := ∑ n ∈ Finset.range N, σ n
      let z := Local.sigma e (Interaction.scalarBackground ui R₀ c F η S) (2 * R₀)
      J + V ≤ η → εentry ≤ η → z ≤ η →
      (⨆ v ∈ Icc v₀ 0, ∫⁻ u in {u | (u, v) ∈ exteriorDomain ui u₀ u₁ vb},
        ENNReal.ofReal (positiveExpIntegrand S u v)) ≤
          ENNReal.ofReal (C * (εentry + V ^ 2 + J ^ 2 + z)) ∧
      C * (εentry + V ^ 2 + J ^ 2 + z) < Real.log 2 ∧
      (∀ p ∈ exteriorDomain ui u₀ u₁ vb,
        ‖S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ)‖ < F ∧
        S.mu p.1 p.2 / (1 - S.mu p.1 p.2) < εweak) ∧
      ((∀ v ∈ Icc v₀ 0, 2 * c ≤ S.lam u₀ v) →
        (∀ p ∈ exteriorDomain ui u₀ u₁ vb,
          0 ≤ signedExpIntegrand S p.1 p.2 ∧
          signedExpIntegrand S p.1 p.2 ≤ positiveExpIntegrand S p.1 p.2 ∧
          c < S.lam p.1 p.2) ∧
        ∀ u ∈ Icc u₀ u₁, (-S.nu u 0) / (-S.nu u (vb u)) < 2) := by
  obtain ⟨Ts, δs, ηs, hTs, hδs, hηs, hbud⟩ :=
    Closure.stopped_boundary_budgets_of_initial_energies δ hδ
  refine ⟨Ts, δs, ηs, hTs, hδs, hηs, ?_⟩
  intro εweak ρ χ C₁ c Λ F hbox hρ hχ hχ1 hC₁ hweak hF hεweak
  obtain ⟨Cb, hCb, hbud⟩ := hbud εweak ρ hεweak.le hρ
  obtain ⟨Csum, hCs, hsums⟩ := Closure.finite_stage_sums χ C₁ Cb ⟨hχ, hχ1⟩ hC₁ hCb.le
  obtain ⟨Co, hCo, hopt⟩ :=
    Closure.stopped_optics_of_budgets δ c Λ F εweak ρ Csum hbox hCs.le
  obtain ⟨Ce, hCe, hexp⟩ :=
    Closure.expansion_clock_improvement_of_budgets δ c Λ F εweak ρ hbox
  obtain ⟨ηfield, hηfield, hfields⟩ := Closure.scalar_mass_improvement_of_budgets c F εweak
    hbox.2.2.1 hF hbox.2.2.2.2.2.1 hεweak
  let C := Co + Ce
  have hC : 0 < C := add_pos hCo hCe
  have hCoC : Co ≤ C := le_add_of_nonneg_right hCe.le
  have hCeC : Ce ≤ C := le_add_of_nonneg_left hCo.le
  let Q := fun t : ℝ => Csum * (t + t ^ 2)
  let P := fun t : ℝ => C * ((Csum + 1) * (t + t ^ 2) + t ^ 2 + t)
  have hQc : ContinuousAt Q 0 := by dsimp [Q]; fun_prop
  have hPc : ContinuousAt P 0 := by dsimp [P]; fun_prop
  have hOc : ContinuousAt (fun t : ℝ => 9 * t) 0 := by fun_prop
  have hQF : Q 0 < F ^ 2 := by simpa [Q] using sq_pos_of_pos hF
  have hQfield : Q 0 < ηfield := by simpa [Q] using hηfield
  have hPlog : P 0 < Real.log 2 := by simpa [P] using Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hevent : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 < t ∧ t < 1 ∧ t < ηfield ∧ 9 * t < ηs ^ 2 ∧
      Q t < F ^ 2 ∧ Q t < ηfield ∧ P t < Real.log 2 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      nhdsWithin_le_nhds (Iio_mem_nhds hηfield),
      (hOc.tendsto.mono_left nhdsWithin_le_nhds).eventually
        (Iio_mem_nhds (by simpa using sq_pos_of_pos hηs)),
      (hQc.tendsto.mono_left nhdsWithin_le_nhds).eventually (Iio_mem_nhds hQF),
      (hQc.tendsto.mono_left nhdsWithin_le_nhds).eventually (Iio_mem_nhds hQfield),
      (hPc.tendsto.mono_left nhdsWithin_le_nhds).eventually (Iio_mem_nhds hPlog)]
      with t ht h1 hf ho hqf hqfield hp
    exact ⟨ht, h1, hf, ho, hqf, hqfield, hp⟩
  obtain ⟨η, hη, hη1, hηf, hηobs, hQFη, hQfieldη, hPη⟩ := hevent.exists
  refine ⟨Cb, Csum, C, η, hCb, hCs, hC, hη, ?_⟩
  intro ui e S h hs
  obtain ⟨ao, hao, hopt⟩ := hopt ui e S h hs η
  obtain ⟨ae, hae, hexp⟩ := hexp ui e S h hs η
  obtain ⟨af, haf, hfields⟩ := hfields ui e S h hs η
  refine ⟨max ao (max ae af), ⟨hao.1.trans_le (le_max_left _ _),
    max_lt hao.2 (max_lt hae.2 haf.2)⟩, ?_⟩
  intro u₀ u₁ v₀ R₀ εentry vb σ N B T hau hN he hσ hstop hR₀ hhalf hgap hradii hT
    γ hends hgraph hσeq hinit
  dsimp only
  let J := (interactionNorm e S (exteriorDomain ui u₀ u₁ vb) u₀ v₀).toReal
  let V := ∑ n ∈ Finset.range N, σ n
  let z := Local.sigma e (Interaction.scalarBackground ui R₀ c F η S) (2 * R₀)
  intro hsmall heη hzη
  have hJ0 : 0 ≤ J := ENNReal.toReal_nonneg
  have hV0 : 0 ≤ V := Finset.sum_nonneg (fun n _ => hσ n)
  have hz0 : 0 ≤ z := by dsimp [z, Local.sigma]; positivity
  have hJη : J ≤ η := by linarith only [hsmall, hV0]
  have hVη : V ≤ η := by linarith only [hsmall, hJ0]
  have hJsq : J ^ 2 ≤ η ^ 2 := (sq_le_sq₀ hJ0 hη.le).mpr hJη
  have hVsq : V ^ 2 ≤ η ^ 2 := (sq_le_sq₀ hV0 hη.le).mpr hVη
  have hE := hbud χ C₁ εentry c Λ F ui e u₀ u₁ v₀ η R₀ S vb σ N B T
    hχ hC₁ he hη.le hweak h hbox hstop hR₀ hhalf hJη hgap hradii
    (fun n => (hT n).le) γ hends hgraph hσeq hinit (hzη.trans hη1.le)
    ((mul_le_mul_of_nonneg_left hzη (by norm_num)).trans hηobs.le)
  let E := fun n : Fin N => stageBudget Cb χ C₁ εentry σ n
  have hsum : (∑ n, E n) ≤ Csum * (εentry + V ^ 2) := by
    simpa only [E, V, ← Fin.sum_univ_eq_sum_range] using (hsums εentry σ N he hσ).1
  have hsumQ : (∑ n, E n) ≤ Q η :=
    hsum.trans (mul_le_mul_of_nonneg_left (add_le_add heη hVsq) hCs.le)
  have hsum0 : 0 ≤ ∑ n, E n := Finset.sum_nonneg (fun n _ => (hE n).1)
  have hEF := hsumQ.trans hQFη.le
  have hmass (u : ℝ) (hu : u ∈ Icc u₀ u₁) : S.m u (vb u) / S.r u (vb u) ≤ F ^ 2 := by
    have hh := (Closure.boundary_budget_le_sum B hN E hE hu).trans hEF
    linarith only [hh, sq_nonneg ‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖]
  have hao' := (le_max_left ao (max ae af)).trans hau
  have hae' := ((le_max_left ae af).trans (le_max_right ao (max ae af))).trans hau
  have haf' := ((le_max_right ae af).trans (le_max_right ao (max ae af))).trans hau
  have ho := hopt u₀ u₁ v₀ R₀ εentry V vb (fun _ => F ^ 2) N B E hao' he hstop hR₀ hhalf hJη
    (fun u hu => ⟨hmass u hu, le_rfl⟩) hE hsum
  have hnum : C * (εentry + V ^ 2 + J ^ 2 + z) < Real.log 2 := by
    apply lt_of_le_of_lt ?_ hPη
    dsimp only [P]
    have hnonneg : 0 ≤ η + η ^ 2 := by positivity
    have hcompare := mul_nonneg hCs.le hnonneg
    nlinarith only [heη, hVsq, hJsq, hzη,
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add heη hVsq) hJsq) hzη) hC.le,
      mul_nonneg hC.le hcompare]
  refine ⟨ho.1.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hCoC (by positivity))), hnum, ?_, ?_⟩
  · exact hfields u₀ u₁ v₀ R₀ δ Λ ρ vb N B E haf' hN hbox hstop hR₀ hhalf hJη hE
      (hsumQ.trans hQfieldη.le) (hJη.trans hηf.le) (hzη.trans hηf.le)
  · intro hentry
    have hcore (u : ℝ) (hu : u ∈ Icc u₀ u₁) (w : ℝ) (hw : w ∈ Icc u 0) :
        δ ≤ 1 - S.mu u w :=
      (hgap (u, w) ⟨(B.mem u hu).1, (B.mem u hu).2.1, hw⟩ hu.1).2
    have hexpsmall : Ce * ((∑ n, E n) + J ^ 2 + z) < Real.log 2 := by
      apply lt_of_le_of_lt ?_ hPη
      have hcoef := mul_le_mul_of_nonneg_right hCeC
        (show 0 ≤ (∑ n, E n) + J ^ 2 + z by positivity)
      apply hcoef.trans
      apply mul_le_mul_of_nonneg_left _ hC.le
      dsimp only [P, Q] at *
      nlinarith only [hsumQ, hJsq, hzη, hη.le, sq_nonneg η]
    obtain ⟨hexpansion, hratio⟩ := hexp u₀ u₁ v₀ R₀ vb N B E hae' hN hstop hR₀ hhalf
      hJη hE hEF hentry hexpsmall
    refine ⟨?_, hratio⟩
    intro p hp
    have hr := h.solution.r_pos p hp.1
      ((B.off_axis p.1 ⟨hp.2.1, hp.2.2.1⟩).trans_le hp.2.2.2)
    have hn := h.solution.nu_neg p hp.1
    have hg := h.solution.one_sub_mu_pos p hp.1
    have hq := (hstop p hp).2.2.2.2.2.2
    have hmu := (hstop p hp).1
    have hq' : S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 ≤ S.mu p.1 p.2 := by
      linarith only [hq, hmu]
    have hsigned := Closure.signed_exponent_bounds hr hn hg hq'
    exact ⟨hsigned.1, hsigned.2, hexpansion p hp⟩

end EmcsfAcExtension.Global
