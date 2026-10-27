module

public import EmcsfAcExtension.Local.Defs.Envelope
public import EmcsfAcExtension.Local.Defs.C1Class
public import EmcsfAcExtension.Local.Defs.Params
import EmcsfAcExtension.Local.Limit.Construct2Axis
import EmcsfAcExtension.Local.Limit.Construct2Cauchy
import EmcsfAcExtension.Local.Construction.WireC1Bound
import EmcsfAcExtension.Local.Stability.ExtendedLipschitz

/-! # Unconditional common AC axis trace

Same-label comparison supplies the incoming mixed Cauchy estimate for actual
full-triangle approximants. Their zero axis gauge identifies the diagonal
density with the ordinary derivative. W¹¹ completeness supplies the common
AC trace and fixes its primitive constant at the datum's vertex value.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

/-- [internal]
The diagonal density difference is bounded by the incoming mixed difference,
with coefficient one, uniformly in time, coupling and fields. Continuity and
the zero axis gauge identify these densities with the approximants' diagonal
derivatives in the constructed-trace theorem below, charged_SF_new_version.tex:L6453–L6459. -/
theorem Null.axis_density_difference_le {e T : ℝ} {S₁ S₂ : Fields} :
    (∫⁻ t in Icc 0 T,
      ‖kC1 e (triangle 0 T) S₁ t t - kC1 e (triangle 0 T) S₂ t t‖ₑ) ≤
        kDist e T S₁ S₂ := by
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact le_iSup₂_of_le t ⟨le_rfl, ht.2⟩ le_rfl

/-- [node restart-sec-independent-null-construction#axis-strong-ac-limit]
Construct full-triangle approximants and their common AC diagonal limit,
including L¹-Cauchy diagonal densities and strong convergence to the actual
trace derivative, charged_SF_new_version.tex:L6453–L6459. Both positive thresholds are
universal, before time, coupling, AC datum and approximation derivatives.
The trace starts at `h 0`; all three scalar axis traces converge to it. -/
theorem Null.axis_strong_ac_limit :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      ∀ (T e : ℝ) (h : ℝ → ℂ), 0 < T →
        AbsolutelyContinuousOnInterval h 0 T → datumVar h T ≤ ε →
        chargedScale e h T ≤ δ →
        ∃ (hn : ℕ → ℝ → ℂ) (Sn : ℕ → Fields) (psi : ℝ → ℂ),
          (∀ n, ContDiffOn ℝ 1 (hn n) (Icc 0 T)) ∧ (∀ n, hn n 0 = h 0) ∧
          Tendsto (fun n => eVariationOn (hn n - h) (Icc 0 T)) atTop (𝓝 0) ∧
          (∀ n, IsC1Solution e (Sn n) (triangle 0 T) ∧ IsRestartData (Sn n) (hn n) T) ∧
          (∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
            (∫⁻ t in Icc 0 T,
              ‖kC1 e (triangle 0 T) (Sn n) t t - kC1 e (triangle 0 T) (Sn m) t t‖ₑ) <
                ENNReal.ofReal ρ) ∧
          AbsolutelyContinuousOnInterval psi 0 T ∧ psi 0 = h 0 ∧
          TendstoUniformlyOn (fun n t => (Sn n).phi t t) psi atTop (Icc 0 T) ∧
          TendstoUniformlyOn (fun n t => (Sn n).a t t) psi atTop (Icc 0 T) ∧
          TendstoUniformlyOn (fun n t => (Sn n).b t t) psi atTop (Icc 0 T) ∧
          ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N,
            (∫ t in (0 : ℝ)..T, ‖kC1 e (triangle 0 T) (Sn n) t t - deriv psi t‖) < ρ := by
  obtain ⟨η, hη, hc⟩ := Null.same_label_mixed_cauchy_of_inputs stab_extended 1 (by norm_num)
  obtain ⟨ε, δ, q, hε, hδ, _, happ⟩ :=
    Null.comparison_approximants_of_inputs whole_triangle_existence η hη
  refine ⟨ε, δ, hε, hδ, ?_⟩
  intro T e h hT hac hsmall hscale
  obtain ⟨hn, Sn, hs, hv, herr, hevar, _, hset, hcomparison⟩ :=
    happ T e h hT hac hsmall hscale
  have hC := hc T e q (2 * datumM h T) Sn hn h hset hac hv herr hcomparison
  have hk : ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      kDist e T (Sn n) (Sn m) < ENNReal.ofReal ρ := by
    intro ρ hρ
    obtain ⟨N, hN⟩ := hC ρ hρ
    exact ⟨N, fun n hn' m hm' => le_add_self.trans_lt (hN n hn' m hm')⟩
  have hz n : (Sn n).phi 0 0 = h 0 := by
    have hp : (0, 0) ∈ triangle 0 T := ⟨le_rfl, le_rfl, hT.le⟩
    exact ((hset n).c1.axis 0 hp).2.2.2.2.1.symm.trans
      (((hset n).data.1 0 ⟨le_rfl, hT.le⟩).2.trans (hv n))
  obtain ⟨psi, hp, hp0, hu, hua, hub, hd⟩ := Null.axis_trace_of_mixed_cauchy hT
    (fun n => (hset n).c1) (fun n => (hset n).data.2) hz hk
  refine ⟨hn, Sn, psi, hs, hv, hevar, fun n => ⟨(hset n).c1, (hset n).data⟩,
    ?_, hp, hp0, hu, hua, hub, hd⟩
  intro ρ hρ
  obtain ⟨N, hN⟩ := hk ρ hρ
  exact ⟨N, fun n hn' m hm' => Null.axis_density_difference_le.trans_lt (hN n hn' m hm')⟩

end EmcsfAcExtension.Local
