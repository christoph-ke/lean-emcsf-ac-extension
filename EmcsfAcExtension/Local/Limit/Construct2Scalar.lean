module

public import EmcsfAcExtension.Local.Limit.Construct2Cauchy
import EmcsfAcExtension.Infra.W11.Completeness
import EmcsfAcExtension.Local.Calculus.Partials

/-! # Ordinary scalar derivative Cauchy control from the full comparison input

The `tv` clause of `StabBounds` is already the quantitative ordinary
characteristic variation bound. For C¹ approximants the landed AC variation
identity turns this directly into section-uniform derivative Cauchy control.
No additional smooth-input W¹¹ proposition is needed for this step.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

private theorem scalar_ac_out {e T : ℝ} {S : Fields}
    (hc1 : IsC1Solution e S (triangle 0 T)) {u : ℝ} (hu : u ∈ Icc 0 T) :
    AbsolutelyContinuousOnInterval (S.a u) u T := by
  apply ContDiffOn.absolutelyContinuousOnInterval
  rw [uIcc_of_le hu.2]
  exact hc1.c1_a.comp (contDiffOn_const.prodMk contDiffOn_id)
    (fun v hv => ⟨hu.1, hv.1, hv.2⟩)

private theorem scalar_ac_in {e T : ℝ} {S : Fields}
    (hc1 : IsC1Solution e S (triangle 0 T)) {v : ℝ} (hv : v ∈ Icc 0 T) :
    AbsolutelyContinuousOnInterval (fun u => S.b u v) 0 v := by
  apply ContDiffOn.absolutelyContinuousOnInterval
  rw [uIcc_of_le hv.1]
  exact hc1.c1_b.comp (contDiffOn_id.prodMk contDiffOn_const)
    (fun u hu => ⟨hu.1, hu.2, hv.2⟩)

/-- The ordinary outgoing and incoming scalar derivatives are uniformly
Cauchy over all natural sections, from the pending full smooth comparison.
The smallness threshold depends only on the envelope coefficient `A`,
before the triangle, coupling, size parameters, data and approximants.
This uses the actual `tv` conclusion, without assuming derivative Cauchy
control or a uniform derivative supremum. -/
theorem Null.scalar_derivative_cauchy_of_inputs (hstab : StabExtendedStmt)
    (A : ℝ) (hA : 0 < A) :
    ∃ η : ℝ, 0 < η ∧
      ∀ (T e ε M : ℝ) (Sn : ℕ → Fields) (hn : ℕ → ℝ → ℂ) (h : ℝ → ℂ),
        (∀ n, StabSetting e T ε M A (Sn n) (hn n)) →
        AbsolutelyContinuousOnInterval h 0 T → (∀ n, hn n 0 = h 0) →
        Tendsto (fun n => datumVar (hn n - h) T) atTop (𝓝 0) →
        ε ^ 2 + sigma e M T ≤ η →
        (∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, ∀ u ∈ Icc 0 T,
          (∫ v in u..T, ‖deriv ((Sn n).a u) v - deriv ((Sn m).a u) v‖) < ρ) ∧
        (∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, ∀ v ∈ Icc 0 T,
          (∫ u in (0 : ℝ)..v,
            ‖deriv (fun u => (Sn n).b u v) u - deriv (fun u => (Sn m).b u v) u‖) < ρ) := by
  obtain ⟨η, C, hη, hC, hcomp⟩ := hstab A hA
  refine ⟨η, hη, ?_⟩
  intro T e ε M Sn hn h hs hac hv hlim hsmall
  have hpair n m := (hcomp T e ε M (Sn n) (Sn m) (hn n) (hn m)
    (hs n) (hs m) hsmall).tv
  have hnonneg n m : 0 ≤ C * dataDist (hn n) (hn m) T :=
    mul_nonneg hC.le (add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg)
  constructor
  · intro ρ hρ
    obtain ⟨N, hN⟩ := data_dist_cauchy_of_stabSetting hs hac hv hlim (ρ / C) (div_pos hρ hC)
    refine ⟨N, fun n hn' m hm' u hu => ?_⟩
    have hb : eVariationOn ((Sn n).a u - (Sn m).a u) (Icc u T) ≤
        ENNReal.ofReal (C * dataDist (hn n) (hn m) T) :=
      (le_iSup₂ u hu).trans (le_self_add.trans (hpair n m))
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    rw [ENNReal.toReal_ofReal (hnonneg n m), W11.variation_sub_eq_integral hu.2
      (scalar_ac_out (hs n).c1 hu) (scalar_ac_out (hs m).c1 hu)] at hr
    exact hr.trans_lt ((lt_div_iff₀' hC).1 (hN n hn' m hm'))
  · intro ρ hρ
    obtain ⟨N, hN⟩ := data_dist_cauchy_of_stabSetting hs hac hv hlim (ρ / C) (div_pos hρ hC)
    refine ⟨N, fun n hn' m hm' v hv' => ?_⟩
    have hb : eVariationOn ((fun u => (Sn n).b u v) - (fun u => (Sn m).b u v)) (Icc 0 v) ≤
        ENNReal.ofReal (C * dataDist (hn n) (hn m) T) :=
      (le_iSup₂ v hv').trans (le_add_self.trans (hpair n m))
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    rw [ENNReal.toReal_ofReal (hnonneg n m), W11.variation_sub_eq_integral hv'.1
      (scalar_ac_in (hs n).c1 hv') (scalar_ac_in (hs m).c1 hv')] at hr
    exact hr.trans_lt ((lt_div_iff₀' hC).1 (hN n hn' m hm'))

private theorem uniform_cauchy_of_supDist {T C : ℝ} {F : ℕ → ℝ → ℝ → ℂ}
    {hn : ℕ → ℝ → ℂ} (hC : 0 < C)
    (hdata : ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      dataDist (hn n) (hn m) T < ρ)
    (hb : ∀ n m, supDist T (F n) (F m) ≤
      ENNReal.ofReal (C * dataDist (hn n) (hn m) T)) :
    UniformCauchySeqOn (fun n => Function.uncurry (F n)) atTop (triangle 0 T) := by
  apply Metric.uniformCauchySeqOn_iff.2
  intro ρ hρ
  obtain ⟨N, hN⟩ := hdata (ρ / C) (div_pos hρ hC)
  refine ⟨N, fun n hn' m hm' p hp => ?_⟩
  have hpoint : ENNReal.ofReal ‖F n p.1 p.2 - F m p.1 p.2‖ ≤
      ENNReal.ofReal (C * dataDist (hn n) (hn m) T) := by
    rw [ofReal_norm]
    exact (le_iSup₂ p hp).trans (hb n m)
  have hδ : 0 ≤ C * dataDist (hn n) (hn m) T :=
    mul_nonneg hC.le (add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg)
  have hr := (ENNReal.ofReal_le_ofReal_iff hδ).1 hpoint
  change dist (F n p.1 p.2) (F m p.1 p.2) < ρ
  rw [dist_eq_norm]
  exact hr.trans_lt ((lt_div_iff₀' hC).1 (hN n hn' m hm'))

/-- The three normalized scalar fields are uniformly Cauchy on the full
closed triangle, from the pending full classical comparison contract.
The threshold depends only on `A`, before all data and size parameters.
This is the scalar uniform component of the same-label construction. -/
theorem Null.scalar_uniform_cauchy_of_inputs (hstab : StabExtendedStmt)
    (A : ℝ) (hA : 0 < A) :
    ∃ η : ℝ, 0 < η ∧
      ∀ (T e ε M : ℝ) (Sn : ℕ → Fields) (hn : ℕ → ℝ → ℂ) (h : ℝ → ℂ),
        (∀ n, StabSetting e T ε M A (Sn n) (hn n)) →
        AbsolutelyContinuousOnInterval h 0 T → (∀ n, hn n 0 = h 0) →
        Tendsto (fun n => datumVar (hn n - h) T) atTop (𝓝 0) →
        ε ^ 2 + sigma e M T ≤ η →
        UniformCauchySeqOn (fun n => Function.uncurry (Sn n).a) atTop (triangle 0 T) ∧
        UniformCauchySeqOn (fun n => Function.uncurry (Sn n).b) atTop (triangle 0 T) ∧
        UniformCauchySeqOn (fun n => Function.uncurry (Sn n).phi) atTop (triangle 0 T) := by
  obtain ⟨η, C, hη, hC, hcomp⟩ := hstab A hA
  refine ⟨η, hη, ?_⟩
  intro T e ε M Sn hn h hs hac hv hlim hsmall
  have hd := data_dist_cauchy_of_stabSetting hs hac hv hlim
  have hp n m := (hcomp T e ε M (Sn n) (Sn m) (hn n) (hn m)
    (hs n) (hs m) hsmall).main
  refine ⟨uniform_cauchy_of_supDist hC hd ?_, uniform_cauchy_of_supDist hC hd ?_,
    uniform_cauchy_of_supDist hC hd ?_⟩
  · intro n m
    exact le_add_self.trans (le_self_add.trans (le_self_add.trans (hp n m)))
  · intro n m
    exact le_add_self.trans (le_self_add.trans (hp n m))
  · intro n m
    exact le_add_self.trans (hp n m)

end EmcsfAcExtension.Local
