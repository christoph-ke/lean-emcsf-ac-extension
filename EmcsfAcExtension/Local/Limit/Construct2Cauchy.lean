module

public import EmcsfAcExtension.Local.Limit.Inputs
import EmcsfAcExtension.Infra.W11.Approximation
import EmcsfAcExtension.Local.Limit.UI
import EmcsfAcExtension.Local.Calculus.Partials

/-! # Same-label mixed Cauchy control from the smooth comparison input

This is the P2 consumer discharge from internal project record: W¹¹ data convergence,
not assumed mixed Cauchy control, is the premise of the UI wrapper.
The standing comparison setting is the internal project record setting.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

private theorem datum_variation_finite {e T : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hT : 0 < T) (hS : IsC1Solution e S (triangle 0 T)) (hd : IsRestartData S h T) :
    eVariationOn h (Icc 0 T) ≠ ⊤ := by
  have ca : ContDiffOn ℝ 1 (S.a 0) (Icc 0 T) :=
    hS.c1_a.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun v hv => ⟨le_rfl, hv.1, hv.2⟩)
  have ch : ContDiffOn ℝ 1 h (Icc 0 T) :=
    ca.congr (fun v hv => (hd.1 v hv).2.symm)
  have hac : AbsolutelyContinuousOnInterval h 0 T := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hT.le] using ch
  exact hac.boundedVariationOn_Icc hT.le

/-- Strong variation approximation with a common vertex makes the actual
normalized data Cauchy in the representative W¹¹ distance. This auxiliary
fact uses only finiteness of the classical data variation, not stability. -/
theorem data_dist_cauchy_of_stabSetting {T e ε M A : ℝ} {Sn : ℕ → Fields}
    {hn : ℕ → ℝ → ℂ} {h : ℝ → ℂ}
    (hs : ∀ n, StabSetting e T ε M A (Sn n) (hn n))
    (hac : AbsolutelyContinuousOnInterval h 0 T)
    (hv : ∀ n, hn n 0 = h 0)
    (hlim : Tendsto (fun n => datumVar (hn n - h) T) atTop (𝓝 0)) :
    ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      dataDist (hn n) (hn m) T < ρ := by
  have hb n : BoundedVariationOn (hn n) (Icc 0 T) :=
    datum_variation_finite (hs n).pos (hs n).c1 (hs n).data
  have hh : BoundedVariationOn h (Icc 0 T) := hac.boundedVariationOn_Icc (hs 0).pos.le
  have heq n : W11.intervalDist 0 T (hn n) h = datumVar (hn n - h) T := by
    simp only [W11.intervalDist_zero, hv, sub_self, norm_zero, zero_add]
  intro ρ hρ
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((tendsto_order.1 hlim).2 (ρ / 2) (by positivity))
  refine ⟨N, fun n hn' m hm' => ?_⟩
  calc
    dataDist (hn n) (hn m) T = W11.intervalDist 0 T (hn n) (hn m) := rfl
    _ ≤ W11.intervalDist 0 T (hn n) h + W11.intervalDist 0 T h (hn m) :=
      W11.intervalDist_triangle (hb n) hh (hb m)
    _ = datumVar (hn n - h) T + datumVar (hn m - h) T := by
      rw [heq, W11.intervalDist_comm 0 T h (hn m), heq]
    _ < ρ := by linarith only [hN n hn', hN m hm']

/-- Mixed component of the same-label Cauchy argument.
The mixed part of same-label Cauchy control follows from strong data
approximation and the pending full classical comparison theorem.
The threshold depends only on the fixed envelope coefficient `A`, before
time, coupling, size parameters and the entire family. No mixed Cauchy
conclusion is assumed. Uniform primary-field construction is separate. -/
theorem Null.same_label_mixed_cauchy_of_inputs (hstab : StabExtendedStmt)
    (A : ℝ) (hA : 0 < A) :
    ∃ η : ℝ, 0 < η ∧
      ∀ (T e ε M : ℝ) (Sn : ℕ → Fields) (hn : ℕ → ℝ → ℂ) (h : ℝ → ℂ),
        (∀ n, StabSetting e T ε M A (Sn n) (hn n)) →
        AbsolutelyContinuousOnInterval h 0 T → (∀ n, hn n 0 = h 0) →
        Tendsto (fun n => datumVar (hn n - h) T) atTop (𝓝 0) →
        ε ^ 2 + sigma e M T ≤ η →
        ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
          jDist T (Sn n) (Sn m) + kDist e T (Sn n) (Sn m) < ENNReal.ofReal ρ := by
  obtain ⟨η, C, hη, hC, hcomp⟩ := hstab A hA
  refine ⟨η, hη, ?_⟩
  intro T e ε M Sn hn h hs hac hv hlim hsmall ρ hρ
  obtain ⟨N, hN⟩ := data_dist_cauchy_of_stabSetting hs hac hv hlim (ρ / C) (div_pos hρ hC)
  refine ⟨N, fun n hn' m hm' => ?_⟩
  have hb := (hcomp T e ε M (Sn n) (Sn m) (hn n) (hn m)
    (hs n) (hs m) hsmall).main
  have hjk : jDist T (Sn n) (Sn m) + kDist e T (Sn n) (Sn m) ≤
      ENNReal.ofReal (C * dataDist (hn n) (hn m) T) := by
    apply le_trans ?_ hb
    exact le_self_add.trans (le_self_add.trans (le_self_add.trans le_self_add))
  apply hjk.trans_lt
  apply (ENNReal.ofReal_lt_ofReal_iff hρ).2
  exact (lt_div_iff₀' hC).1 (hN n hn' m hm')

/-- Comparison-setting UI helper for the constructed-sequence wrapper.
Discharge both mixed Cauchy premises of internal project record's UI helper using the full
classical comparison contract and W¹¹ convergence of the common-label data.
The threshold depends only on `A`, uniformly in all data and derivatives.
The same wrapper also supplies the strong-comparison UI route. -/
theorem Null.envelope_ui_of_inputs (hstab : StabExtendedStmt)
    (A : ℝ) (hA : 0 < A) :
    ∃ η : ℝ, 0 < η ∧
      ∀ (T e ε M : ℝ) (Sn : ℕ → Fields) (hn : ℕ → ℝ → ℂ) (h : ℝ → ℂ),
        (∀ n, StabSetting e T ε M A (Sn n) (hn n)) →
        AbsolutelyContinuousOnInterval h 0 T → (∀ n, hn n 0 = h 0) →
        Tendsto (fun n => datumVar (hn n - h) T) atTop (𝓝 0) →
        ε ^ 2 + sigma e M T ≤ η →
        UnifIntegrable (fun n v => (outEnv 0 (jC1 (triangle 0 T) (Sn n)) v).toReal)
            1 (volume.restrict (Icc 0 T)) ∧
          UnifIntegrable (fun n u => (inEnv T (kC1 e (triangle 0 T) (Sn n)) u).toReal)
            1 (volume.restrict (Icc 0 T)) := by
  obtain ⟨η, hη, hc⟩ := Null.same_label_mixed_cauchy_of_inputs hstab A hA
  refine ⟨η, hη, ?_⟩
  intro T e ε M Sn hn h hs hac hv hlim hsmall
  have hC := hc T e ε M Sn hn h hs hac hv hlim hsmall
  apply Null.envelope_uniform_integrability_of_cauchy (hs 0).pos (fun n => (hs n).c1)
  · intro ρ hρ
    obtain ⟨N, hN⟩ := hC ρ hρ
    exact ⟨N, fun n hn' m hm' => le_self_add.trans_lt (hN n hn' m hm')⟩
  · intro ρ hρ
    obtain ⟨N, hN⟩ := hC ρ hρ
    exact ⟨N, fun n hn' m hm' => le_add_self.trans_lt (hN n hn' m hm')⟩

end EmcsfAcExtension.Local
