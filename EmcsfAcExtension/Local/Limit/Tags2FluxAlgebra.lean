module

public import EmcsfAcExtension.Local.Defs.Limit
import EmcsfAcExtension.Local.Limit.UIAux
import EmcsfAcExtension.Infra.Mixed.SectionIntegral

/-! # Uniform charge-to-radius quotients at the regular axis

The quadratic charge bound makes division by the radius continuous on a
compact cusp. This supplies the actual electric term in the mass flux;
uniform primary convergence alone is not used to divide at the axis.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace EmcsfAcExtension.Local

private theorem continuousOn_cusp_div {B R : ℝ} (_hB : 0 ≤ B) :
    ContinuousOn (fun p : ℝ × ℝ => p.2 / p.1)
      {p | 0 ≤ p.1 ∧ p.1 ≤ R ∧ |p.2| ≤ B * p.1 ^ 2} := by
  intro p hp
  by_cases hp0 : p.1 = 0
  · have hpq : p.2 = 0 := by
      have hh : |p.2| ≤ 0 := by
        simpa only [hp0, zero_pow (by norm_num : 2 ≠ 0), mul_zero] using hp.2.2
      exact abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))
    change Tendsto _ _ _
    apply tendsto_iff_norm_sub_tendsto_zero.2
    have hlim : Tendsto (fun q : ℝ × ℝ => B * |q.1|)
        (𝓝[{p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ R ∧ |p.2| ≤ B * p.1 ^ 2}] p) (𝓝 0) := by
      have hc : Continuous (fun q : ℝ × ℝ => B * |q.1|) := continuous_const.mul continuous_fst.abs
      simpa only [hp0, abs_zero, mul_zero] using
        (hc.continuousAt (x := p)).tendsto.mono_left nhdsWithin_le_nhds
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with q hq
    simp only [hp0, hpq, div_zero, sub_zero, Real.norm_eq_abs, abs_div, abs_of_nonneg hq.1]
    by_cases hq0 : q.1 = 0
    · simp [hq0]
    · rw [div_le_iff₀ (lt_of_le_of_ne hq.1 (Ne.symm hq0))]
      simpa only [pow_two, mul_assoc] using hq.2.2
  · exact continuous_snd.continuousWithinAt.div continuous_fst.continuousWithinAt hp0

/-- [internal] Quadratic axis control gives uniform convergence of `Q/r`,
including its literal zero-axis value. `B,R` are explicit common bounds;
the statement introduces no constant and uses no derivative supremum. -/
theorem uniform_charge_ratio_of_quadratic_bound {T B R : ℝ}
    {rn qn : ℕ → ℝ → ℝ → ℝ} {r q : ℝ → ℝ → ℝ}
    (hB : 0 ≤ B) (_hR : 0 ≤ R)
    (cr : ∀ n, ContinuousOn (Function.uncurry (rn n)) (triangle 0 T))
    (cq : ∀ n, ContinuousOn (Function.uncurry (qn n)) (triangle 0 T))
    (hr : TendstoUniformlyOn (fun n => Function.uncurry (rn n))
      (Function.uncurry r) atTop (triangle 0 T))
    (hq : TendstoUniformlyOn (fun n => Function.uncurry (qn n))
      (Function.uncurry q) atTop (triangle 0 T))
    (hb : ∀ n p, p ∈ triangle 0 T →
      0 ≤ rn n p.1 p.2 ∧ rn n p.1 p.2 ≤ R ∧ |qn n p.1 p.2| ≤ B * rn n p.1 p.2 ^ 2) :
    (∀ n, ContinuousOn (fun p : ℝ × ℝ => qn n p.1 p.2 / rn n p.1 p.2) (triangle 0 T)) ∧
      ContinuousOn (fun p : ℝ × ℝ => q p.1 p.2 / r p.1 p.2) (triangle 0 T) ∧
      TendstoUniformlyOn (fun n p => qn n p.1 p.2 / rn n p.1 p.2)
        (fun p => q p.1 p.2 / r p.1 p.2) atTop (triangle 0 T) := by
  let K := {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ R ∧ |p.2| ≤ B * p.1 ^ 2}
  have hclosed : IsClosed K :=
    (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_fst continuous_const).inter
        (isClosed_le continuous_snd.abs (continuous_const.mul (continuous_fst.pow 2))))
  have hcompact : IsCompact K := by
    apply (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hclosed
      (s := Icc (0 : ℝ) R ×ˢ Icc (-B*R^2) (B*R^2))
    intro p hp
    have hpq := hp.2.2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp.1 hp.2.1 2) hB)
    exact ⟨⟨hp.1,hp.2.1⟩, by simpa only [mem_Icc, neg_mul] using abs_le.1 hpq⟩
  have hlim p (hp : p ∈ triangle 0 T) : (r p.1 p.2, q p.1 p.2) ∈ K := by
    refine ⟨ge_of_tendsto (hr.tendsto_at hp) (Eventually.of_forall fun n => (hb n p hp).1),
      le_of_tendsto (hr.tendsto_at hp) (Eventually.of_forall fun n => (hb n p hp).2.1), ?_⟩
    exact le_of_tendsto_of_tendsto (hq.tendsto_at hp).abs
      ((hr.tendsto_at hp).pow 2 |>.const_mul B) (Eventually.of_forall fun n => (hb n p hp).2.2)
  have hcont := continuousOn_cusp_div (R := R) hB
  have hcn n : ContinuousOn (fun p : ℝ × ℝ => qn n p.1 p.2 / rn n p.1 p.2) (triangle 0 T) :=
    hcont.comp ((cr n).prodMk (cq n)) (hb n)
  have hc : ContinuousOn (fun p : ℝ × ℝ => q p.1 p.2 / r p.1 p.2) (triangle 0 T) :=
    hcont.comp ((hr.continuousOn (Eventually.of_forall cr).frequently).prodMk
      (hq.continuousOn (Eventually.of_forall cq).frequently)) hlim
  have hmaps : ∀ n : ℕ, ∀ p ∈ triangle 0 T,
      (rn n p.1 p.2, qn n p.1 p.2) ∈ K := fun n p hp => hb n p hp
  have hpair : TendstoUniformlyOn
      (fun (n : ℕ) (p : ℝ × ℝ) => (rn n p.1 p.2, qn n p.1 p.2))
      (fun p : ℝ × ℝ => (r p.1 p.2, q p.1 p.2)) atTop (triangle 0 T) := by
    apply Metric.tendstoUniformlyOn_iff.2
    intro ρ hρ
    filter_upwards [(Metric.tendstoUniformlyOn_iff.1 hr) ρ hρ,
      (Metric.tendstoUniformlyOn_iff.1 hq) ρ hρ] with n hnr hnq p hp
    rw [Prod.dist_eq]
    exact max_lt (hnr p hp) (hnq p hp)
  exact ⟨hcn,hc, UniformContinuousOn.comp_tendstoUniformlyOn_eventually
    (Eventually.of_forall hmaps) hlim
    (hcompact.uniformContinuousOn_of_continuous hcont) hpair⟩

end EmcsfAcExtension.Local
