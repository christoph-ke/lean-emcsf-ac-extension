module

public import EmcsfAcExtension.Local.Stability.AssemblyOrdered

/-! # Complete ordered scalar sources in the small-data regime

The area estimates select `p = 3/4` under the section's explicit smallness
instance, `charged_SF_new_version.tex:L4971–L4971`. The pointwise estimate retains every
`1/2 ≤ p ≤ 1 - ε²` and includes the complete curvature combination in the
`j` transport equation, `charged_SF_new_version.tex:L5042–L5053`.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem scalar_combination_le (c z : ℂ) :
    ‖c * (z + 2 * starRingEnd ℂ z)‖ₑ ≤ ENNReal.ofReal 3 * ‖c * z‖ₑ := by
  have hb : ‖c * (z + 2 * starRingEnd ℂ z)‖ ≤ 3 * ‖c * z‖ := by
    rw [norm_mul, norm_mul]
    calc
      _ ≤ ‖c‖ * (‖z‖ + ‖2 * starRingEnd ℂ z‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg c)
      _ = _ := by
        simp only [norm_mul, RCLike.norm_conj]
        norm_num
        ring
  simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ofReal_norm] using
    ENNReal.ofReal_le_ofReal hb

/-- [node restart-stab-ordered-pointwise]
Complete outgoing scalar curvature source pointwise bound,
charged_SF_new_version.tex:L5042–L5053. The literal constant `768` is universal,
independent of `e,T,ε,M,A,S,h,p` and all derivative suprema, uniformly for
`1/2 ≤ p ≤ 1 - ε²`. -/
theorem stab_ordered_source_pointwise
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h)
    {p u v : ℝ} (hp0 : 1 / 2 ≤ p) (hp : p ≤ 1 - ε ^ 2)
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    ‖(S.nu u v : ℂ) * S.theta u v / (S.r u v : ℂ) ^ 2 *
      (curvScalar (triangle 0 T) S u v +
        2 * starRingEnd ℂ (curvScalar (triangle 0 T) S u v))‖ₑ ≤
      ENNReal.ofReal (768 * ε) * stabOrderedKernel p
        ((Icc 0 T).indicator (inEnv T (kC1 e (triangle 0 T) S)))
        ((Icc 0 T).indicator (outEnv 0 (jC1 (triangle 0 T) S))) u v := by
  apply (scalar_combination_le _ _).trans
  apply (mul_le_mul' le_rfl (stab_ordered_pointwise hset hp0 hp hu huv hvT)).trans_eq
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
  rw [show (3 : ℝ) * (256 * ε) = 768 * ε by ring]

/-- [node restart-stab-ordered-l1]
Exponent-free complete outgoing scalar source area bound,
charged_SF_new_version.tex:L5059–L5064. The literal constant `1536` is universal,
independent of `e,T,ε,M,A,S,h` and all derivative suprema. The proof
selects `p = 3/4` using only the displayed smallness instance. -/
theorem stab_ordered_l1_small
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) (hε : ε ^ 2 ≤ 1 / 4) :
    (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v,
      ‖(S.nu u v : ℂ) * S.theta u v / (S.r u v : ℂ) ^ 2 *
        (curvScalar (triangle 0 T) S u v +
          2 * starRingEnd ℂ (curvScalar (triangle 0 T) S u v))‖ₑ) ≤
      ENNReal.ofReal (1536 * ε) *
        (∫⁻ s in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S) s) *
        (∫⁻ w in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S) w) := by
  exact stab_ordered_l1 (p := 3 / 4) hset (by norm_num) (by linarith only [hε])

/-- [node restart-sec-bv-stability-independent#incoming-ordered-l1]
Exponent-free complete incoming scalar source area bound,
charged_SF_new_version.tex:L5065–L5068, with the approved incoming conjugate orientation.
The literal constant `1536` is universal, independent of `e,T,ε,M,A,S,h`
and all derivative suprema. The proof selects `p = 3/4` using only the
displayed smallness instance. -/
theorem stab_incoming_ordered_l1_small
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) (hε : ε ^ 2 ≤ 1 / 4) :
    (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v,
      ‖(S.lam u v : ℂ) * S.xi u v / (S.r u v : ℂ) ^ 2 *
        (curvScalarIn e (triangle 0 T) S u v +
          2 * starRingEnd ℂ (curvScalarIn e (triangle 0 T) S u v))‖ₑ) ≤
      ENNReal.ofReal (1536 * ε) *
        (∫⁻ s in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S) s) *
        (∫⁻ w in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S) w) := by
  exact stab_incoming_ordered_l1 (p := 3 / 4) hset (by norm_num) (by linarith only [hε])

end EmcsfAcExtension.Local
