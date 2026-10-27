module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.EnvelopeClose
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseApex
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseRestriction
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseContinuity
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseAxis
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseSharp
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Api.Finite
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Continuity closure of the two characteristic envelope budgets

One fixed classical field supplies the continuous growing-triangle
budgets. Each positive subtriangle inherits the same upper controls. The
simultaneous strict improvement then excludes the large algebraic branch
of the coupled inequalities, including at zero datum variation.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- Each characteristic envelope has coefficient `9/8` under universal
positive thresholds chosen before all data. The thresholds depend only on
the fixed box, uniformly in all higher initial derivatives. This helper
provides the individual envelope clauses of `restart-bv-envelope-final`. -/
theorem closed_envelopes_sharp : ∃ ε₀ δ₀ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ (e T ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e T ε M S h → ε ≤ ε₀ → |e| * (T / 2) * M ≤ δ₀ →
      (∫⁻ v in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S) v) ≤
          ENNReal.ofReal (9 / 8 * ε) ∧
        (∫⁻ u in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S) u) ≤
          ENNReal.ofReal (9 / 8 * ε) := by
  obtain ⟨Cj, hCj, hj⟩ := bv_J_close
  obtain ⟨Ck, hCk, hk⟩ := bv_K_close
  let A := Cj + Ck
  have hA : 0 < A := add_pos hCj hCk
  let τ := 1 / (10000 * (A + 1))
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  have hτsmall : τ ≤ 1 / 10000 := by
    dsimp only [τ]
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 10000)
    linarith only [hA]
  have hAτ : A * τ ≤ 1 / 10000 := by
    dsimp only [τ]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : 0 < 10000 * (A + 1))).mpr
    linarith only [hA]
  refine ⟨τ, τ, hτ, hτ, ?_⟩
  intro e T ε M S h hset hε hδ
  let δ := |e| * (T / 2) * M
  let X := fun s => (∫⁻ v in Icc 0 s, outEnv 0 (jC1 (triangle 0 T) S) v).toReal
  let Y := fun s => (∫⁻ u in Icc 0 s, inEnv s (kC1 e (triangle 0 T) S) u).toReal
  have hε0 := hset.eps_nonneg
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans hset.one_le_M
  have hδ0 : 0 ≤ δ := by dsimp only [δ]; have := hset.pos; positivity
  have hsmall (x : ℝ) (hx : 0 ≤ x) (hxt : x ≤ τ) : A * x ^ 2 ≤ 1 / 1000 := by
    have hx1 : x ≤ 1 := hxt.trans (hτsmall.trans (by norm_num))
    have hx2 : x ^ 2 ≤ x := by nlinarith only [hx, hx1]
    exact ((mul_le_mul_of_nonneg_left hx2 hA.le).trans
      ((mul_le_mul_of_nonneg_left hxt hA.le).trans hAτ)).trans (by norm_num)
  have hε8 : ε ≤ 1 / 8 := hε.trans (hτsmall.trans (by norm_num))
  have hc := continuous_apex_envelope_integrals hset.pos.le
    (continuousOn_jC1_aux hset.pos hset.c1) (continuousOn_kC1_aux hset.pos hset.c1)
  have hx0 : X 0 = 0 := by simp [X]
  have hy0 : Y 0 = 0 := by simp [Y]
  have hCJ : Cj ≤ A := le_add_of_nonneg_right hCk.le
  have hCK : Ck ≤ A := le_add_of_nonneg_left hCj.le
  have hineq (s : ℝ) (hs : s ∈ Icc 0 T) :
      X s ≤ Real.exp (A * ε * Y s) *
          (ε + A * ε ^ 3 + A * ε * X s * Y s + A * δ ^ 2 * ε) ∧
        Y s ≤ X s + A * ε * X s * Y s + A * δ ^ 2 * ε := by
    rcases eq_or_lt_of_le hs.1 with hs0 | hs0
    · have hsz : s = 0 := hs0.symm
      subst s
      rw [hx0, hy0]
      constructor <;> positivity
    · have hsub := hset.restrict_apex hs0 hs.2
      have heq := envelope_integrals_restrict_apex hset.c1 hs0 hs.2
      have hx : (∫⁻ v in Icc 0 s, outEnv 0 (jC1 (triangle 0 s) S) v).toReal = X s :=
        congrArg ENNReal.toReal heq.1
      have hy : (∫⁻ u in Icc 0 s, inEnv s (kC1 e (triangle 0 s) S) u).toReal = Y s :=
        congrArg ENNReal.toReal heq.2
      have hscale : |e| * (s / 2) * M ≤ δ := by
        dsimp only [δ]
        gcongr
        exact hs.2
      have hscale0 : 0 ≤ |e| * (s / 2) * M := by positivity
      have hj' := hj e s ε M S h hsub hε8
      have hk' := hk e s ε M S h hsub hε8
      dsimp only at hj' hk'
      rw [hx, hy] at hj' hk'
      rw [show Cj * ε * Y s * X s = Cj * ε * X s * Y s by ring] at hj'
      have haxis : (eVariationOn (fun t => S.phi t t) (Icc 0 s)).toReal ≤ X s := by
        rw [← hx]
        exact ENNReal.toReal_mono
          (outEnv_lintegral_ne_top_of_continuousOn (continuousOn_jC1_aux hs0 hsub.c1))
          (smooth_axis_variation_budget hs0 hsub.c1 hsub.data.2)
      constructor
      · apply hj'.trans
        gcongr
      · apply hk'.trans
        gcongr
  have hclosed := coupled_envelopes_le_of_continuous hA.le hε0
    (hsmall ε hε0 hε) (hsmall δ hδ0 hδ) hc.1 hc.2 hx0 hy0
    (fun _ _ => ENNReal.toReal_nonneg) (fun _ _ => ENNReal.toReal_nonneg)
    (fun s hs => (hineq s hs).1) (fun s hs => (hineq s hs).2) T ⟨hset.pos.le, le_rfl⟩
  have hJfin := outEnv_lintegral_ne_top_of_continuousOn
    (continuousOn_jC1_aux hset.pos hset.c1)
  have hKfin := inEnv_lintegral_ne_top_of_continuousOn
    (continuousOn_kC1_aux hset.pos hset.c1)
  constructor
  · simpa only [X, ENNReal.ofReal_toReal hJfin] using ENNReal.ofReal_le_ofReal hclosed.1
  · simpa only [Y, ENNReal.ofReal_toReal hKfin] using ENNReal.ofReal_le_ofReal hclosed.2

private theorem closed_envelopes_and_variations : ∃ ε₀ δ₀ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ (e T ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e T ε M S h → ε ≤ ε₀ → |e| * (T / 2) * M ≤ δ₀ →
      (∫⁻ v in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S) v) ≤
          ENNReal.ofReal (9 / 8 * ε) ∧
      (∫⁻ u in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S) u) ≤
          ENNReal.ofReal (9 / 8 * ε) ∧
      (⨆ u ∈ Icc 0 T, eVariationOn (S.a u) (Icc u T)) ≤ ENNReal.ofReal (3 / 2 * ε) ∧
      (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
        ‖pdU (triangle 0 T) S.b u v + I * e * S.A u v * S.b u v‖ₑ) ≤
          ENNReal.ofReal (3 / 2 * ε) := by
  obtain ⟨ε₁, δ₁, hε₁, hδ₁, henv⟩ := closed_envelopes_sharp
  refine ⟨min ε₁ (1 / 64), min δ₁ 1, lt_min hε₁ (by norm_num),
    lt_min hδ₁ zero_lt_one, ?_⟩
  intro e T ε M S h hset hε hδ
  have he := henv e T ε M S h hset (hε.trans (min_le_left _ _))
    (hδ.trans (min_le_left _ _))
  have hv := closed_variations_of_envelopes hset (hε.trans (min_le_right _ _))
    (hδ.trans (min_le_right _ _)) he.1 he.2
  exact ⟨he.1, he.2, hv.1, hv.2⟩

/-- [node restart-bv-envelope-final]
The two envelope norms and the two characteristic variation budgets close
with one universal constant, chosen before all data (`charged_SF_new_version.tex:L4780–L4813`).
The constant is `3`, depending only on the fixed box and uniformly in higher
initial derivatives. The separate coefficients below two are recorded in
`bv_envelope_final_individual`, using the approved interpretation of I2. -/
theorem bv_envelope_final : ∃ ε₀ δ₀ C : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧ 0 < C ∧
    ∀ (e T ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e T ε M S h → ε ≤ ε₀ → |e| * (T / 2) * M ≤ δ₀ →
      (∫⁻ v in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S) v) +
        (∫⁻ u in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S) u) ≤ ENNReal.ofReal (C * ε) ∧
      (⨆ u ∈ Icc 0 T, eVariationOn (S.a u) (Icc u T)) +
        (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
          ‖pdU (triangle 0 T) S.b u v + I * e * S.A u v * S.b u v‖ₑ) ≤
          ENNReal.ofReal (C * ε) := by
  obtain ⟨ε₀, δ₀, hε₀, hδ₀, hclosed⟩ := closed_envelopes_and_variations
  refine ⟨ε₀, δ₀, 3, hε₀, hδ₀, by norm_num, ?_⟩
  intro e T ε M S h hset hε hδ
  obtain ⟨hj, hk, ht, hb⟩ := hclosed e T ε M S h hset hε hδ
  have hε0 := hset.eps_nonneg
  constructor
  · apply (add_le_add hj hk).trans
    rw [← ENNReal.ofReal_add (by positivity : 0 ≤ 9 / 8 * ε)
      (by positivity : 0 ≤ 9 / 8 * ε)]
    exact ENNReal.ofReal_le_ofReal (by linarith only [hε0])
  · apply (add_le_add ht hb).trans
    rw [← ENNReal.ofReal_add (by positivity : 0 ≤ 3 / 2 * ε)
      (by positivity : 0 ≤ 3 / 2 * ε)]
    exact ENNReal.ofReal_le_ofReal (by linarith)

/-- [node restart-bv-envelope-final]
Each of the four individual bounds in `restart-bv-envelope-final` has
a universal coefficient below two: `9/8` for each envelope and `3/2` for
each variation. The thresholds precede all data and are uniform in higher
initial derivatives. This is the explicit I2 interpretation of L4286–L4288. -/
theorem bv_envelope_final_individual : ∃ ε₀ δ₀ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ (e T ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e T ε M S h → ε ≤ ε₀ → |e| * (T / 2) * M ≤ δ₀ →
      (∫⁻ v in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S) v) ≤
          ENNReal.ofReal (9 / 8 * ε) ∧
      (∫⁻ u in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S) u) ≤
          ENNReal.ofReal (9 / 8 * ε) ∧
      (⨆ u ∈ Icc 0 T, eVariationOn (S.a u) (Icc u T)) ≤ ENNReal.ofReal (3 / 2 * ε) ∧
      (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
        ‖pdU (triangle 0 T) S.b u v + I * e * S.A u v * S.b u v‖ₑ) ≤
          ENNReal.ofReal (3 / 2 * ε) :=
  closed_envelopes_and_variations

end EmcsfAcExtension.Local
