module

public import EmcsfAcExtension.Local.Defs.C1Bound
public import EmcsfAcExtension.Local.Defs.C1Class
public import EmcsfAcExtension.Local.Defs.Params
import EmcsfAcExtension.Local.Construction.Corner
import EmcsfAcExtension.Local.Construction.WireC1Bound
import EmcsfAcExtension.Local.Construction.WireShort
import EmcsfAcExtension.Local.Construction.WireRecovery

/-! # Unconditional uniform axis continuation parameters

The common primary bound, enlarged cone class and actual short-cone existence
time are chosen before the candidate maximal apex and corner width. All three
producer inputs in the earlier continuation helper are discharged.
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- [node restart-sec-independent-null-construction#continuation-parameters]
The common C¹ bound and actual uniform axis Picard time, charged_SF_new_version.tex:L6291–L6293,
internal project record:L1073–L1085. Positive thresholds are universal, before `T,e,h`.
The finite `B`, enlarged `Bc`, expansion margin `ℓ` and local time `τ` may depend
on this datum's first derivative, but precede every constructed apex `s` and
candidate maximal apex `q`. Choose `η < min (q/8) (τ/8)` only afterwards.
Neither the Picard theorem nor full-system recovery is an extra premise. -/
theorem Null.continuation_parameters_uniform :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      ∀ (T e : ℝ) (h : ℝ → ℂ), 0 < T → ContDiffOn ℝ 1 h (Icc 0 T) →
        datumVar h T ≤ ε → chargedScale e h T ≤ δ →
        ∃ B Bc ℓ τ : ℝ, 0 < B ∧ 1 ≤ Bc ∧ 0 < ℓ ∧ 0 < τ ∧
          ℓ = B⁻¹ ∧
          Bc = 1 + 16 * (B + 1) * (1 + ℓ⁻¹) + 64 * (B + 1) ^ 2 * ℓ⁻¹ ^ 2 ∧
          (∀ (s : ℝ) (F : Fields), 0 < s → s ≤ T →
            IsC1Solution e F (triangle 0 s) → IsRestartData F h s →
            C1BoundOn F (triangle 0 s) B) ∧
          (∀ (c L : ℝ) (lam₀ : ℝ → ℝ) (h₀ : ℝ → ℂ), 0 < L → L ≤ τ →
            ContDiffOn ℝ 1 lam₀ (Icc c (c + L)) →
            ContDiffOn ℝ 1 h₀ (Icc c (c + L)) →
            (∀ v ∈ Icc c (c + L), ℓ / 2 ≤ lam₀ v ∧ |lam₀ v| ≤ Bc ∧
              ‖h₀ v‖ ≤ Bc ∧ |derivWithin lam₀ (Icc c (c + L)) v| ≤ Bc ∧
              ‖derivWithin h₀ (Icc c (c + L)) v‖ ≤ Bc) →
            ∃ F : Fields, IsC1Solution e F (triangle c (c + L)) ∧
              (∀ v ∈ Icc c (c + L), F.lam c v = lam₀ v ∧ F.a c v = h₀ v) ∧
              ∀ t ∈ Icc c (c + L), F.A t t = 0) ∧
          ∀ q : ℝ, 0 < q → q ≤ T →
            ∃ η : ℝ, 0 < η ∧ η < q / 8 ∧ η < τ / 8 :=
  continuation_parameters_of_inputs continuation_c1_bound_input
    continuation_short_picard_input continuation_recovery_input

end EmcsfAcExtension.Local
