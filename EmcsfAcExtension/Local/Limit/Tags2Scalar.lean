module

public import EmcsfAcExtension.Local.Limit.AcBridgeScalar
import EmcsfAcExtension.Local.Construction.WireC1Bound
import EmcsfAcExtension.Local.Stability.ExtendedLipschitz

/-! # Strong scalar and ordinary incoming AC limit node closures

The landed full general AC record applies in particular to the common-gauge
smooth approximants, without a derivative supremum bound. Both producer
inputs are discharged. charged_SF_new_version.tex:L6450–6452.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

/-- [node restart-sec-independent-null-construction#scalar-strong-ac-limit]
[node restart-sec-independent-null-construction#ordinary-incoming-AC-limit]
Uniform normalized scalar limits and section-uniform strong ordinary,
own-connection covariant, and transported derivatives, with AC limit sections.
The thresholds and derivative coefficient depend only on the fixed box gap
`c` and envelope coefficient `H`, before time, coupling, size and the sequence;
there is no bound on smooth initial derivative suprema. The ordinary incoming
clause is explicit, including conversion through the varying connections. -/
theorem scalar_strong_ac_limit (c H : ℝ) (hc : 0 < c) (hH : 0 < H) :
    ∃ s C : ℝ, 0 < s ∧ 0 < C ∧
      ∀ (T e η M Cb : ℝ) (hn : ℕ → ℝ → ℂ) (h : ℝ → ℂ)
        (Sn : ℕ → Fields) (Jn Kn : ℕ → ℝ → ℝ),
        0 < T → 0 ≤ η → AbsolutelyContinuousOnInterval h 0 T →
        (∀ n, AbsolutelyContinuousOnInterval (hn n) 0 T) →
        (∀ n, IsSolution e (Sn n) (triangle 0 T)) →
        (∀ n, IsRestartData (Sn n) (hn n) T) →
        (∀ n, StabBox (Sn n) c Cb η M (triangle 0 T)) →
        (∀ n, IntervalIntegrable (Jn n) volume 0 T) →
        (∀ n, IntervalIntegrable (Kn n) volume 0 T) →
        (∀ n u, u ∈ Icc 0 T → ∀ᵐ v ∂volume.restrict (Icc u T), ‖jOut (Sn n) u v‖ ≤ Jn n v) →
        (∀ n v, v ∈ Icc 0 T → ∀ᵐ u ∂volume.restrict (Icc 0 v), ‖kIn e (Sn n) u v‖ ≤ Kn n u) →
        (∀ n, (∫ v in (0 : ℝ)..T, Jn n v) + (∫ u in (0 : ℝ)..T, Kn n u) ≤ H * η) →
        η ^ 2 + sigma e M T ≤ s →
        Tendsto (fun n => dataDist (hn n) h T) atTop (𝓝 0) →
        ∃ S : Fields, IsSolution e S (triangle 0 T) ∧ IsRestartData S h T ∧
          ScalarCharacteristicLimit e T Sn S ∧
          (∀ n u, u ∈ Icc 0 T → (∫ v in u..T,
            ‖deriv ((Sn n).a u) v - deriv (S.a u) v‖) ≤ C * dataDist (hn n) h T) ∧
          (∀ n v, v ∈ Icc 0 T → (∫ u in (0 : ℝ)..v,
            ‖deriv (fun u => (Sn n).b u v) u - deriv (fun u => S.b u v) u‖) ≤ C * dataDist (hn n) h
                T) :=
  scalar_characteristic_strong_W11_of_inputs
    whole_triangle_existence stab_extended c H hc hH

end EmcsfAcExtension.Local
