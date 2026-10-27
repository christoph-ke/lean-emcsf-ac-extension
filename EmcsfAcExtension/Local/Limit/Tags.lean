module

public import EmcsfAcExtension.Local.Defs.Bounds
public import EmcsfAcExtension.Local.Assembly.Inputs
public import EmcsfAcExtension.Frozen.Fields.EqOn
import EmcsfAcExtension.Local.Limit.Construct2
import EmcsfAcExtension.Local.Limit.Construct2Complete
import EmcsfAcExtension.Local.Limit.Existence
import EmcsfAcExtension.Local.Limit.Stability
import EmcsfAcExtension.Local.Construction.WireC1Bound
import EmcsfAcExtension.Local.Stability.ExtendedLipschitz
import EmcsfAcExtension.Local.Broad.Propagation

/-! # Unconditional construction, existence and stability node exports

The full closed-triangle producer and extended comparison theorem supply
all conditional inputs. Equal-data uniqueness is exported for actual AC
solutions and exact restart data, with equality of all nine primary fields.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

/-- [node restart-sec-independent-null-construction#whole-triangle-approximants]
Choose vertex-preserving strong-W¹¹ data approximants and classical solutions
on the same full closed triangle, charged_SF_new_version.tex:L6371–L6391. The positive
thresholds and a priori coefficient are universal, before time, coupling,
datum and every approximation derivative. -/
theorem Null.whole_triangle_approximants :
    ∃ ε δ C : ℝ, 0 < ε ∧ 0 < δ ∧ 0 < C ∧
      ∀ (T e : ℝ) (h : ℝ → ℂ), 0 < T →
        AbsolutelyContinuousOnInterval h 0 T →
        datumVar h T ≤ ε → chargedScale e h T ≤ δ →
        ∃ (hn : ℕ → ℝ → ℂ) (Sn : ℕ → Fields),
          (∀ n, ContDiffOn ℝ 1 (hn n) (Icc 0 T)) ∧
          (∀ n, hn n 0 = h 0) ∧
          Tendsto (fun n => datumVar (hn n - h) T) atTop (𝓝 0) ∧
          Tendsto (fun n => eVariationOn (hn n - h) (Icc 0 T)) atTop (𝓝 0) ∧
          Tendsto (fun n => datumVar (hn n) T) atTop (𝓝 (datumVar h T)) ∧
          (∀ n, IsC1Solution e (Sn n) (triangle 0 T) ∧ IsRestartData (Sn n) (hn n) T) ∧
          ∀ n, SmoothBounds C e T (datumVar (hn n) T) (datumM (hn n) T) (Sn n) :=
  Null.whole_triangle_approximants_of_inputs whole_triangle_existence

/-- [node restart-sec-independent-null-construction#strong-same-label-cauchy]
Construct the complete mixed comparison Cauchy norm, strong limit and
constructed provenance, charged_SF_new_version.tex:L6391–L6446. Both positive thresholds
are universal, before time, coupling and datum; no uniform approximation
derivative bound is required. -/
theorem Null.constructed_strong_limit :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      ∀ (T e : ℝ) (h : ℝ → ℂ), 0 < T →
        AbsolutelyContinuousOnInterval h 0 T → datumVar h T ≤ ε → chargedScale e h T ≤ δ →
        ∃ (hn : ℕ → ℝ → ℂ) (Sn : ℕ → Fields) (S : Fields),
          (∀ n, hn n 0 = h 0) ∧
          Tendsto (fun n => eVariationOn (hn n - h) (Icc 0 T)) atTop (𝓝 0) ∧
          (∀ n, IsC1Solution e (Sn n) (triangle 0 T) ∧ IsRestartData (Sn n) (hn n) T) ∧
          (∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
            jDist T (Sn n) (Sn m) + kDist e T (Sn n) (Sn m) + geomDist T (Sn n) (Sn m) +
              supDist T (Sn n).a (Sn m).a + supDist T (Sn n).b (Sn m).b +
              supDist T (Sn n).phi (Sn m).phi < ENNReal.ofReal ρ) ∧
          StrongLimit e T Sn S ∧ IsRestartData S h T ∧ IsConstructedLimit e T h S :=
  Null.constructed_strong_limit_of_inputs whole_triangle_existence stab_extended

/-- [node restart-sec-independent-null-construction#ac-data-existence]
[node restart-sec-independent-null-construction#limit-characteristic-bounds]
[node restart-sec-independent-null-construction#integral-limit-solution]
Construct one full frozen AC solution with exact restart data, strong
constructed provenance and every existence bound, charged_SF_new_version.tex:L4421–L4436,
L6474–L6502. All positive thresholds and the bound coefficient are universal,
before time, coupling and datum; the datum requires only AC regularity. -/
theorem Null.ac_data_existence : AcDataExistenceStmt :=
  ac_data_existence_of_inputs whole_triangle_existence stab_extended

/-- [node restart-sec-independent-null-construction#limit-class-stability-uniqueness]
[node restart-sec-independent-null-construction#limit-characteristic-variation-difference]
Stability of constructed AC limits, charged_SF_new_version.tex:L6477–L6482, including
the sum of the ordinary variation-difference suprema. The positive thresholds
and coefficient are universal, before time, coupling, both data and solutions. -/
theorem Null.limit_class_stability : LimitClassStabilityStmt :=
  limit_class_stability_of_inputs stab_extended

/-- [node restart-sec-independent-null-construction#limit-class-stability-uniqueness]
Equal-data uniqueness for actual AC solutions, charged_SF_new_version.tex:L6477–L6482:
all nine fields agree on the full closed triangle. Exact restart data provide
the common entering radius and normalized scalar and both axis gauges.
No smallness, constructed provenance or estimate coefficient is required. -/
theorem Null.limit_class_equal_data_uniqueness {T e : ℝ} {h : ℝ → ℂ}
    {S₁ S₂ : Fields} (hT : 0 < T)
    (hS₁ : IsSolution e S₁ (triangle 0 T)) (hS₂ : IsSolution e S₂ (triangle 0 T))
    (hd₁ : IsRestartData S₁ h T) (hd₂ : IsRestartData S₂ h T) :
    S₁.EqOn S₂ (triangle 0 T) := by
  apply broad_uniqueness hT hS₁ hS₂
  · intro v hv
    exact ⟨(hd₁.1 v hv).1.trans (hd₂.1 v hv).1.symm,
      (hd₁.1 v hv).2.trans (hd₂.1 v hv).2.symm⟩
  · intro t ht
    exact ⟨hd₁.2 t ht, hd₂.2 t ht⟩

end EmcsfAcExtension.Local
