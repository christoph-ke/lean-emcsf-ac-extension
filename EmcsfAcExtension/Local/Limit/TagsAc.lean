module

public import EmcsfAcExtension.Local.Limit.AcBridgeScalar
public import EmcsfAcExtension.Local.Limit.AcBridgeMaxwell
public import EmcsfAcExtension.Local.Limit.AcBridgeMass
public import EmcsfAcExtension.Local.Limit.AcBridgePotential
import EmcsfAcExtension.Local.Construction.WireC1Bound
import EmcsfAcExtension.Local.Stability.ExtendedLipschitz

/-! # Unconditional general-AC characteristic node exports

The landed whole-triangle and extended stability producers discharge the
conditional bridge theorems. The original broad AC sequence, fixed box,
independent envelopes and every quantitative scale factor are retained.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

/-- [node restart-sec-bv-stability-independent#scalar-characteristic-strong-W11]
The general-AC scalar characteristic record, including own-connection and
parallel derivatives, charged_SF_new_version.tex:L5375–L5406. The positive threshold and
coefficient depend only on `c,H`, uniformly in time, coupling, size, data and
solutions; no original-sequence smoothness is required. -/
theorem Stab.scalar_characteristic_strong_w11
    (c H : ℝ) (hc : 0 < c) (hH : 0 < H) :
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
            ‖deriv (fun u => (Sn n).b u v) u - deriv (fun u => S.b u v) u‖) ≤
              C * dataDist (hn n) h T) :=
  scalar_characteristic_strong_W11_of_inputs whole_triangle_existence stab_extended c H hc hH

/-- [node restart-sec-bv-stability-independent#Maxwell-characteristic-AC-limit]
The general-AC Maxwell characteristic record, charged_SF_new_version.tex:L5452.
The positive threshold depends only on `c,H`, uniformly in time, coupling,
size, data and solutions. Both literal current limits, strong section
derivatives and zero axis charge belong to the conclusion. -/
theorem Stab.maxwell_characteristic_ac_limit
    (c H : ℝ) (hc : 0 < c) (hH : 0 < H) :
    ∃ s : ℝ, 0 < s ∧
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
          MaxwellCharacteristicLimit e T Sn S :=
  maxwell_characteristic_ac_limit_of_inputs whole_triangle_existence stab_extended c H hc hH

/-- [node restart-sec-bv-stability-independent#mass-derivatives-strong]
The full general-AC mass-ratio derivative record, charged_SF_new_version.tex:L5442–L5450.
The positive threshold and coefficient depend only on `c,H`, uniformly in
time, coupling, size, data and solutions. The sum of both section suprema
retains its dimensionless `C * dataDist` bound. -/
theorem Stab.mass_derivatives_strong
    (c H : ℝ) (hc : 0 < c) (hH : 0 < H) :
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
          RealCharacteristicLimit T (fun n => (Sn n).mu) S.mu ∧
          (∀ n, (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T,
            ‖deriv ((Sn n).mu u) v - deriv (S.mu u) v‖ₑ) +
            (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
              ‖deriv (fun s => (Sn n).mu s v) u - deriv (fun s => S.mu s v) u‖ₑ) ≤
                ENNReal.ofReal (C * dataDist (hn n) h T)) :=
  mass_derivatives_strong_of_inputs whole_triangle_existence stab_extended c H hc hH

/-- [node restart-sec-bv-stability-independent#potential-characteristic-AC-strong-limit]
The full general-AC potential record, charged_SF_new_version.tex:L5453–L5523.
The positive threshold and coefficient depend only on `c,H`, uniformly in
time, coupling, size, data and solutions. The derivative bound retains
`6*C*|e|*M*T`, both AC families, literal constraint and primitives. -/
theorem Stab.potential_characteristic_ac_strong_limit
    (c H : ℝ) (hc : 0 < c) (hH : 0 < H) :
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
          PotentialCharacteristicLimit T Sn S ∧
          (∀ n, (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T,
            ‖deriv ((Sn n).A u) v - deriv (S.A u) v‖ₑ) +
            (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
              ‖deriv (fun s => (Sn n).A s v) u - deriv (fun s => S.A s v) u‖ₑ) ≤
                ENNReal.ofReal (6 * C * |e| * M * T * dataDist (hn n) h T)) :=
  potential_characteristic_ac_strong_limit_of_inputs whole_triangle_existence
    stab_extended c H hc hH

end EmcsfAcExtension.Local
