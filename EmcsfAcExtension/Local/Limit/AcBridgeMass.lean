module

public import EmcsfAcExtension.Local.Limit.Inputs
public import EmcsfAcExtension.Local.Defs.Box
public import EmcsfAcExtension.Local.Limit.AcBridgeDerivative
import EmcsfAcExtension.Local.Limit.AcBridgeStrongSequence

/-! # Full general-AC strong mass-ratio characteristic derivatives

internal project record item 7.6 and internal project record. Smooth mass Hardy comparisons are
passed through construction before broad identification is used.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

/-- [internal]
charged_SF_new_version.tex:L5442–L5450. Both ordinary mass-ratio derivatives converge
strongly in L¹,
uniformly over the complete outgoing and incoming section families.
The original sequence consists of broad AC solutions, without smoothness
or constructed provenance assumptions. The positive threshold and coefficient
depend only on the fixed `c,H`, before time, coupling, size and all data.
The displayed quantitative estimate is the stronger dimensionless bound;
the approved loose `C*(1+σ)` estimate follows since `σ≥0`. -/
theorem mass_derivatives_strong_of_inputs
    (hex : WholeTriangleExistenceStmt) (hstab : StabExtendedStmt)
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
                ENNReal.ofReal (C * dataDist (hn n) h T)) := by
  obtain ⟨s,C,hs,hC,hcore⟩ := ac_mass_potential_limits_of_inputs hex hstab c H hc hH
  refine ⟨s,C,hs,hC,?_⟩
  intro T e η M Cb hn h Sn Jn Kn hT hη hac hacn hSn hdn hbox hJn hKn hjn hkn hmass hsmall hd
  obtain ⟨S,hS,hdS,hm,_,hb,_⟩ := hcore T e η M Cb hn h Sn Jn Kn hT hη hac hacn hSn hdn
    hbox hJn hKn hjn hkn hmass hsmall hd
  exact ⟨S,hS,hdS,hm,hb⟩

end EmcsfAcExtension.Local
