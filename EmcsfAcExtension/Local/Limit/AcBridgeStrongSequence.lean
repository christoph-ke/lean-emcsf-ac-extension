module

public import EmcsfAcExtension.Local.Limit.Inputs
public import EmcsfAcExtension.Local.Defs.Box
public import EmcsfAcExtension.Local.Limit.AcBridgeDerivative
import EmcsfAcExtension.Local.Limit.AcBridgeSequence
import EmcsfAcExtension.Local.Limit.AcBridgeStrongComparison
import EmcsfAcExtension.Local.Limit.AcBridgeUniform

/-! # Strong mass and potential records after broad identification

Only the fixed common box and independent j/k envelopes are assumed of
the original AC sequence. Each solution is first identified with its own
constructed solution; strong pair estimates then pass to that sequence.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

/-- Both strong real characteristic records for a general AC sequence.
The positive threshold and coefficient depend only on `c,H` and the fixed
producer contracts, before time, coupling, size, data and solutions. The
incoming potential bound retains the scale `6*C*|e|*M*T`. Original vertex
values may vary and no smooth provenance is assumed. -/
theorem ac_mass_potential_limits_of_inputs
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
          RealCharacteristicLimit T (fun n => (Sn n).A) S.A ∧
          (∀ n, (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T,
            ‖deriv ((Sn n).mu u) v - deriv (S.mu u) v‖ₑ) +
            (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
              ‖deriv (fun s => (Sn n).mu s v) u - deriv (fun s => S.mu s v) u‖ₑ) ≤
                ENNReal.ofReal (C * dataDist (hn n) h T)) ∧
          (∀ n, (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T,
            ‖deriv ((Sn n).A u) v - deriv (S.A u) v‖ₑ) +
            (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
              ‖deriv (fun s => (Sn n).A s v) u - deriv (fun s => S.A s v) u‖ₑ) ≤
                ENNReal.ofReal (6 * C * |e| * M * T * dataDist (hn n) h T)) := by
  obtain ⟨s₀,B,C₀,hs₀,_,hC₀,hcore⟩ := ac_sequence_comparisons_of_inputs hex hstab c H hc hH
  obtain ⟨ε,δ,C,hε,hδ,hC,hpair⟩ := constructed_mass_potential_pairs_of_inputs hstab
  obtain ⟨s₁,hs₁,hadm⟩ := ac_data_admissible_of_initial_envelope c H ε δ hc hH hε hδ
  refine ⟨min s₀ s₁,C,lt_min hs₀ hs₁,hC,?_⟩
  intro T e η M Cb hn h Sn Jn Kn hT hη hac hacn hSn hdn hbox hJn _hKn hjn hkn hmass hsmall hd
  have hJmass n : (∫ v in (0 : ℝ)..T, Jn n v) ≤ H * η := by
    have hK0 : 0 ≤ ∫ u in (0 : ℝ)..T, Kn n u := by
      apply intervalIntegral.integral_nonneg_of_ae_restrict hT.le
      filter_upwards [hkn n T ⟨hT.le,le_rfl⟩] with u hu
      exact (norm_nonneg _).trans hu
    linarith only [hmass n,hK0]
  have hadmiss n := hadm T e η M Cb (hn n) (Sn n) (Jn n) hT hη (hacn n)
    (hSn n) (hdn n) (hbox n) (hJn n) (hjn n 0 ⟨le_rfl,hT.le⟩) (hJmass n)
    (hsmall.trans (min_le_right _ _))
  obtain ⟨_,hv,_,hscale⟩ := data_parameters_tendsto_of_dataDist (e := e) hT.le hacn hac hd
  have hεh : datumVar h T ≤ ε := le_of_tendsto hv (Eventually.of_forall fun n => (hadmiss n).1)
  have hδh : chargedScale e h T ≤ δ := le_of_tendsto hscale
    (Eventually.of_forall fun n => (hadmiss n).2.1)
  obtain ⟨S,hS,hdS,hcS,_,hM,hcons,hpairs⟩ := hcore T e η M Cb hn h Sn Jn hT hη hac hacn hSn hdn hbox
      hJn
    (fun n => hjn n 0 ⟨le_rfl,hT.le⟩) hJmass (hsmall.trans (min_le_left _ _)) hd
  have hb n := hpair T e (hn n) h (Sn n) S hT (hacn n) (hadmiss n).1 (hadmiss n).2.1
    hac hεh hδh (hcons n).1 hcS
  have hd0 n : 0 ≤ dataDist (hn n) h T := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hMu := uniform_tendsto_of_norm_sub_le C₀ hd (fun n p hp => by
    have hh := (le_iSup₂ p hp).trans (hpairs n).2.2.1
    have hh' : ENNReal.ofReal ‖(Sn n).mu p.1 p.2 - S.mu p.1 p.2‖ ≤
        ENNReal.ofReal (C₀ * dataDist (hn n) h T) := by simpa only [ofReal_norm] using hh
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC₀.le (hd0 n))).1 hh')
  obtain ⟨_,_,_,_,_,_,hA,_,_⟩ := ac_uniform_limits_of_comparisons hT hc hC₀ hSn hS hbox
    (fun n => (hcons n).2.2) hM (fun n => ⟨(hpairs n).1,(hpairs n).2.1⟩) hd
  have hM0 : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans (hbox 0).1
  have hpot n : (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T,
      ‖deriv ((Sn n).A u) v - deriv (S.A u) v‖ₑ) +
      (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
        ‖deriv (fun s => (Sn n).A s v) u - deriv (fun s => S.A s v) u‖ₑ) ≤
          ENNReal.ofReal (6 * C * |e| * M * T * dataDist (hn n) h T) := by
    apply (hb n).2.2.2.2.2.trans
    apply ENNReal.ofReal_le_ofReal
    have hD := hd0 n
    have hsize : 2 * max (datumM (hn n) T) (datumM h T) ≤ 6 * M := by
      have hh := max_le (hcons n).2.2 hM
      linarith only [hh]
    calc
      _ ≤ C * |e| * (6 * M) * T * dataDist (hn n) h T := by gcongr
      _ = _ := by ring
  have hm := real_characteristic_limit_of_vanishing_bound hC.le hd0
    (fun n => (hb n).1.out) (fun n => (hb n).1.incoming)
    (hb 0).2.1.out (hb 0).2.1.incoming hMu hd (fun n => (hb n).2.2.2.2.1)
  have hp := real_characteristic_limit_of_vanishing_bound
    (by positivity : 0 ≤ 6 * C * |e| * M * T) hd0
    (fun n => (hb n).2.2.1.out) (fun n => (hb n).2.2.1.incoming)
    (hb 0).2.2.2.1.out (hb 0).2.2.2.1.incoming hA hd hpot
  exact ⟨S,hS,hdS,hm,hp,fun n => (hb n).2.2.2.2.1,hpot⟩

end EmcsfAcExtension.Local
