module

public import EmcsfAcExtension.Local.Limit.AcBridgeSequence
public import EmcsfAcExtension.Local.Limit.AcBridgeCovariant
public import EmcsfAcExtension.Local.Limit.AcBridgeScalarBounds
import EmcsfAcExtension.Local.Limit.AcBridgeUniform

/-! # The full general-AC scalar characteristic W¹¹ sequence record

internal project record item 7.5. Equality after broad uniqueness gives
regularity first; only then are the original scalar sections differentiated.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

/-- Strong characteristic scalar W¹¹ convergence of the original general AC
sequence. Uniform function convergence and uniform section L¹ derivative
convergence give the full W¹¹ conclusion with function-length factor at most `T`.
The incoming covariant and transported fields use their own actual potentials. -/
structure ScalarCharacteristicLimit (e T : ℝ) (Sn : ℕ → Fields) (S : Fields) : Prop where
  /-- Every original outgoing normalized section is AC. -/
  ac_out : ∀ n u, u ∈ Icc 0 T → AbsolutelyContinuousOnInterval ((Sn n).a u) u T
  /-- Every original incoming normalized section is AC. -/
  ac_in : ∀ n v, v ∈ Icc 0 T → AbsolutelyContinuousOnInterval (fun u => (Sn n).b u v) 0 v
  /-- The outgoing normalized limit sections are AC. -/
  limit_ac_out : ∀ u ∈ Icc 0 T, AbsolutelyContinuousOnInterval (S.a u) u T
  /-- The incoming normalized limit sections are AC. -/
  limit_ac_in : ∀ v ∈ Icc 0 T, AbsolutelyContinuousOnInterval (fun u => S.b u v) 0 v
  /-- Outgoing normalized fields converge uniformly in the fixed gauge. -/
  uniform_out : TendstoUniformlyOn (fun n => Function.uncurry (Sn n).a) (Function.uncurry S.a) atTop
      (triangle 0 T)
  /-- Incoming normalized fields converge uniformly in the fixed gauge. -/
  uniform_in : TendstoUniformlyOn (fun n => Function.uncurry (Sn n).b) (Function.uncurry S.b) atTop
      (triangle 0 T)
  /-- Ordinary outgoing derivatives converge uniformly over sections in L¹. -/
  strong_out : ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ u ∈ Icc 0 T,
    (∫ v in u..T, ‖deriv ((Sn n).a u) v - deriv (S.a u) v‖) < ρ
  /-- Ordinary incoming derivatives converge uniformly over sections in L¹. -/
  strong_in : ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ v ∈ Icc 0 T,
    (∫ u in (0 : ℝ)..v, ‖deriv (fun u => (Sn n).b u v) u - deriv (fun u => S.b u v) u‖) < ρ
  /-- Own-connection incoming derivatives converge uniformly over sections in L¹. -/
  strong_covariant : ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ v ∈ Icc 0 T,
    (∫ u in (0 : ℝ)..v, ‖incomingCovDeriv e (Sn n) u v - incomingCovDeriv e S u v‖) < ρ
  /-- Every actual parallel representative is AC. -/
  parallel_ac : ∀ n v, v ∈ Icc 0 T → AbsolutelyContinuousOnInterval
    (fun u => incomingParallel e (Sn n).A u v * (Sn n).b u v) 0 v
  /-- The limiting parallel representative is AC. -/
  limit_parallel_ac : ∀ v ∈ Icc 0 T, AbsolutelyContinuousOnInterval
    (fun u => incomingParallel e S.A u v * S.b u v) 0 v
  /-- Actual parallel representatives converge uniformly. -/
  parallel_uniform : TendstoUniformlyOn
    (fun n p => incomingParallel e (Sn n).A p.1 p.2 * (Sn n).b p.1 p.2)
    (fun p => incomingParallel e S.A p.1 p.2 * S.b p.1 p.2) atTop (triangle 0 T)
  /-- Derivatives of actual parallel representatives converge strongly in L¹,
  uniformly over all incoming sections. -/
  parallel_strong : ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ v ∈ Icc 0 T,
    (∫ u in (0 : ℝ)..v,
      ‖deriv (fun u => incomingParallel e (Sn n).A u v * (Sn n).b u v) u -
        deriv (fun u => incomingParallel e S.A u v * S.b u v) u‖) < ρ

/-- [internal]
The full general-AC sequence record, including own-connection and transported
incoming derivatives. The smallness threshold depends only on the fixed gap
`c` and envelope coefficient `H`, before time, coupling, common size, data and
all solutions. The derivative coefficient has this same fixed-parameter scope;
phase conversion retains its coupling and length factors. -/
theorem scalar_characteristic_strong_W11_of_inputs
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
          ScalarCharacteristicLimit e T Sn S ∧
          (∀ n u, u ∈ Icc 0 T → (∫ v in u..T,
            ‖deriv ((Sn n).a u) v - deriv (S.a u) v‖) ≤ C * dataDist (hn n) h T) ∧
          (∀ n v, v ∈ Icc 0 T → (∫ u in (0 : ℝ)..v,
            ‖deriv (fun u => (Sn n).b u v) u - deriv (fun u => S.b u v) u‖) ≤ C * dataDist (hn n) h
                T) := by
  obtain ⟨s,B,C,hs,hB,hC,hcore⟩ := ac_sequence_comparisons_of_inputs hex hstab c H hc hH
  refine ⟨s,C,hs,hC,?_⟩
  intro T e η M Cb hn h Sn Jn Kn hT hη hac hacn hSn hdn hbox hJn _hKn hjn hkn hmass hsmall hd
  have hJmass n : (∫ v in (0 : ℝ)..T, Jn n v) ≤ H * η := by
    have hK0 : 0 ≤ ∫ u in (0 : ℝ)..T, Kn n u := by
      apply intervalIntegral.integral_nonneg_of_ae_restrict hT.le
      filter_upwards [hkn n T ⟨hT.le,le_rfl⟩] with u hu
      exact (norm_nonneg _).trans hu
    linarith only [hmass n, hK0]
  obtain ⟨S,hS,hdS,_,hbS,hM,hcons,hpair⟩ := hcore T e η M Cb hn h Sn Jn hT hη hac hacn hSn hdn hbox
      hJn
    (fun n => hjn n 0 ⟨le_rfl,hT.le⟩) hJmass hsmall hd
  obtain ⟨_,_,_,ha,hb,_,hA,_,_⟩ := ac_uniform_limits_of_comparisons hT hc hC hSn hS hbox
    (fun n => (hcons n).2.2) hM (fun n => ⟨(hpair n).1,(hpair n).2.1⟩) hd
  have hder n := (hpair n).1.derivative_bounds_of_ac hC.le ((hcons n).2.1).1 hbS.1
    ((hcons n).2.1).2.1 hbS.2.1
  have hder0 : Tendsto (fun n => C * dataDist (hn n) h T) atTop (𝓝 0) :=
      by simpa using hd.const_mul C
  have hstrongo : ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ u ∈ Icc 0 T,
      (∫ v in u..T, ‖deriv ((Sn n).a u) v - deriv (S.a u) v‖) < ρ := by
    intro ρ hρ
    obtain ⟨N,hN⟩ := eventually_atTop.1 ((tendsto_order.1 hder0).2 ρ hρ)
    exact ⟨N, fun n hn u hu => ((hder n).1 u hu).trans_lt (hN n hn)⟩
  have hstrongi : ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ v ∈ Icc 0 T,
      (∫ u in (0 : ℝ)..v, ‖deriv (fun u => (Sn n).b u v) u - deriv (fun u => S.b u v) u‖) < ρ := by
    intro ρ hρ
    obtain ⟨N,hN⟩ := eventually_atTop.1 ((tendsto_order.1 hder0).2 ρ hρ)
    exact ⟨N, fun n hn v hv => ((hder n).2 v hv).trans_lt (hN n hn)⟩
  have hvar v (hv : v ∈ Icc 0 T) : covVarIn e S.A S.b 0 v v ≤ ENNReal.ofReal (B * datumVar h T) :=
    (le_iSup₂ v hv).trans (le_add_self.trans hbS.2.2.2.1)
  obtain ⟨hcov,hpu,hps⟩ := covariant_scalar_limits_of_ordinary hT
    (mul_nonneg hB.le ENNReal.toReal_nonneg) hSn hS
    (fun n => ((hcons n).2.1).2.1) hbS.2.1 hvar hA hb hstrongi
  have hpac (F : Fields) (hF : IsSolution e F (triangle 0 T)) v (hv : v ∈ Icc 0 T)
      (hbi : AbsolutelyContinuousOnInterval (fun u => F.b u v) 0 v) :=
    (incoming_parallel_ac_deriv_of_ac (e := e) hv.1
      (hF.cont_A.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun u hu => ⟨hu.1,hu.2,hv.2⟩)) hbi).1
  exact ⟨S,hS,hdS,⟨fun n => ((hcons n).2.1).1, fun n => ((hcons n).2.1).2.1,
    hbS.1,hbS.2.1,ha,hb,hstrongo,hstrongi,hcov,
    fun n v hv => hpac _ (hSn n) v hv (((hcons n).2.1).2.1 v hv),
    fun v hv => hpac _ hS v hv (hbS.2.1 v hv),hpu,hps⟩,
    fun n => (hder n).1,fun n => (hder n).2⟩

end EmcsfAcExtension.Local
