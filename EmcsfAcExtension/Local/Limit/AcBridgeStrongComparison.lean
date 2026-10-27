module

public import EmcsfAcExtension.Local.Limit.StabilitySettings
public import EmcsfAcExtension.Local.Limit.AcBridgeDerivative
import EmcsfAcExtension.Local.Limit.AcBridgeSmooth
import EmcsfAcExtension.Local.Limit.ExistencePointwise
import EmcsfAcExtension.Local.Limit.StabilityPointwise
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassRegularity
import EmcsfAcExtension.Local.Stability.GeomStrongMassInRaw
import EmcsfAcExtension.Local.Calculus.Partials

/-! # Strong mass and potential comparisons of constructed AC pairs

Each smooth witness has a strong derivative limit in both characteristic
families. Completeness supplies the endpoint AC needed to pass the pair
bound by variation semicontinuity, retaining the sum and coefficient one.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

/-- Both characteristic families of a real field are AC, including all
axis and outer endpoints. This conclusion record carries no estimate constant. -/
structure RealCharacteristicAC (T : ℝ) (f : ℝ → ℝ → ℝ) : Prop where
  /-- Outgoing AC on the complete section. -/
  out : ∀ u ∈ Icc 0 T, AbsolutelyContinuousOnInterval (f u) u T
  /-- Incoming AC on the complete section. -/
  incoming : ∀ v ∈ Icc 0 T, AbsolutelyContinuousOnInterval (fun u => f u v) 0 v

/-- Identify both real strong derivative records on one classical witness.
The explicit coefficients `C,K` retain their supplied scope; the potential
scale is exactly `|e|MT`. Data Cauchy control and pair bounds are explicit
analytic premises of this helper, discharged by the constructed-pair export. -/
theorem strong_mass_potential_of_classical_witness
    {e T ε M C K : ℝ} {Sn : ℕ → Fields} {hn : ℕ → ℝ → ℂ} {S : Fields}
    (hC : 0 < C) (hK : 0 < K)
    (hs : ∀ n, StabSetting e T ε M 1 (Sn n) (hn n))
    (hl : StrongLimit e T Sn S)
    (hd : ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, dataDist (hn n) (hn m) T < ρ)
    (hvalue : ∀ n m, supDist T (Sn n).mu (Sn m).mu ≤ ENNReal.ofReal (C * dataDist (hn n) (hn m) T))
    (hm : ∀ n m,
      (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T, ‖deriv ((Sn n).mu u) v - deriv ((Sn m).mu u) v‖ₑ) +
      (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
        ‖deriv (fun s => (Sn n).mu s v) u - deriv (fun s => (Sn m).mu s v) u‖ₑ) ≤
          ENNReal.ofReal (K * dataDist (hn n) (hn m) T))
    (hp : ∀ n m,
      (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T, ‖deriv ((Sn n).A u) v - deriv ((Sn m).A u) v‖ₑ) +
      (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
        ‖deriv (fun s => (Sn n).A s v) u - deriv (fun s => (Sn m).A s v) u‖ₑ) ≤
          ENNReal.ofReal (K * |e| * M * T * dataDist (hn n) (hn m) T)) :
    RealCharacteristicLimit T (fun n => (Sn n).mu) S.mu ∧
      RealCharacteristicLimit T (fun n => (Sn n).A) S.A := by
  have hgeom := hl.lower_geometry_of_settings hs
  have hr p (hp : p ∈ triangle 0 T) (hlt : p.1 < p.2) : 0 < S.r p.1 p.2 :=
    (div_pos (sub_pos.2 hlt) (by norm_num : (0 : ℝ) < 4)).trans_le (hgeom p hp).2.2
  have hd0 n m : 0 ≤ dataDist (hn n) (hn m) T :=
    add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hMu := real_uniform_of_pair_bound hC hd (fun n m p hp => by
    have hh := (le_iSup₂ p hp).trans (hvalue n m)
    have hh' : ENNReal.ofReal |(Sn n).mu p.1 p.2 - (Sn m).mu p.1 p.2| ≤
        ENNReal.ofReal (C * dataDist (hn n) (hn m) T) := by
      simpa only [← ofReal_norm,Real.norm_eq_abs] using hh
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC.le (hd0 n m))).1 hh')
    (fun p hp => hl.tendsto_mu_of_radius_pos (fun n => (hs n).c1) hr hp)
  refine ⟨real_characteristic_limit_of_pair_bound hK.le hd0
    (fun n u hu => stab_mu_out_ac (hs n) hu.1 hu.2 le_rfl)
    (fun n v hv => stab_mu_in_ac (hs n) le_rfl hv.1 hv.2) hMu hd hm, ?_⟩
  have hT := (hs 0).pos
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans (hs 0).box.1
  apply real_characteristic_limit_of_pair_bound (by positivity : 0 ≤ K * |e| * M * T) hd0
    (Fn := fun n => (Sn n).A) (f := S.A) _ _ hl.unif_A hd hp
  · intro n u hu
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le hu.2]
    exact (hs n).c1.c1_A.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun v hv => ⟨hu.1,hv.1,hv.2⟩)
  · intro n v hv
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le hv.1]
    exact (hs n).c1.c1_A.comp (contDiffOn_id.prodMk contDiffOn_const)
      (fun u hu => ⟨hu.1,hu.2,hv.2⟩)

/-- Constructed mass and potential pairs retain both strong derivative
comparisons. The positive thresholds and coefficient are universal, before
all data, coupling, time and fields. The comparison size is literally twice
the maximum datum size, with the potential scale `|e|MT` retained. -/
theorem constructed_mass_potential_pairs_of_inputs (hstab : StabExtendedStmt) :
    ∃ ε δ C : ℝ, 0 < ε ∧ 0 < δ ∧ 0 < C ∧
      ∀ (T e : ℝ) (h₁ h₂ : ℝ → ℂ) (S₁ S₂ : Fields), 0 < T →
        AbsolutelyContinuousOnInterval h₁ 0 T → datumVar h₁ T ≤ ε → chargedScale e h₁ T ≤ δ →
        AbsolutelyContinuousOnInterval h₂ 0 T → datumVar h₂ T ≤ ε → chargedScale e h₂ T ≤ δ →
        IsConstructedLimit e T h₁ S₁ → IsConstructedLimit e T h₂ S₂ →
        RealCharacteristicAC T S₁.mu ∧ RealCharacteristicAC T S₂.mu ∧
        RealCharacteristicAC T S₁.A ∧ RealCharacteristicAC T S₂.A ∧
        ((⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T, ‖deriv (S₁.mu u) v - deriv (S₂.mu u) v‖ₑ) +
          (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
            ‖deriv (fun s => S₁.mu s v) u - deriv (fun s => S₂.mu s v) u‖ₑ) ≤
              ENNReal.ofReal (C * dataDist h₁ h₂ T)) ∧
        ((⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T, ‖deriv (S₁.A u) v - deriv (S₂.A u) v‖ₑ) +
          (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
            ‖deriv (fun s => S₁.A s v) u - deriv (fun s => S₂.A s v) u‖ₑ) ≤
              ENNReal.ofReal (C * |e| * (2 * max (datumM h₁ T) (datumM h₂ T)) * T * dataDist h₁ h₂
                  T)) := by
  obtain ⟨η,Cm,Kp,hη,hCm,hKp,hpairs⟩ := smooth_mass_potential_pairs_of_inputs hstab
  obtain ⟨ηv,Cv,hηv,hCv,hcomp⟩ := hstab 1 (by norm_num)
  obtain ⟨ε,δ,q,hε,hδ,_,ht⟩ := comparison_tails_with_cauchy_of_constructed_limits
    (min η ηv) (lt_min hη hηv)
  let K := Cm + Kp
  have hK : 0 < K := add_pos hCm hKp
  refine ⟨ε,δ,K,hε,hδ,hK,?_⟩
  intro T e h₁ h₂ S₁ S₂ hT hac₁ hd₁ he₁ hac₂ hd₂ he₂ hc₁ hc₂
  obtain ⟨Sn₁,Sn₂,hn₁,hn₂,M,hs₁,hs₂,hl₁,hl₂,hd,hsmall,hM,hC₁,hC₂⟩ :=
    ht T e h₁ h₂ S₁ S₂ hT hac₁ hd₁ he₁ hac₂ hd₂ he₂ hc₁ hc₂
  have hM0 : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans (hs₁ 0).box.1
  have pair (F G : Fields) (f g : ℝ → ℂ)
      (hf : StabSetting e T q M 1 F f) (hg : StabSetting e T q M 1 G g) :=
    hpairs T e q M F G f g hf hg (hsmall.trans (min_le_left _ _))
  have mass (F G : Fields) (f g : ℝ → ℂ)
      (hf : StabSetting e T q M 1 F f) (hg : StabSetting e T q M 1 G g) :=
    (pair F G f g hf hg).1.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hKp.le)
        (add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg)))
  have pot (F G : Fields) (f g : ℝ → ℂ)
      (hf : StabSetting e T q M 1 F f) (hg : StabSetting e T q M 1 G g) :=
    (pair F G f g hf hg).2.trans (ENNReal.ofReal_le_ofReal
      (show Kp * |e| * M * T * dataDist f g T ≤ K * |e| * M * T * dataDist f g T from by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCm.le) (abs_nonneg e)) hM0) hT.le)
          (add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg)))
  have value (F G : Fields) (f g : ℝ → ℂ)
      (hf : StabSetting e T q M 1 F f) (hg : StabSetting e T q M 1 G g) :=
    (hcomp T e q M F G f g hf hg (hsmall.trans (min_le_right _ _))).extra_mu
  obtain ⟨m₁,a₁⟩ := strong_mass_potential_of_classical_witness hCv hK hs₁ hl₁ hC₁
    (fun n m => value _ _ _ _ (hs₁ n) (hs₁ m))
    (fun n m => mass _ _ _ _ (hs₁ n) (hs₁ m))
    (fun n m => pot _ _ _ _ (hs₁ n) (hs₁ m))
  obtain ⟨m₂,a₂⟩ := strong_mass_potential_of_classical_witness hCv hK hs₂ hl₂ hC₂
    (fun n m => value _ _ _ _ (hs₂ n) (hs₂ m))
    (fun n m => mass _ _ _ _ (hs₂ n) (hs₂ m))
    (fun n m => pot _ _ _ _ (hs₂ n) (hs₂ m))
  refine ⟨⟨m₁.limit_ac_out,m₁.limit_ac_in⟩,⟨m₂.limit_ac_out,m₂.limit_ac_in⟩,
    ⟨a₁.limit_ac_out,a₁.limit_ac_in⟩,⟨a₂.limit_ac_out,a₂.limit_ac_in⟩,?_,?_⟩
  · exact real_characteristic_pair_of_pointwise m₁.ac_out m₂.ac_out m₁.ac_in m₂.ac_in
      m₁.limit_ac_out m₂.limit_ac_out m₁.limit_ac_in m₂.limit_ac_in
      (fun p hp => m₁.uniform.tendsto_at hp) (fun p hp => m₂.uniform.tendsto_at hp)
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hd.const_mul K))
      (fun n => mass _ _ _ _ (hs₁ n) (hs₂ n))
  · rw [← hM]
    exact real_characteristic_pair_of_pointwise a₁.ac_out a₂.ac_out a₁.ac_in a₂.ac_in
      a₁.limit_ac_out a₂.limit_ac_out a₁.limit_ac_in a₂.limit_ac_in
      (fun p hp => hl₁.unif_A.tendsto_at hp) (fun p hp => hl₂.unif_A.tendsto_at hp)
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hd.const_mul (K * |e| * M * T)))
      (fun n => pot _ _ _ _ (hs₁ n) (hs₂ n))

end EmcsfAcExtension.Local
