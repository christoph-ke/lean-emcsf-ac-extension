module

public import EmcsfAcExtension.Local.Assembly.Inputs
public import EmcsfAcExtension.Local.Limit.AcBridgeStrongComparison
import EmcsfAcExtension.Local.Construction.WireC1Bound
import EmcsfAcExtension.Local.Stability.ExtendedLipschitz
import EmcsfAcExtension.Local.Limit.Existence
import EmcsfAcExtension.Local.Limit.UIAux
import EmcsfAcExtension.Local.Limit.StabilityPointwise
import EmcsfAcExtension.Local.Limit.AcBridgePotential
import EmcsfAcExtension.Local.Limit.AcBridgeMaxwellDensity
import EmcsfAcExtension.Local.Calculus.Reconstruction
import EmcsfAcExtension.Local.Broad.GeometryRay
import EmcsfAcExtension.Infra.Null.IntegralForm
import EmcsfAcExtension.Local.Limit.AcBridgeSmooth
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassRegularity
import EmcsfAcExtension.Local.Stability.GeomStrongMassInRaw

/-! # Nondegenerate characteristic AC geometry in the constructed limit

The same limit carries uniform primary geometry, C¹ radius, every frozen
integral identity and both incoming and outgoing potential AC. The potential
regularity comes from strong derivative completeness, rather than BV bounds.
charged_SF_new_version.tex:L6463–6474.
-/

public section

open Set MeasureTheory Complex Filter Topology

namespace EmcsfAcExtension.Local

private theorem geometric_primitives_of_ac {e T C : ℝ} {h : ℝ → ℂ} {S : Fields}
    (hS : IsSolution e S (triangle 0 T)) (hb : ExistenceBounds C e T h S)
    (hA : RealCharacteristicAC T S.A) :
    (∀ u ∈ Icc 0 T, ∀ v ∈ Icc u T,
      IntegralForm (S.r u) (S.lam u) u v ∧
      IntegralForm (S.nu u) (S.rUV u) u v ∧
      IntegralForm (S.m u) (S.mV u) u v ∧
      IntegralForm (S.Q u) (S.QV e u) u v ∧
      IntegralForm (S.A u) (S.AV u) u v) ∧
    (∀ v ∈ Icc 0 T, ∀ u ∈ Icc 0 v,
      IntegralForm (fun s => S.r s v) (fun s => S.nu s v) u v ∧
      IntegralForm (fun s => S.lam s v) (fun s => S.rUV s v) u v ∧
      IntegralForm (fun s => S.m s v) (fun s => S.mU s v) u v ∧
      IntegralForm (fun s => S.Q s v) (fun s => S.QU e s v) u v) := by
  obtain ⟨_,_,_,_,_,_,_,hACo,hACi,_,_⟩ := hb
  constructor
  · intro u hu v hv
    have hs : outSeg u u v ⊆ triangle 0 T := by
      rintro ⟨x,y⟩ ⟨rfl,hy⟩
      exact ⟨hu.1,hy.1,hy.2.trans hv.2⟩
    have hac := hS.ac_out u u v hv.1 hs
    have hsub : uIcc u v ⊆ uIcc u T := by
      rw [uIcc_of_le hv.1,uIcc_of_le hu.2]
      exact Icc_subset_Icc_right hv.2
    refine ⟨integralForm_of_ac_of_interior_deriv hv.1 hac.1
        (fun x hx => IsSolution.hasDerivAt_radius_out hS hs hx),
      integralForm_of_ac_of_interior_deriv hv.1 ((hACo u hu).2.1.mono hsub)
        (fun x hx => Broad.hasDerivAt_nu_out hS hs hx),
      integralForm_of_ac_of_interior_deriv hv.1 hac.2.1
        (fun x hx => IsSolution.hasDerivAt_mass_out hS hs hx),
      integralForm_of_ac_of_interior_deriv hv.1 hac.2.2.1
        (fun x hx => IsSolution.hasDerivAt_charge_out hS hs hx),?_⟩
    apply integralForm_of_ac_of_ae_deriv_eq ((hA.out u hu).mono hsub)
    rw [uIcc_of_le hv.1]
    exact ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc_right hv.2)
      (hS.potential_derivative_out_ae hu)
  · intro v hv u hu
    have hs : inSeg u v v ⊆ triangle 0 T := by
      rintro ⟨x,y⟩ ⟨hx,hxv,rfl⟩
      exact ⟨hu.1.trans hx,hxv,hv.2⟩
    have hac := hS.ac_in u v v hu.2 hs
    have hsub : uIcc u v ⊆ uIcc 0 v := by
      rw [uIcc_of_le hu.2,uIcc_of_le hv.1]
      exact Icc_subset_Icc hu.1 le_rfl
    refine ⟨integralForm_of_ac_of_interior_deriv hu.2 hac.1
        (fun x hx => Broad.hasDerivAt_radius_in hS hs hx),
      integralForm_of_ac_of_interior_deriv hu.2 ((hACi v hv).1.mono hsub)
        (fun x hx => Broad.hasDerivAt_lam_in hS hs hx),
      integralForm_of_ac_of_interior_deriv hu.2 hac.2.1
        (fun x hx => IsSolution.hasDerivAt_mass_in hS hs hx),?_⟩
    apply integralForm_of_ac_of_ae_deriv_eq hac.2.2.1
    rw [uIcc_of_le hu.2]
    exact ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc hu.1 le_rfl)
      (hS.charge_derivatives_ae.2 v hv)

/-- [node restart-sec-independent-null-construction#geometry-ac-limit]
Nondegenerate geometry and its characteristic identities for the actual
constructed limit. `IsConstructedLimit` retains the uniform geometric
approximation, `IsSolution` the positive expansions/gap and integral equations,
and `ExistenceBounds` both geometric AC families and the C¹ radius. Both
potential AC directions, fixed quarter lower bounds, and all closed-section
geometric, Maxwell and potential primitives are explicit. The positive thresholds and bound
coefficient are universal, before time, coupling, data and approximants. -/
theorem constructed_geometry_ac_limit :
    ∃ ε δ C : ℝ, 0 < ε ∧ 0 < δ ∧ 0 < C ∧
      ∀ (T e : ℝ) (h : ℝ → ℂ), 0 < T →
        AbsolutelyContinuousOnInterval h 0 T → datumVar h T ≤ ε → chargedScale e h T ≤ δ →
        ∃ S : Fields, IsSolution e S (triangle 0 T) ∧ IsRestartData S h T ∧
          IsConstructedLimit e T h S ∧ ExistenceBounds C e T h S ∧
          RealCharacteristicAC T S.A ∧
          (∀ p ∈ triangle 0 T, 1/4 ≤ S.lam p.1 p.2 ∧ 1/4 ≤ -S.nu p.1 p.2 ∧
            1/4 ≤ 1 - S.mu p.1 p.2 ∧ (p.2-p.1)/4 ≤ S.r p.1 p.2) ∧
          (∀ u ∈ Icc 0 T, ∀ v ∈ Icc u T,
            IntegralForm (S.r u) (S.lam u) u v ∧
            IntegralForm (S.nu u) (S.rUV u) u v ∧
            IntegralForm (S.m u) (S.mV u) u v ∧
            IntegralForm (S.Q u) (S.QV e u) u v ∧
            IntegralForm (S.A u) (S.AV u) u v) ∧
          (∀ v ∈ Icc 0 T, ∀ u ∈ Icc 0 v,
            IntegralForm (fun s => S.r s v) (fun s => S.nu s v) u v ∧
            IntegralForm (fun s => S.lam s v) (fun s => S.rUV s v) u v ∧
            IntegralForm (fun s => S.m s v) (fun s => S.mU s v) u v ∧
            IntegralForm (fun s => S.Q s v) (fun s => S.QU e s v) u v) ∧
          ∃ (Sn : ℕ → Fields) (hn : ℕ → ℝ → ℂ),
            (∀ n, IsC1Solution e (Sn n) (triangle 0 T) ∧ IsRestartData (Sn n) (hn n) T) ∧
            StrongLimit e T Sn S ∧
            RealCharacteristicLimit T (fun n => (Sn n).mu) S.mu ∧
            RealCharacteristicLimit T (fun n => (Sn n).A) S.A ∧
            TendstoUniformlyOn (fun n => Function.uncurry (Sn n).Omega2)
              (Function.uncurry S.Omega2) atTop (triangle 0 T) := by
  obtain ⟨ε₁, δ₁, C₁, hε₁, hδ₁, hC₁, hex⟩ :=
    ac_data_existence_of_inputs whole_triangle_existence stab_extended
  obtain ⟨ε₂, δ₂, C₂, hε₂, hδ₂, _, hpair⟩ :=
    constructed_mass_potential_pairs_of_inputs stab_extended
  obtain ⟨η,Cm,Kp,hη,hCm,hKp,hpairs⟩ := smooth_mass_potential_pairs_of_inputs stab_extended
  obtain ⟨ηv,Cv,hηv,hCv,hcomp⟩ := stab_extended 1 (by norm_num)
  obtain ⟨ε₃,δ₃,q,hε₃,hδ₃,_,ht⟩ := comparison_tails_with_cauchy_of_constructed_limits
    (min η ηv) (lt_min hη hηv)
  refine ⟨min ε₁ (min ε₂ ε₃), min δ₁ (min δ₂ δ₃), C₁,
    lt_min hε₁ (lt_min hε₂ hε₃), lt_min hδ₁ (lt_min hδ₂ hδ₃), hC₁, ?_⟩
  intro T e h hT hac hd he
  have hd₂ := hd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have he₂ := he.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hd₃ := hd.trans ((min_le_right _ _).trans (min_le_right _ _))
  have he₃ := he.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨S,hS,hdata,hc,hb⟩ := hex T e h hT hac
    (hd.trans (min_le_left _ _)) (he.trans (min_le_left _ _))
  have hp := hpair T e h h S S hT hac hd₂ he₂ hac hd₂ he₂ hc hc
  obtain ⟨Sn,_,hn,_,M,hs,_,hl,_,_,hsmall,_,hCauchy,_⟩ :=
    ht T e h h S S hT hac hd₃ he₃ hac hd₃ he₃ hc hc
  have hM0 : 0 ≤ M := zero_le_one.trans (hs 0).box.1
  let K := Cm + Kp
  have hK : 0 < K := add_pos hCm hKp
  have mass n m := (hpairs T e q M (Sn n) (Sn m) (hn n) (hn m)
    (hs n) (hs m) (hsmall.trans (min_le_left _ _))).1
  have pot n m := (hpairs T e q M (Sn n) (Sn m) (hn n) (hn m)
    (hs n) (hs m) (hsmall.trans (min_le_left _ _))).2
  obtain ⟨hm,hA⟩ := strong_mass_potential_of_classical_witness hCv hK hs hl hCauchy
    (fun n m => (hcomp T e q M (Sn n) (Sn m) (hn n) (hn m)
      (hs n) (hs m) (hsmall.trans (min_le_right _ _))).extra_mu)
    (fun n m => (mass n m).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hKp.le)
        (add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg))))
    (fun n m => (pot n m).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCm.le) (abs_nonneg e))
            hM0) hT.le) (add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg))))
  have cMu := hm.uniform.continuousOn
    (Filter.Eventually.of_forall fun n => (hs n).c1.continuousOn_mu hT).frequently
  have hnlam := hl.unif_nu.tendstoLocallyUniformlyOn.mul₀
    hl.unif_lam.tendstoLocallyUniformlyOn hS.cont_nu hS.cont_lam
  have hnum := (uniformContinuous_mul_left' (-4 : ℝ)).comp_tendstoLocallyUniformlyOn hnlam
  have hden := ((tendsto_const_nhds.tendstoUniformlyOn_const (triangle 0 T) :
      TendstoUniformlyOn (fun _ : ℕ => fun _ : ℝ × ℝ => (1 : ℝ)) (fun _ => 1)
        atTop (triangle 0 T)).tendstoLocallyUniformlyOn).sub hm.uniform.tendstoLocallyUniformlyOn
  have hO := hnum.div₀ hden
    (by simpa only [mul_assoc] using! (continuousOn_const.mul hS.cont_nu).mul hS.cont_lam)
    (continuousOn_const.sub cMu) (fun p hp => (hS.one_sub_mu_pos p hp).ne')
  have hO' : TendstoLocallyUniformlyOn (fun n => Function.uncurry (Sn n).Omega2)
      (Function.uncurry S.Omega2) atTop (triangle 0 T) := by
    convert hO using 1 <;> first
      | (funext n p; simp only [Fields.Omega2, Function.uncurry_def, Function.comp_def,
          Pi.div_apply, Pi.mul_apply, Pi.sub_apply]; ring)
      | (funext p; simp only [Fields.Omega2, Function.uncurry_def, Function.comp_def,
          Pi.div_apply, Pi.mul_apply, Pi.sub_apply]; ring)
  have hΩ := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
    (isCompact_triangle 0 T)).1 hO'
  obtain ⟨hout,hin⟩ := geometric_primitives_of_ac hS hb hp.2.2.1
  have hgeom := hl.lower_geometry_of_settings hs
  refine ⟨S,hS,hdata,hc,hb,hp.2.2.1,?_,hout,hin,Sn,hn,
    fun n => ⟨(hs n).c1,(hs n).data⟩,hl,hm,hA,hΩ⟩
  intro p hp
  exact ⟨(hgeom p hp).1,(hgeom p hp).2.1,
    ge_of_tendsto ((hm.uniform.tendsto_at hp).const_sub 1)
      (Filter.Eventually.of_forall fun n => ((hs n).box.2 p hp).2.2.2.2.1),
    (hgeom p hp).2.2⟩

end EmcsfAcExtension.Local
