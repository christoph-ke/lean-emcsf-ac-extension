module

public import EmcsfAcExtension.Local.Limit.Construct2Cauchy
public import EmcsfAcExtension.Local.Defs.Limit
import EmcsfAcExtension.Local.Limit.Scalar
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Infra.AC.Complex

/-! # Natural geometric AC from the full smooth comparison

The pure geometric derivative clause of StabBounds gives real L¹-Cauchy
derivatives. Complexification lets the landed family completeness theorem
identify the real natural expansion limits without a derivative supremum.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

private theorem real_ac_family {ι : Type*} {a b : ι → ℝ}
    {F : ℕ → ι → ℝ → ℝ} {f : ι → ℝ → ℝ}
    (hab : ∀ i, a i ≤ b i)
    (hF : ∀ n i, AbsolutelyContinuousOnInterval (F n i) (a i) (b i))
    (hl : TendstoUniformlyOn (fun n (p : ι × ℝ) => F n p.1 p.2) (fun p => f p.1 p.2)
      atTop {p | p.2 ∈ Icc (a p.1) (b p.1)})
    (hc : ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, ∀ i,
      (∫ x in a i..b i, ‖deriv (F n i) x - deriv (F m i) x‖) < ρ) :
    ∀ i, AbsolutelyContinuousOnInterval (f i) (a i) (b i) := by
  have he n i : deriv (fun x => (F n i x : ℂ)) =ᵐ[volume.restrict (Icc (a i) (b i))]
      (fun x => ((deriv (F n i) x : ℝ) : ℂ)) := by
    filter_upwards [ae_restrict_of_ae (hF n i).ae_differentiableAt_of_mem_uIcc,
      ae_restrict_mem measurableSet_Icc] with x hx hmem
    exact (hx (by simpa only [uIcc_of_le (hab i)] using hmem)).hasDerivAt.ofReal_comp.deriv
  have hcl : ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, ∀ i,
      (∫ x in a i..b i, ‖deriv (fun x => (F n i x : ℂ)) x -
        deriv (fun x => (F m i x : ℂ)) x‖) < ρ := by
    intro ρ hρ
    obtain ⟨N, hN⟩ := hc ρ hρ
    refine ⟨N, fun n hn m hm i => ?_⟩
    have hEq : (∫ x in a i..b i, ‖deriv (fun x => (F n i x : ℂ)) x -
        deriv (fun x => (F m i x : ℂ)) x‖) =
        ∫ x in a i..b i, ‖deriv (F n i) x - deriv (F m i) x‖ := by
      apply intervalIntegral.integral_congr_ae_restrict
      rw [uIoc_of_le (hab i)]
      filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self (he n i),
        ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self (he m i)] with x hn hm
      rw [hn, hm, ← Complex.ofReal_sub, Complex.norm_real]
    rw [hEq]
    exact hN n hn m hm i
  obtain ⟨hac, _, _⟩ := ac_family_limit_of_derivative_cauchy
    (s := a) (t := b) (f := fun i x => (f i x : ℂ)) hab (fun n i => (hF n i).ofReal)
    (Complex.isometry_ofReal.uniformContinuous.comp_tendstoUniformlyOn hl) hcl
  intro i
  simpa only [Complex.ofReal_re] using (hac i).re

private theorem integral_derivative_sub_le {F G q r : ℝ → ℝ} {a b D : ℝ}
    (hab : a ≤ b) (hD : 0 ≤ D)
    (hF : AbsolutelyContinuousOnInterval F a b) (hG : AbsolutelyContinuousOnInterval G a b)
    (hq : deriv F =ᵐ[volume.restrict (Icc a b)] q)
    (hr : deriv G =ᵐ[volume.restrict (Icc a b)] r)
    (hb : (∫⁻ x in Icc a b, ‖q x - r x‖ₑ) ≤ ENNReal.ofReal D) :
    (∫ x in a..b, ‖deriv F x - deriv G x‖) ≤ D := by
  apply (ENNReal.ofReal_le_ofReal_iff hD).1
  have hi : IntegrableOn (fun x => deriv F x - deriv G x) (Icc a b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).1
      (hF.intervalIntegrable_deriv.sub hG.intervalIntegrable_deriv)
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    ofReal_integral_norm_eq_lintegral_enorm hi]
  apply le_trans ?_ hb
  apply lintegral_mono_ae
  filter_upwards [hq, hr] with x hx hy
  rw [hx, hy]

/-- The actual outgoing lambda and incoming nu limits are AC, from the
pending full comparison's pure geometric derivative clause. The threshold
depends only on `A`, uniformly in time, coupling, data and derivative suprema.
This `_of_` helper consumes an already constructed primary strong limit. -/
theorem Null.geometry_natural_ac_of_inputs (hstab : StabExtendedStmt) (A : ℝ) (hA : 0 < A) :
    ∃ η : ℝ, 0 < η ∧
      ∀ (T e ε M : ℝ) (Sn : ℕ → Fields) (hn : ℕ → ℝ → ℂ) (h : ℝ → ℂ) (S : Fields),
        (∀ n, StabSetting e T ε M A (Sn n) (hn n)) →
        AbsolutelyContinuousOnInterval h 0 T → (∀ n, hn n 0 = h 0) →
        Tendsto (fun n => datumVar (hn n - h) T) atTop (𝓝 0) →
        ε ^ 2 + sigma e M T ≤ η → StrongLimit e T Sn S →
        (∀ u ∈ Icc 0 T, AbsolutelyContinuousOnInterval (S.lam u) u T) ∧
        (∀ v ∈ Icc 0 T, AbsolutelyContinuousOnInterval (fun u => S.nu u v) 0 v) := by
  obtain ⟨η, C, hη, hC, hcomp⟩ := hstab A hA
  refine ⟨η, hη, ?_⟩
  intro T e ε M Sn hn h S hs hac hv hlim hsmall hstrong
  have ha n (i : Icc (0 : ℝ) T) : AbsolutelyContinuousOnInterval ((Sn n).lam i.1) i.1 T := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le i.property.2]
    exact (hs n).c1.c1_lam.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun x hx => ⟨i.property.1, hx.1, hx.2⟩)
  have hb n (i : Icc (0 : ℝ) T) :
      AbsolutelyContinuousOnInterval (fun u => (Sn n).nu u i.1) 0 i.1 := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le i.property.1]
    exact (hs n).c1.c1_nu.comp (contDiffOn_id.prodMk contDiffOn_const)
      (fun x hx => ⟨hx.1, hx.2, i.property.2⟩)
  have hda n (i : Icc (0 : ℝ) T) : deriv ((Sn n).lam i.1) =ᵐ[volume.restrict (Icc i.1 T)]
      pdV (triangle 0 T) (Sn n).lam i.1 := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact deriv_eq_pdV (hs n).c1.c1_lam ⟨i.property.1, hx.1.le, hx.2.le⟩
      (s := Icc i.1 T) (fun y hy => ⟨i.property.1, hy.1, hy.2⟩) (Icc_mem_nhds hx.1 hx.2)
  have hdb n (i : Icc (0 : ℝ) T) : deriv (fun u => (Sn n).nu u i.1) =ᵐ[volume.restrict (Icc 0 i.1)]
      (fun u => pdU (triangle 0 T) (Sn n).nu u i.1) := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact deriv_eq_pdU (hs n).c1.c1_nu ⟨hx.1.le, hx.2.le, i.property.2⟩
      (s := Icc 0 i.1) (fun y hy => ⟨hy.1, hy.2, i.property.2⟩) (Icc_mem_nhds hx.1 hx.2)
  have hp n m := (hcomp T e ε M (Sn n) (Sn m) (hn n) (hn m) (hs n) (hs m) hsmall).geomStrong
  have hdist := data_dist_cauchy_of_stabSetting hs hac hv hlim
  have hnonneg n m : 0 ≤ C * dataDist (hn n) (hn m) T :=
    mul_nonneg hC.le (add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg)
  constructor
  · have hla : TendstoUniformlyOn
        (fun n (p : Icc (0 : ℝ) T × ℝ) => (Sn n).lam p.1.1 p.2)
        (fun p => S.lam p.1.1 p.2) atTop {p | p.2 ∈ Icc p.1.1 T} :=
      (hstrong.unif_lam.comp (fun p : Icc (0 : ℝ) T × ℝ => (p.1.1, p.2))).mono
        (fun p hp => ⟨p.1.property.1, hp.1, hp.2⟩)
    have h := real_ac_family (a := fun i : Icc (0 : ℝ) T => i.1) (b := fun _ => T)
      (f := fun i x => S.lam i.1 x) (fun i => i.property.2) ha hla (by
        intro ρ hρ
        obtain ⟨N, hN⟩ := hdist (ρ / C) (div_pos hρ hC)
        refine ⟨N, fun n hn' m hm' i => ?_⟩
        apply (integral_derivative_sub_le i.property.2 (hnonneg n m) (ha n i) (ha m i)
          (hda n i) (hda m i) ((le_iSup₂ i.1 i.property).trans (le_self_add.trans (hp n
              m)))).trans_lt
        exact (lt_div_iff₀' hC).1 (hN n hn' m hm'))
    exact fun u hu => h ⟨u, hu⟩
  · have hlb : TendstoUniformlyOn
        (fun n (p : Icc (0 : ℝ) T × ℝ) => (Sn n).nu p.2 p.1.1)
        (fun p => S.nu p.2 p.1.1) atTop {p | p.2 ∈ Icc 0 p.1.1} :=
      (hstrong.unif_nu.comp (fun p : Icc (0 : ℝ) T × ℝ => (p.2, p.1.1))).mono
        (fun p hp => ⟨hp.1, hp.2, p.1.property.2⟩)
    have h := real_ac_family (a := fun _ : Icc (0 : ℝ) T => (0 : ℝ)) (b := fun i => i.1)
      (f := fun i u => S.nu u i.1) (fun i => i.property.1) hb hlb (by
        intro ρ hρ
        obtain ⟨N, hN⟩ := hdist (ρ / C) (div_pos hρ hC)
        refine ⟨N, fun n hn' m hm' i => ?_⟩
        apply (integral_derivative_sub_le i.property.1 (hnonneg n m) (hb n i) (hb m i)
          (hdb n i) (hdb m i) ((le_iSup₂ i.1 i.property).trans (le_add_self.trans (hp n
              m)))).trans_lt
        exact (lt_div_iff₀' hC).1 (hN n hn' m hm'))
    exact fun v hv => h ⟨v, hv⟩

end EmcsfAcExtension.Local
