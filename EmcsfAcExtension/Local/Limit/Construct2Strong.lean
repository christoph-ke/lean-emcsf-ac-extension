module

public import EmcsfAcExtension.Infra.UnifIntegrable
public import EmcsfAcExtension.Local.Defs.Limit
public import EmcsfAcExtension.Local.Limit.Construct2Primary
public import EmcsfAcExtension.Local.Limit.Construct2Settings
import EmcsfAcExtension.Local.Limit.Construct2ScalarLimits
import EmcsfAcExtension.Local.Limit.Construct2Identify
import EmcsfAcExtension.Local.Limit.Construct2Mixed
import EmcsfAcExtension.Local.Limit.ExistencePointwise
import EmcsfAcExtension.Local.Limit.UI
import EmcsfAcExtension.Local.Limit.Scalar
import EmcsfAcExtension.Local.Limit.ScalarAxisAC
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Local.Stability.MomentsSections

/-! # Construction of the actual frozen strong limit

All nine uniform limits and both mixed densities are constructed from the
classical comparison and W¹¹ data approximation. Natural scalar completeness
and sectionwise subsequences identify the densities with frozen j/k. The
construction assumes neither a strong-limit record nor a solution-limit record.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

private theorem tendsto_zero_of_uniform_bound {q : ℕ → ℝ}
    (hq : ∀ n, 0 ≤ q n)
    (hl : ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, q n < ρ) :
    Tendsto q atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ρ hρ
  obtain ⟨N, hN⟩ := hl ρ hρ
  exact ⟨N, fun n hn => by simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (hq n)] using hN n hn⟩

/-- Construct a frozen `StrongLimit` from admissible classical approximants
and strong data convergence. The threshold depends only on the envelope
coefficient `A`, uniformly in all triangle, coupling, size, datum and family
parameters. The actual outgoing a and incoming b limits are AC; no scalar,
mixed-density, Cauchy or strong-limit conclusion is an extra premise. -/
theorem Null.strong_limit_of_inputs (hstab : StabExtendedStmt) (A : ℝ) (hA : 0 < A) :
    ∃ η : ℝ, 0 < η ∧
      ∀ (T e ε M : ℝ) (Sn : ℕ → Fields) (hn : ℕ → ℝ → ℂ) (h : ℝ → ℂ),
        (∀ n, StabSetting e T ε M A (Sn n) (hn n)) →
        AbsolutelyContinuousOnInterval h 0 T → (∀ n, hn n 0 = h 0) →
        Tendsto (fun n => datumVar (hn n - h) T) atTop (𝓝 0) →
        ε ^ 2 + sigma e M T ≤ η →
        ∃ S : Fields, StrongLimit e T Sn S ∧
          TendstoUniformlyOn (fun n => Function.uncurry (Sn n).mu)
            (Function.uncurry S.mu) atTop (triangle 0 T) ∧
          (∀ u ∈ Icc 0 T, AbsolutelyContinuousOnInterval (S.a u) u T) ∧
          (∀ v ∈ Icc 0 T, AbsolutelyContinuousOnInterval (fun u => S.b u v) 0 v) ∧
          AbsolutelyContinuousOnInterval (fun t => S.phi t t) 0 T ∧
          UnifIntegrable (fun n v => (outEnv 0 (jC1 (triangle 0 T) (Sn n)) v).toReal)
            1 (volume.restrict (Icc 0 T)) ∧
          UnifIntegrable (fun n u => (inEnv T (kC1 e (triangle 0 T) (Sn n)) u).toReal)
            1 (volume.restrict (Icc 0 T)) := by
  obtain ⟨ηp, hηp, hp⟩ := Null.primary_uniform_limits_of_inputs hstab A hA
  obtain ⟨ηa, hηa, ha⟩ := Null.scalar_natural_ac_limits_of_inputs hstab A hA
  obtain ⟨ηd, hηd, hd⟩ := Null.scalar_derivative_cauchy_of_inputs hstab A hA
  obtain ⟨ηm, hηm, hm⟩ := Null.same_label_mixed_cauchy_of_inputs hstab A hA
  obtain ⟨ηg, hηg, hgeometry⟩ := Null.geometry_uniform_cauchy_of_inputs hstab A hA
  refine ⟨min ηg (min ηp (min ηa (min ηd ηm))),
    lt_min hηg (lt_min hηp (lt_min hηa (lt_min hηd hηm))), ?_⟩
  intro T e ε M Sn hn h hs hac hv hlim hsmallAll
  have hsmall := hsmallAll.trans (min_le_right _ _)
  obtain ⟨_, _, _, hMuCauchy, _, _⟩ := hgeometry T e ε M Sn hn h hs hac hv hlim
    (hsmallAll.trans (min_le_left _ _))
  have hT := (hs 0).pos
  have hC1 n := (hs n).c1
  obtain ⟨S, hr, hl, hnu, hmass, hQ, hphi, hpot, htheta, hxi⟩ :=
    hp T e ε M Sn hn h hs hac hv hlim (hsmall.trans (min_le_left _ _))
  obtain ⟨a, b, phi, hfa, hfb, _, _, _, _, _⟩ :=
    ha T e ε M Sn hn h hs hac hv hlim ((hsmall.trans (min_le_right _ _)).trans (min_le_left _ _))
  obtain ⟨hda, hdb⟩ := hd T e ε M Sn hn h hs hac hv hlim
    (((hsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _))
  have hmix := hm T e ε M Sn hn h hs hac hv hlim
    (((hsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _))
  have hL p (hp : p ∈ triangle 0 T) : 0 < S.lam p.1 p.2 := by
    have hh : (1 : ℝ) / 4 ≤ S.lam p.1 p.2 := ge_of_tendsto (hl.tendsto_at hp)
      (Eventually.of_forall fun n => ((hs n).box.2 p hp).1)
    linarith only [hh]
  have hN p (hp : p ∈ triangle 0 T) : S.nu p.1 p.2 < 0 := by
    have hh : (1 : ℝ) / 4 ≤ -S.nu p.1 p.2 := ge_of_tendsto (hnu.tendsto_at hp).neg
      (Eventually.of_forall fun n => ((hs n).box.2 p hp).2.2.1)
    linarith only [hh]
  have hR p (hp : p ∈ triangle 0 T) (hlt : p.1 < p.2) : 0 < S.r p.1 p.2 := by
    have hh : (p.2 - p.1) / 4 ≤ S.r p.1 p.2 := ge_of_tendsto (hr.tendsto_at hp)
      (Eventually.of_forall fun n => (stab_radius_bounds (hs n) hp.1 hp.2.1 hp.2.2).1)
    exact (div_pos (sub_pos.mpr hlt) (by norm_num)).trans_le hh
  have hpa p (hp : p ∈ triangle 0 T) :
      Tendsto (fun n => (Sn n).a p.1 p.2) atTop (𝓝 (S.a p.1 p.2)) :=
    (hphi.tendsto_at hp).add ((htheta.tendsto_at hp).div
      (Complex.continuous_ofReal.continuousAt.tendsto.comp (hl.tendsto_at hp))
      (Complex.ofReal_ne_zero.mpr (hL p hp).ne'))
  have hpb p (hp : p ∈ triangle 0 T) :
      Tendsto (fun n => (Sn n).b p.1 p.2) atTop (𝓝 (S.b p.1 p.2)) :=
    (hphi.tendsto_at hp).add ((hxi.tendsto_at hp).div
      (Complex.continuous_ofReal.continuousAt.tendsto.comp (hnu.tendsto_at hp))
      (Complex.ofReal_ne_zero.mpr (hN p hp).ne))
  have hua : TendstoUniformlyOn (fun n => Function.uncurry (Sn n).a)
      (Function.uncurry S.a) atTop (triangle 0 T) :=
    hfa.congr_right (fun p hp => tendsto_nhds_unique (hfa.tendsto_at hp) (hpa p hp))
  have hub : TendstoUniformlyOn (fun n => Function.uncurry (Sn n).b)
      (Function.uncurry S.b) atTop (triangle 0 T) :=
    hfb.congr_right (fun p hp => tendsto_nhds_unique (hfb.tendsto_at hp) (hpb p hp))
  have haF n (i : Icc (0 : ℝ) T) : AbsolutelyContinuousOnInterval ((Sn n).a i.1) i.1 T := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le i.property.2]
    exact (hC1 n).c1_a.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun v hv => ⟨i.property.1, hv.1, hv.2⟩)
  have hbF n (i : Icc (0 : ℝ) T) :
      AbsolutelyContinuousOnInterval (fun u => (Sn n).b u i.1) 0 i.1 := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le i.property.1]
    exact (hC1 n).c1_b.comp (contDiffOn_id.prodMk contDiffOn_const)
      (fun u hu => ⟨hu.1, hu.2, i.property.2⟩)
  have hla : TendstoUniformlyOn
      (fun n (p : Icc (0 : ℝ) T × ℝ) => (Sn n).a p.1.1 p.2)
      (fun p => S.a p.1.1 p.2) atTop {p | p.2 ∈ Icc p.1.1 T} :=
    (hua.comp (fun p : Icc (0 : ℝ) T × ℝ => (p.1.1, p.2))).mono
      (fun p hp => ⟨p.1.property.1, hp.1, hp.2⟩)
  have hlb : TendstoUniformlyOn
      (fun n (p : Icc (0 : ℝ) T × ℝ) => (Sn n).b p.2 p.1.1)
      (fun p => S.b p.2 p.1.1) atTop {p | p.2 ∈ Icc 0 p.1.1} :=
    (hub.comp (fun p : Icc (0 : ℝ) T × ℝ => (p.2, p.1.1))).mono
      (fun p hp => ⟨hp.1, hp.2, p.1.property.2⟩)
  obtain ⟨hacA, hstrongA, _⟩ := ac_family_limit_of_derivative_cauchy
    (s := fun i : Icc (0 : ℝ) T => i.1) (t := fun _ => T)
    (f := fun i x => S.a i.1 x)
    (fun i : Icc (0 : ℝ) T => i.property.2) haF hla (by
      intro ρ hρ
      obtain ⟨N, hN⟩ := hda ρ hρ
      exact ⟨N, fun n hn' m hm' i => hN n hn' m hm' i.1 i.property⟩)
  obtain ⟨hacB, hstrongB, _⟩ := ac_family_limit_of_derivative_cauchy
    (s := fun _ : Icc (0 : ℝ) T => (0 : ℝ)) (t := fun i => i.1)
    (f := fun i u => S.b u i.1)
    (fun i : Icc (0 : ℝ) T => i.property.1) hbF hlb (by
      intro ρ hρ
      obtain ⟨N, hN⟩ := hdb ρ hρ
      exact ⟨N, fun n hn' m hm' i => hN n hn' m hm' i.1 i.property⟩)
  obtain ⟨j, k, Dj, Dk, hjm, hkm, hDjm, hDkm, hDjl, hDkl, hjdom, hkdom, hjl, hkl⟩ :=
    exists_mixed_densities_with_errors_of_cauchy hT hC1
      (by
        intro ρ hρ
        obtain ⟨N, hN⟩ := hmix ρ hρ
        exact ⟨N, fun n hn' m hm' => le_self_add.trans_lt (hN n hn' m hm')⟩)
      (by
        intro ρ hρ
        obtain ⟨N, hN⟩ := hmix ρ hρ
        exact ⟨N, fun n hn' m hm' => le_add_self.trans_lt (hN n hn' m hm')⟩)
  have hjeq u (hu : u ∈ Icc 0 T) : jOut S u =ᵐ[volume.restrict (Icc u T)] j u := by
    apply jOut_eq_of_uniform_of_derivative_limit hT hC1
      (fun _ hp => hr.tendsto_at hp) (fun _ hp => hl.tendsto_at hp)
      (fun _ hp => hmass.tendsto_at hp) (fun _ hp => htheta.tendsto_at hp)
      hR hL hjm hjl hu (hacA ⟨u, hu⟩)
    apply tendsto_zero_of_uniform_bound
      (fun _ => intervalIntegral.integral_nonneg hu.2 (fun _ _ => norm_nonneg _))
    intro ρ hρ
    obtain ⟨N, hN⟩ := hstrongA ρ hρ
    exact ⟨N, fun n hn' => hN n hn' ⟨u, hu⟩⟩
  have hkeq v (hv : v ∈ Icc 0 T) :
      (fun u => kIn e S u v) =ᵐ[volume.restrict (Icc 0 v)] (fun u => k u v) := by
    apply kIn_eq_of_uniform_of_derivative_limit hT hC1
      (fun _ hp => hr.tendsto_at hp) (fun _ hp => hnu.tendsto_at hp)
      (fun _ hp => hmass.tendsto_at hp) (fun _ hp => hxi.tendsto_at hp)
      (fun _ hp => hpot.tendsto_at hp) hpb hR hN hkm hkl hv (hacB ⟨v, hv⟩)
    apply tendsto_zero_of_uniform_bound
      (fun _ => intervalIntegral.integral_nonneg hv.1 (fun _ _ => norm_nonneg _))
    intro ρ hρ
    obtain ⟨N, hN⟩ := hstrongB ρ hρ
    exact ⟨N, fun n hn' => hN n hn' ⟨v, hv⟩⟩
  have hStrong : StrongLimit e T Sn S := by
    refine ⟨hr, hl, hnu, hmass, hQ, hphi, hpot, htheta, hxi, ?_, ?_⟩
    · refine ⟨Dj, hDjm, hDjl, ?_⟩
      intro n u hu
      filter_upwards [hjdom n u hu, hjeq u hu] with v hv heq
      rwa [heq]
    · refine ⟨Dk, hDkm, hDkl, ?_⟩
      intro n v hv
      filter_upwards [hkdom n v hv, hkeq v hv] with u hu heq
      rwa [heq]
  have hMuUniform := hMuCauchy.tendstoUniformlyOn_of_tendsto
    (fun p hp => hStrong.tendsto_mu_of_radius_pos hC1 hR hp)
  have hjC : ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      jDist T (Sn n) (Sn m) < ENNReal.ofReal ρ := by
    intro ρ hρ
    obtain ⟨N, hN⟩ := hmix ρ hρ
    exact ⟨N, fun n hn' m hm' => le_self_add.trans_lt (hN n hn' m hm')⟩
  have hkC : ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      kDist e T (Sn n) (Sn m) < ENNReal.ofReal ρ := by
    intro ρ hρ
    obtain ⟨N, hN⟩ := hmix ρ hρ
    exact ⟨N, fun n hn' m hm' => le_add_self.trans_lt (hN n hn' m hm')⟩
  obtain ⟨hUIj, hUIk⟩ := Null.envelope_uniform_integrability_of_cauchy hT hC1 hjC hkC
  refine ⟨S, hStrong, hMuUniform, fun u hu => hacA ⟨u, hu⟩, fun v hv => hacB ⟨v, hv⟩,
    ?_, hUIj, hUIk⟩
  exact (Null.axis_strong_ac_limit_of_strongLimit_of_cauchy hT hC1
    (fun n => (hs n).data.2) hStrong (by
      intro ρ hρ
      obtain ⟨N, hN⟩ := hmix ρ hρ
      exact ⟨N, fun n hn' m hm' => le_add_self.trans_lt (hN n hn' m hm')⟩)).1

end EmcsfAcExtension.Local
