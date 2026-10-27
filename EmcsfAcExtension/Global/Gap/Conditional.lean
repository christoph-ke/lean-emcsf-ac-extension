/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Global.Gap.Collar
public import EmcsfAcExtension.Global.Gap.MovingFlux
public import EmcsfAcExtension.Global.Gap.Recovery

/-! # The perturbative charged gap on a complete proper triangle

Every geometric and analytic input is derived from the frozen solution class
and the stated triangle bootstrap. All constants are literal and independent
of the solution, coupling, data size, triangle, and bootstrap gap.
Source: charged_SF_new_version.tex:L1505–1761.
-/

public section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace EmcsfAcExtension.Global

section Collar

variable {e δ u₀ B a τ v : ℝ} {S : Fields} {V : ℝ → ℝ}
  (hS : IsSolution e S (triangle u₀ B)) (hδ : 0 < δ ∧ δ ≤ 1)
  (hmu : ∀ p ∈ triangle u₀ B, 0 ≤ S.mu p.1 p.2)
  (hgap : ∀ p ∈ triangle u₀ B, δ ≤ 1 - S.mu p.1 p.2)
  (hsmall : ∀ p ∈ triangle u₀ B, |e| * S.r p.1 p.2 * ‖S.phi p.1 p.2‖ ≤ δ / 64)
  (ha : u₀ ≤ a) (haτ : a ≤ τ) (hτv : τ < v) (hb : v ≤ B)
  (hV : ∀ u ∈ Icc a τ, V u ∈ Ioo u v ∧ S.r u (V u) = (1 - (1 / 8 : ℝ)) * S.r u v)
  (hout : ∀ u ∈ Icc a τ, 1 - S.mu u v ≤ (1 / 256 : ℝ))

include hS hδ hmu hgap hsmall ha haτ hτv hb hV hout

namespace Annulus

/-- [internal]
The actual fractional-radius collar is continuous, has the displayed derivative,
and its optical ratio and label velocity have the required signs. -/
theorem moving_collar_boundary : ContinuousOn V (Icc a τ) ∧
    (∀u∈Icc a τ,-S.nu u (V u)≤(1-(1/8:ℝ))*(-S.nu u v)) ∧
    ∀u∈Ioo a τ,
      HasDerivAt V (((1-(1/8:ℝ))*S.nu u v-S.nu u (V u))/S.lam u (V u)) u ∧
      S.lam u (V u)*deriv V u=(-S.nu u (V u))-(1-(1/8:ℝ))*(-S.nu u v) ∧
      deriv V u≤0 := by
  have hd : (0:ℝ)<1/8 ∧ (1/8:ℝ)<1 := by norm_num
  have hc := moving_collar_continuousOn hS ha haτ hτv hb hd hV
  have hopt : ∀u∈Icc a τ,-S.nu u (V u)≤(1-(1/8:ℝ))*(-S.nu u v) := by
    intro u hu
    have hs : outSeg u (V u) v⊆triangle u₀ B := by
      rintro ⟨x,y⟩ ⟨rfl,hvy,hyv⟩
      exact ⟨ha.trans hu.1,(hV _ hu).1.1.le.trans hvy,hyv.trans hb⟩
    have hexp : ∀x∈Icc (V u) v,1≤(S.mu u x-S.Q u x^2/S.r u x^2)/(1-S.mu u x) :=
      fun x hx=>(Gap.collar_expansion hS hδ hmu hgap hsmall (ha.trans hu.1)
        (hV u hu).1.1 (hV u hu).1.2 hb (hV u hu).2 (hout u hu) x hx).2.le
    have hh := collar_optical_ratio_of_expansion hS (hV u hu).1.1 (hV u hu).1.2.le hs hexp
    have hr := (hS.r_pos (u,v) ⟨ha.trans hu.1,(hu.2.trans_lt hτv).le,hb⟩
      (hu.2.trans_lt hτv)).ne'
    calc
      _ ≤ (S.r u (V u)/S.r u v)*(-S.nu u v) := hh
      _ = _ := by rw [(hV u hu).2]; field_simp [hr]
  refine ⟨hc,hopt,?_⟩
  intro u hu
  have hdV := moving_collar_hasDerivAt hS ha hb hV hc hu
  have hvel := moving_collar_velocity_nonpos_of_optical_bound hS ha hb hV hopt
    (show u∈Icc a τ from ⟨hu.1.le,hu.2.le⟩)
  refine ⟨hdV,?_,?_⟩
  · rw [hdV.deriv]
    have hl := (hS.lam_pos (u,V u)
      ⟨ha.trans hu.1.le,(hV u ⟨hu.1.le,hu.2.le⟩).1.1.le,
        (hV u ⟨hu.1.le,hu.2.le⟩).1.2.le.trans hb⟩).ne'
    field_simp [hl]
    ; ring
  · rw [hdV.deriv]
    exact hvel

end Annulus
namespace Gap

/-- [node cg:inner-budget]
The scalar plus electric incoming inner flux has its exact `7r*/16` budget
on every initial subinterval of the actual moving collar. -/
theorem inner_budget : IntervalIntegrable (fun u=>-S.mU u (V u)) volume a τ ∧
    ∀t∈Icc a τ,(∫u in a..t,-S.mU u (V u))≤7*S.r a v/16 := by
  have hopt := (Annulus.moving_collar_boundary hS hδ hmu hgap hsmall ha haτ hτv hb hV hout).2.1
  have h := Annulus.moving_inner_budget_of_optical_bound hS hmu ha haτ hτv hb
    (by norm_num : (0:ℝ)<1/8 ∧ (1/8:ℝ)<1) hV hopt
  refine ⟨h.1,?_⟩
  intro t ht
  convert h.2 t ht using 1; ring

end Gap
namespace Annulus

/-- [internal] Actual moving-collar inputs for the recovery estimates. -/
theorem collar_recovery_data :
    IntervalIntegrable (fun u=>-S.mU u (V u)) volume a τ ∧
    (∀u∈Icc a τ,0≤-S.mU u (V u)) ∧
    (∀u∈Icc a τ,S.Q u v^2/S.r u v^2≤(1/1024:ℝ)*S.mu u v) ∧
    (∀u∈Icc a τ,(1-S.mu u v)/(2*(-S.nu u v))*‖S.xi u v‖^2≤
      18*(1-S.mu u v)*(-S.mU u (V u))+(9/4:ℝ)*(1-S.mu u v)*(-S.nu u v)) ∧
    ∀t∈Icc a τ,(∫u in a..t,-S.mU u (V u))≤7*S.r a v/16 := by
  have hbudget := Gap.inner_budget hS hδ hmu hgap hsmall ha haτ hτv hb hV hout
  refine ⟨hbudget.1,?_,?_,?_,hbudget.2⟩
  · intro u hu
    exact neg_nonneg.mpr (Gap.mass_monotonicity hS
      (show (u,V u)∈triangle u₀ B from
        ⟨ha.trans hu.1,(hV u hu).1.1.le,(hV u hu).1.2.le.trans hb⟩)).1
  · intro u hu
    have hs : outSeg u u v⊆triangle u₀ B := by
      rintro ⟨x,y⟩ ⟨rfl,huy,hyv⟩
      exact ⟨ha.trans hu.1,huy,hyv.trans hb⟩
    have h := Gap.relative_charge hS (hu.2.trans_lt hτv) hs hδ
      (hmu (u,v) ⟨ha.trans hu.1,(hu.2.trans_lt hτv).le,hb⟩)
      (fun x hx=>hgap (u,x) (hs ⟨rfl,hx⟩)) (fun x hx=>hsmall (u,x) (hs ⟨rfl,hx⟩))
    exact h.1.trans h.2
  · intro u hu
    exact Gap.moving_flux hS hδ hmu hgap hsmall (ha.trans hu.1)
      (hV u hu).1.1 (hV u hu).1.2 hb (hV u hu).2 (hout u hu)

/-- [node lem:charged-conditional-gap#outer-flux-budget]
The actual outer total mass loss has the exact `41r*/1024` bound on every
initial subinterval, uniformly in all solution and triangle data. -/
theorem outer_flux_budget :
    ∀t∈Icc a τ,(∫u in a..t,-S.mU u v)≤41*S.r a v/1024 := by
  have h := collar_recovery_data hS hδ hmu hgap hsmall ha haτ hτv hb hV hout
  intro t ht
  have hs : inSeg a t v⊆triangle u₀ B := by
    rintro ⟨u,w⟩ ⟨hau,hut,rfl⟩
    exact ⟨ha.trans hau,hut.trans (ht.2.trans hτv.le),hb⟩
  have hsub : uIcc a t⊆uIcc a τ := by
    rw [uIcc_of_le ht.1,uIcc_of_le haτ]
    exact Icc_subset_Icc le_rfl ht.2
  exact outer_flux_budget_of_moving_flux hS ht.1 (ht.2.trans_lt hτv) hs (h.1.mono_set hsub)
    (fun u hu=>h.2.1 u ⟨hu.1,hu.2.trans ht.2⟩)
    (fun u hu=>hout u ⟨hu.1,hu.2.trans ht.2⟩)
    (fun u hu=>h.2.2.1 u ⟨hu.1,hu.2.trans ht.2⟩)
    (fun u hu=>h.2.2.2.1 u ⟨hu.1,hu.2.trans ht.2⟩) (h.2.2.2.2 t ht)

/-- [node lem:charged-conditional-gap#mass-radius-persistence]
The ordinary mass stays at least `469r*/1024` and the outer radius exceeds
`r*/2` throughout the actual first-recovery collar interval. -/
theorem mass_radius_persistence (hinit : 1 - S.mu a v < (1 / 256 : ℝ)) :
    ∀t∈Icc a τ,469*S.r a v/1024≤S.m t v ∧ S.r a v/2<S.r t v := by
  intro t ht
  have hs : inSeg a t v⊆triangle u₀ B := by
    rintro ⟨u,w⟩ ⟨hau,hut,rfl⟩
    exact ⟨ha.trans hau,hut.trans (ht.2.trans hτv.le),hb⟩
  exact mass_radius_persistence_of_budget hS ht.1 (ht.2.trans_lt hτv) hs hinit
    (outer_flux_budget hS hδ hmu hgap hsmall ha haτ hτv hb hV hout t ht)

/-- [node lem:charged-conditional-gap#gap-differential-inequality]
The actual a.e. gap derivative keeps the electric cancellation and satisfies
the precise moving-collar differential inequality. -/
theorem gap_differential_inequality :
    (∀ᵐ u ∂volume.restrict (Icc a τ), HasDerivAt (fun x=>1-S.mu x v)
      ((2*((1-S.mu u v)/(2*(-S.nu u v))*‖S.xi u v‖^2)-
        (S.mu u v-S.Q u v^2/S.r u v^2)*(-S.nu u v))/S.r u v) u) ∧
    ∀ᵐ u ∂volume.restrict (Icc a τ),deriv (fun x=>1-S.mu x v) u≤
      36*(1-S.mu u v)*(-S.mU u (V u))/S.r u v := by
  have h := collar_recovery_data hS hδ hmu hgap hsmall ha haτ hτv hb hV hout
  have hs : inSeg a τ v⊆triangle u₀ B := by
    rintro ⟨u,w⟩ ⟨hau,huτ,rfl⟩
    exact ⟨ha.trans hau,huτ.trans hτv.le,hb⟩
  exact ⟨incoming_gap_derivative hS haτ hτv hs,
    gap_differential_inequality_of_flux hS haτ hτv hs hout h.2.2.1 h.2.2.2.1⟩

/-- [node lem:charged-conditional-gap#logarithmic-gap-recovery]
Integrating to the actual first-recovery gap gives `log(1/(256c))≤63/2<32`
and hence the literal universal gap `Real.exp (-32)/256`. -/
theorem logarithmic_gap_recovery (hinit : 1 - S.mu a v < (1 / 256 : ℝ))
    (hend : 1 - S.mu τ v = (1 / 256 : ℝ)) :
    Real.log (1/(256*(1-S.mu a v)))≤(63/2:ℝ) ∧
      Real.exp (-32)/256<1-S.mu a v := by
  have h := collar_recovery_data hS hδ hmu hgap hsmall ha haτ hτv hb hV hout
  have hs : inSeg a τ v⊆triangle u₀ B := by
    rintro ⟨u,w⟩ ⟨hau,huτ,rfl⟩
    exact ⟨ha.trans hau,huτ.trans hτv.le,hb⟩
  exact recovery_of_moving_flux hS haτ hτv hs h.1 h.2.1 hinit hend hout
    h.2.2.1 h.2.2.2.1 h.2.2.2.2

end Annulus
end Collar

private theorem closed_interval_regular {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x) :
    (∀ x ∈ Icc a b, HasDerivWithinAt f (g x) (Icc a b) x) ∧
      ∃ K > 0, LipschitzOnWith (Real.toNNReal K) f (Icc a b) ∧
        AbsolutelyContinuousOnInterval f a b := by
  let G (x : ℝ) := g (min (max a x) b)
  have cG : Continuous G := hg.comp_continuous
    ((continuous_const.max continuous_id).min continuous_const)
    (fun x => ⟨le_min (le_max_left _ _) hab, min_le_right _ _⟩)
  have hG (x : ℝ) (hx : x ∈ Icc a b) : G x = g x := by
    dsimp [G]; rw [max_eq_right hx.1, min_eq_left hx.2]
  have heq (x : ℝ) (hx : x ∈ Icc a b) :
      f x = f a + ∫ t in a..x, G t := by
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
      (hf.mono (Icc_subset_Icc le_rfl hx.2))
      (fun t ht => by
        have ht' : t ∈ Icc a b := ⟨ht.1.le, ht.2.le.trans hx.2⟩
        simpa only [hG t ht'] using hd t ⟨ht.1, ht.2.trans_le hx.2⟩)
      (cG.intervalIntegrable a x)
    linarith only [hi]
  have hder (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivWithinAt f (g x) (Icc a b) x := by
    have hp := (intervalIntegral.integral_hasDerivAt_right (cG.intervalIntegrable a x)
      cG.stronglyMeasurable.stronglyMeasurableAtFilter cG.continuousAt).const_add (f a)
    rw [hG x hx] at hp
    exact hp.hasDerivWithinAt.congr_of_mem heq hx
  obtain ⟨z, hz, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨a, le_rfl, hab⟩ hg.norm
  let K := max 1 ‖g z‖
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hLip : LipschitzOnWith (Real.toNNReal K) f (Icc a b) := by
    apply (convex_Icc a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hder
    intro x hx
    apply NNReal.coe_le_coe.mp
    simpa only [coe_nnnorm, Real.coe_toNNReal _ hK.le] using
      (hmax hx).trans (le_max_right 1 ‖g z‖)
  exact ⟨hder, K, hK, hLip, by
    exact (show LipschitzOnWith (Real.toNNReal K) f (uIcc a b) from
      by simpa only [uIcc_of_le hab] using hLip).absolutelyContinuousOnInterval⟩

/-- [node lem:charged-conditional-gap#moving-collar-boundary]
Construct the unique fractional-radius collar and its continuous derivative
on the closed recovery interval (charged_SF_new_version.tex:L1672–1676). It is AC and
Lipschitz, with the optical ratio and velocity signs throughout. The positive
Lipschitz constant depends on the fixed solution and recovery interval,
uniformly in its labels; the ratio `7/8` is universal. -/
theorem Annulus.exists_moving_collar_boundary {e δ u₀ B a τ v : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle u₀ B)) (hδ : 0 < δ ∧ δ ≤ 1)
    (hmu : ∀ p ∈ triangle u₀ B, 0 ≤ S.mu p.1 p.2)
    (hgap : ∀ p ∈ triangle u₀ B, δ ≤ 1 - S.mu p.1 p.2)
    (hsmall : ∀ p ∈ triangle u₀ B, |e| * S.r p.1 p.2 * ‖S.phi p.1 p.2‖ ≤ δ / 64)
    (ha : u₀ ≤ a) (haτ : a ≤ τ) (hτv : τ < v) (hb : v ≤ B)
    (hout : ∀ u ∈ Icc a τ, 1 - S.mu u v ≤ (1 / 256 : ℝ)) :
    ∃ V : ℝ → ℝ,
      (∀ u ∈ Icc a τ, V u ∈ Ioo u v ∧ S.r u (V u) = (1 - (1/8:ℝ)) * S.r u v) ∧
      (∀ u ∈ Icc a τ, ∀ w ∈ Ioo u v,
        S.r u w = (1 - (1/8:ℝ)) * S.r u v → w = V u) ∧
      ContinuousOn V (Icc a τ) ∧ ContDiffOn ℝ 1 V (Icc a τ) ∧
      let g := fun u => ((1 - (1/8:ℝ)) * S.nu u v - S.nu u (V u)) / S.lam u (V u)
      ContinuousOn g (Icc a τ) ∧
      (∀ u ∈ Icc a τ, HasDerivWithinAt V (g u) (Icc a τ) u ∧
        -S.nu u (V u) ≤ (1 - (1/8:ℝ)) * (-S.nu u v) ∧
        S.lam u (V u) * g u = (-S.nu u (V u)) - (1 - (1/8:ℝ)) * (-S.nu u v) ∧
        g u ≤ 0) ∧
      ∃ K > 0, LipschitzOnWith (Real.toNNReal K) V (Icc a τ) ∧
        AbsolutelyContinuousOnInterval V a τ := by
  obtain ⟨V, hV, hc⟩ := Annulus.moving_collar_exists hS ha haτ hτv hb (by norm_num :
    (0:ℝ) < 1/8 ∧ (1/8:ℝ) < 1)
  have hfull := Annulus.moving_collar_boundary hS hδ hmu hgap hsmall ha haτ hτv hb hV hout
  let g := fun u => ((1 - (1/8:ℝ)) * S.nu u v - S.nu u (V u)) / S.lam u (V u)
  have hmap (u : ℝ) (hu : u ∈ Icc a τ) : (u, V u) ∈ triangle u₀ B :=
    ⟨ha.trans hu.1, (hV u hu).1.1.le, (hV u hu).1.2.le.trans hb⟩
  have hl (u : ℝ) (hu : u ∈ Icc a τ) := hS.lam_pos (u, V u) (hmap u hu)
  have cg : ContinuousOn g (Icc a τ) :=
    ((continuousOn_const.mul (hS.cont_nu.comp (continuousOn_id.prodMk continuousOn_const)
      (fun u hu => ⟨ha.trans hu.1, (hu.2.trans_lt hτv).le, hb⟩))).sub
      (hS.cont_nu.comp (continuousOn_id.prodMk hc) hmap)).div
      (hS.cont_lam.comp (continuousOn_id.prodMk hc) hmap) (fun u hu => (hl u hu).ne')
  obtain ⟨hd, hLip⟩ := closed_interval_regular haτ hc cg (fun u hu => (hfull.2.2 u hu).1)
  have hC1 : ContDiffOn ℝ 1 V (Icc a τ) := by
    change ContDiffOn ℝ ((0:ℕ∞ω) + 1) V (Icc a τ)
    rw [contDiffOn_succ_iff_hasFDerivWithinAt (by simp)]
    intro x hx
    refine ⟨Icc a τ, ?_, by simp, fun u => ContinuousLinearMap.toSpanSingleton ℝ (g u),
      ?_, ?_⟩
    · simpa only [insert_eq_of_mem hx] using
        (self_mem_nhdsWithin : Icc a τ ∈ 𝓝[Icc a τ] x)
    · exact fun u hu => (hd u hu).hasFDerivWithinAt
    · rw [contDiffOn_zero]
      exact ContinuousLinearMap.toSpanSingletonCLE.continuous.comp_continuousOn cg
  refine ⟨V, hV, ?_, hc, hC1, cg, ?_, hLip⟩
  · intro u hu w hw he
    exact Annulus.radius_out_injOn hS (ha.trans hu.1) (hu.2.trans_lt hτv) hb
      ⟨hw.1.le, hw.2.le⟩ ⟨(hV u hu).1.1.le, (hV u hu).1.2.le⟩ (he.trans (hV u hu).2.symm)
  · intro u hu
    refine ⟨hd u hu, hfull.2.1 u hu, ?_, ?_⟩
    · dsimp [g]; field_simp [(hl u hu).ne']; ring
    · exact Annulus.moving_collar_velocity_nonpos_of_optical_bound hS ha hb hV hfull.2.1 hu

/-- [node lem:charged-conditional-gap]
The triangle bootstrap improves to the literal universal gap. Every
intermediate moving-collar estimate is discharged from the actual solution. -/
theorem charged_conditional_gap (e u₀ b δ : ℝ) (S : Fields) (_hub : u₀ < b)
    (hS : IsSolution e S (triangle u₀ b)) (hδ : 0 < δ ∧ δ ≤ 1)
    (hmu : ∀ p ∈ triangle u₀ b, 0 ≤ S.mu p.1 p.2)
    (hgap : ∀ p ∈ triangle u₀ b, δ ≤ 1 - S.mu p.1 p.2)
    (hsmall : ∀ p ∈ triangle u₀ b, |e| * S.r p.1 p.2 * ‖S.phi p.1 p.2‖ ≤ δ / 64) :
    ∀p∈triangle u₀ b,Real.exp (-32)/256≤1-S.mu p.1 p.2 := by
  rintro ⟨a,v⟩ hp
  change u₀≤a ∧ a≤v ∧ v≤b at hp
  change Real.exp (-32)/256≤1-S.mu a v
  by_cases hbig : (1/256:ℝ)≤1-S.mu a v
  · have he : Real.exp (-32)≤1 := Real.exp_le_one_iff.mpr (by norm_num)
    exact (div_le_div_of_nonneg_right he (by norm_num : (0:ℝ)≤256)).trans hbig
  have hinit : 1-S.mu a v<(1/256:ℝ) := lt_of_not_ge hbig
  rcases lt_or_eq_of_le hp.2.1 with hav | rfl
  · obtain ⟨τ,hτ,hend,hlow⟩ := Annulus.first_recovery hS hp.1 hav hp.2.2 hinit
    obtain ⟨V,hV,_⟩ := Annulus.moving_collar_exists hS hp.1 hτ.1.le hτ.2 hp.2.2
      (by norm_num : (0:ℝ)<1/8 ∧ (1/8:ℝ)<1)
    exact (Annulus.logarithmic_gap_recovery hS hδ hmu hgap hsmall hp.1 hτ.1.le
      hτ.2 hp.2.2 hV hlow hinit hend).2.le
  · have hz := (hS.axis a ⟨hp.1,le_rfl,hp.2.2⟩).1
    simp only [Fields.mu,hz,div_zero,sub_zero] at hinit
    norm_num at hinit

namespace Gap

/-- [internal] The architecture interface for the canonical conditional-gap theorem. -/
theorem conditional (e a b δ : ℝ) (S : Fields) (hab : a < b)
    (hS : IsSolution e S (triangle a b)) (hδ : 0 < δ ∧ δ ≤ 1)
    (hmu : ∀ p ∈ triangle a b, 0 ≤ S.mu p.1 p.2)
    (hgap : ∀ p ∈ triangle a b, δ ≤ 1 - S.mu p.1 p.2)
    (hsmall : ∀ p ∈ triangle a b, |e| * S.r p.1 p.2 * ‖S.phi p.1 p.2‖ ≤ δ / 64) :
    ∀p∈triangle a b,Real.exp (-32)/256≤1-S.mu p.1 p.2 :=
  charged_conditional_gap e a b δ S hab hS hδ hmu hgap hsmall

end Gap
end EmcsfAcExtension.Global
