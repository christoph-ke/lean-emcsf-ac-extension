/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Global.Gap.Annulus
import EmcsfAcExtension.Infra.Gronwall

/-! # Recovery of a small incoming gap

The exact incoming field equation retains the electric cancellation. The
remaining lemmas separate the explicit numerical and analytic steps from
the construction of the moving collar. Constants are uniform in all data.
Source: charged_SF_new_version.tex:L1728–1760.
-/

public section

open Set MeasureTheory Filter Topology
namespace EmcsfAcExtension.Global.Annulus

/-- [internal] The actual a.e. incoming derivative of the frozen gap, with its
scalar flux and electric/geometric cancellation. -/
theorem incoming_gap_derivative {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a b v : ℝ} (hab : a ≤ b) (hbv : b < v)
    (hs : inSeg a b v ⊆ D) :
    ∀ᵐ u ∂volume.restrict (Icc a b),
      HasDerivAt (fun x => 1 - S.mu x v)
        ((2 * ((1-S.mu u v)/(2*(-S.nu u v))*‖S.xi u v‖^2) -
          (S.mu u v - S.Q u v^2/S.r u v^2)*(-S.nu u v))/S.r u v) u := by
  have h := Calculus.in_section hS hab hbv.le hs
  filter_upwards [h.1.2, h.2.2.1.2, ae_restrict_mem measurableSet_Icc] with u hr hm hu
  have hp : (u,v) ∈ D := hs ⟨hu.1, hu.2, rfl⟩
  have hr0 := (hS.r_pos (u,v) hp (hu.2.trans_lt hbv)).ne'
  have hn0 := (hS.nu_neg (u,v) hp).ne
  have hd : HasDerivAt (fun x => 1-S.mu x v)
      (-((2*S.mU u v*S.r u v-2*S.m u v*S.nu u v)/S.r u v^2)) u := by
    simpa only [Fields.mu, Pi.mul_apply, Pi.div_apply, zero_mul, zero_add] using
      (((hasDerivAt_const u (2:ℝ)).mul hm).div hr hr0).const_sub 1
  apply hd.congr_deriv
  dsimp [Fields.mu, Fields.mU]
  field_simp [hr0,hn0]
  ; ring

/-- [internal] The discarded recovery remainder is nonpositive below gap `1/256`. -/
theorem recovery_remainder_nonpos {g μ q n : ℝ} (hμ : μ = 1 - g)
    (hg : g ≤ (1 / 256 : ℝ)) (hn : 0 ≤ n) (hq : q ≤ (1 / 1024 : ℝ) * μ) :
    ((9/2:ℝ)*g-(μ-q))*n ≤ 0 := by
  have hsign : (9/2:ℝ)*g-(μ-q) ≤ 0 := by nlinarith only [hμ,hg,hq]
  exact mul_nonpos_of_nonpos_of_nonneg hsign hn

/-- [internal] Insert the moving scalar flux estimate into the exact gap density. -/
theorem gap_density_bound {g μ q n r F Fs : ℝ}
    (hr : 0 < r) (hn : 0 ≤ n) (hμ : μ = 1 - g)
    (hg : g ≤ (1 / 256 : ℝ)) (hq : q ≤ (1 / 1024 : ℝ) * μ)
    (hflux : Fs ≤ 18 * g * F + (9 / 4 : ℝ) * g * n) :
    (2*Fs-(μ-q)*n)/r ≤ 36*g*F/r := by
  apply (div_le_div_iff_of_pos_right hr).mpr
  have hrem := recovery_remainder_nonpos hμ hg hn hq
  nlinarith only [hflux,hrem]

/-- [internal] Exact mass and radius persistence from the outer flux budget. -/
theorem mass_radius_of_budget {r m R c loss : ℝ}
    (hR : 0 < R) (hc : c < (1 / 256 : ℝ))
    (hm : m = (1 - c) * R / 2 - loss) (hl : loss ≤ 41 * R / 1024)
    (hgeom : 2 * m < r) :
    469*R/1024 ≤ m ∧ R/2 < r := by
  have hcR := mul_lt_mul_of_pos_right hc hR
  constructor <;> nlinarith only [hcR,hm,hl,hgeom,hR]

/-- [internal] AC Grönwall gives the exact logarithmic bound `63/2`, hence
the literal improved gap `Real.exp (-32) / 256`. The integral coefficient
is supplied by the moving-collar budget before this helper is applied. -/
theorem logarithmic_recovery_of_integral_bound {g k : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hg : AbsolutelyContinuousOnInterval g a b)
    (hga : 0 < g a) (hgb : g b = (1 / 256 : ℝ))
    (hk : IntervalIntegrable k volume a b)
    (hder : ∀ᵐ u ∂volume.restrict (Icc a b), deriv g u ≤ k u * g u)
    (hbudget : (∫ u in a..b, k u) ≤ (63 / 2 : ℝ)) :
    Real.log (1/(256*g a)) ≤ (63/2:ℝ) ∧ Real.exp (-32)/256 < g a := by
  have h := le_exp_integral_of_ac_deriv_le hab hg hk hder b ⟨hab,le_rfl⟩
  rw [hgb] at h
  have h' : 1/(256*g a) ≤ Real.exp (∫ u in a..b,k u) := by
    apply (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ)<256) hga)).mpr
    nlinarith only [h]
  have hlog := (Real.log_le_iff_le_exp (by positivity : 0<1/(256*g a))).mpr h'
  have hlog' := hlog.trans hbudget
  constructor
  · exact hlog'
  · have hs : Real.exp (-32) < Real.exp (-Real.log (1/(256*g a))) := by
      apply Real.exp_lt_exp.mpr
      linarith only [hlog']
    rw [Real.exp_neg (Real.log (1/(256*g a))), Real.exp_log (by positivity : 0<1/(256*g a))] at hs
    have heq : (1/(256*g a))⁻¹ = 256*g a := by field_simp
    rw [heq] at hs
    exact (div_lt_iff₀ (by norm_num : (0:ℝ)<256)).mpr (by linarith only [hs])

/-- [internal] Integrating the moving comparison gives the exact `41/1024` budget. -/
theorem outer_flux_budget_of_comparison {F₁ F₂ n : ℝ → ℝ} {a b R : ℝ}
    (hab : a ≤ b)
    (hF₁ : IntervalIntegrable F₁ volume a b)
    (hF₂ : IntervalIntegrable F₂ volume a b)
    (hn : IntervalIntegrable n volume a b)
    (hflux : ∀ u ∈ Icc a b, F₂ u ≤ (9 / 128 : ℝ) * F₁ u + (19 / 2048 : ℝ) * n u)
    (hinner : (∫ u in a..b, F₁ u) ≤ 7 * R / 16)
    (hrad : (∫ u in a..b, n u) ≤ R) :
    (∫u in a..b,F₂ u) ≤ 41*R/1024 := by
  have h := intervalIntegral.integral_mono_on hab hF₂
    ((hF₁.const_mul (9/128:ℝ)).add (hn.const_mul (19/2048:ℝ))) hflux
  rw [intervalIntegral.integral_add (hF₁.const_mul _) (hn.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at h
  linarith only [h,hinner,hrad]

end EmcsfAcExtension.Global.Annulus

namespace EmcsfAcExtension.Global.Annulus

/-- [internal] On an actual positive-radius incoming section the frozen gap
is AC. Its positive lower radius bound is derived from compactness. -/
theorem incoming_gap_ac {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a b v : ℝ} (hab : a ≤ b) (hbv : b < v)
    (hs : inSeg a b v ⊆ D) :
    AbsolutelyContinuousOnInterval (fun u => 1 - S.mu u v) a b := by
  have h := Calculus.in_section hS hab hbv.le hs
  have cr := Calculus.continuousOn_in_section hS.cont_r hs
  obtain ⟨c, hc, hcr⟩ := isCompact_Icc.exists_forall_le' cr (fun u hu =>
    hS.r_pos (u, v) (hs ⟨hu.1, hu.2, rfl⟩) (hu.2.trans_lt hbv))
  have hq := (h.2.2.1.1.const_mul 2).div_of_le_norm h.1.1 hc (fun u hu => by
    rw [uIcc_of_le hab] at hu
    exact (hcr u hu).trans (le_abs_self _))
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) a b :=
    (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  exact hconst.fun_sub hq

/-- [internal] The actual incoming differential inequality once the moving
scalar-flux estimate and relative-charge estimate have been discharged. -/
theorem gap_differential_inequality_of_flux {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a b v : ℝ} (hab : a ≤ b) (hbv : b < v)
    (hs : inSeg a b v ⊆ D) {F : ℝ → ℝ}
    (hgap : ∀ u ∈ Icc a b, 1 - S.mu u v ≤ (1 / 256 : ℝ))
    (hcharge : ∀ u ∈ Icc a b, S.Q u v ^ 2 / S.r u v ^ 2 ≤ (1 / 1024 : ℝ) * S.mu u v)
    (hflux : ∀ u ∈ Icc a b,
      (1 - S.mu u v) / (2 * (-S.nu u v)) * ‖S.xi u v‖ ^ 2 ≤
        18 * (1 - S.mu u v) * F u + (9 / 4 : ℝ) * (1 - S.mu u v) * (-S.nu u v)) :
    ∀ᵐ u ∂volume.restrict (Icc a b), deriv (fun x => 1-S.mu x v) u ≤
      36*(1-S.mu u v)*F u/S.r u v := by
  filter_upwards [incoming_gap_derivative hS hab hbv hs,
    ae_restrict_mem measurableSet_Icc] with u hd hu
  rw [hd.deriv]
  exact gap_density_bound
    (hS.r_pos (u, v) (hs ⟨hu.1, hu.2, rfl⟩) (hu.2.trans_lt hbv))
    (neg_nonneg.mpr (hS.nu_neg (u, v) (hs ⟨hu.1, hu.2, rfl⟩)).le)
    (by ring) (hgap u hu) (hcharge u hu) (hflux u hu)

end EmcsfAcExtension.Global.Annulus

namespace EmcsfAcExtension.Global.Annulus

/-- [internal] The actual outer total-flux budget once the moving scalar
comparison is available. Its coefficient is exactly `41/1024`. -/
theorem outer_flux_budget_of_moving_flux {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a b v : ℝ} (hab : a ≤ b) (hbv : b < v)
    (hs : inSeg a b v ⊆ D) {F : ℝ → ℝ}
    (hF : IntervalIntegrable F volume a b) (hF0 : ∀ u ∈ Icc a b, 0 ≤ F u)
    (hgap : ∀ u ∈ Icc a b, 1 - S.mu u v ≤ (1 / 256 : ℝ))
    (hcharge : ∀ u ∈ Icc a b, S.Q u v ^ 2 / S.r u v ^ 2 ≤ (1 / 1024 : ℝ) * S.mu u v)
    (hflux : ∀ u ∈ Icc a b, (1 - S.mu u v) / (2 * (-S.nu u v)) * ‖S.xi u v‖ ^ 2 ≤
      18 * (1 - S.mu u v) * F u + (9 / 4 : ℝ) * (1 - S.mu u v) * (-S.nu u v))
    (hinner : (∫ u in a..b, F u) ≤ 7 * S.r a v / 16) :
    (∫u in a..b,-S.mU u v)≤41*S.r a v/1024 := by
  have hforms := Calculus.in_integralForm hS hab hbv.le hs
  have hn : IntervalIntegrable (fun u=>-S.nu u v) volume a b := hforms.1.1.neg
  have hF₂ : IntervalIntegrable (fun u=>-S.mU u v) volume a b := hforms.2.2.1.1.neg
  refine outer_flux_budget_of_comparison hab hF hF₂ hn ?_ hinner ?_
  · intro u hu
    have hp : (u,v)∈D := hs ⟨hu.1,hu.2,rfl⟩
    have hn0 := (neg_pos.mpr (hS.nu_neg (u,v) hp)).le
    have hg0 := hS.one_sub_mu_pos (u,v) hp
    have hq : S.Q u v^2/S.r u v^2≤(1/1024:ℝ) :=
      (hcharge u hu).trans (by linarith only [hg0])
    have hel : (-S.nu u v)*S.Q u v^2/(2*S.r u v^2)≤(-S.nu u v)/2048 := by
      have h := mul_le_mul_of_nonneg_left hq (div_nonneg hn0 (by norm_num : (0:ℝ)≤2))
      convert h using 1 <;> ring
    have hgF := mul_le_mul_of_nonneg_right (hgap u hu) (hF0 u hu)
    have hgn := mul_le_mul_of_nonneg_right (hgap u hu) hn0
    rw [incoming_flux_decomposition S u v]
    nlinarith only [hflux u hu,hgF,hgn,hel]
  · have hr := hS.r_pos (b,v) (hs ⟨hab,le_rfl,rfl⟩) hbv
    rw [intervalIntegral.integral_neg,←hforms.1.2]
    linarith only [hr]

/-- [internal] The actual mass and radius persistence furnished by an outer
mass-loss budget. This uses ordinary Hawking mass and the frozen `mu`. -/
theorem mass_radius_persistence_of_budget {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a b v : ℝ} (hab : a ≤ b) (hbv : b < v)
    (hs : inSeg a b v ⊆ D) (hinit : 1 - S.mu a v < (1 / 256 : ℝ))
    (hbudget : (∫ u in a..b, -S.mU u v) ≤ 41 * S.r a v / 1024) :
    469*S.r a v/1024≤S.m b v ∧ S.r a v/2<S.r b v := by
  have ha : (a,v)∈D := hs ⟨le_rfl,hab,rfl⟩
  have hb : (b,v)∈D := hs ⟨hab,le_rfl,rfl⟩
  have hr₀ := hS.r_pos (a,v) ha (hab.trans_lt hbv)
  have hr₁ := hS.r_pos (b,v) hb hbv
  have hform := (Calculus.in_integralForm hS hab hbv.le hs).2.2.1
  have hm : S.m b v=(1-(1-S.mu a v))*S.r a v/2-(∫u in a..b,-S.mU u v) := by
    rw [intervalIntegral.integral_neg,←hform.2]
    dsimp [Fields.mu]
    field_simp [hr₀.ne']
    ; ring
  have hgeom : 2*S.m b v<S.r b v := by
    simpa only [one_mul] using
      (div_lt_iff₀ hr₁).mp (sub_pos.mp (hS.one_sub_mu_pos (b,v) hb))
  exact mass_radius_of_budget hr₀ hinit hm hbudget hgeom

end EmcsfAcExtension.Global.Annulus

namespace EmcsfAcExtension.Global.Annulus

/-- [internal] Complete recovery on an actual incoming section from the moving
scalar-flux estimate and its inner mass budget on every initial subinterval.
The moving-collar construction discharges these explicit inputs. -/
theorem recovery_of_moving_flux {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a b v : ℝ} (hab : a ≤ b) (hbv : b < v)
    (hs : inSeg a b v ⊆ D) {F : ℝ → ℝ}
    (hF : IntervalIntegrable F volume a b) (hF0 : ∀ u ∈ Icc a b, 0 ≤ F u)
    (hinit : 1 - S.mu a v < (1 / 256 : ℝ)) (hend : 1 - S.mu b v = (1 / 256 : ℝ))
    (hgap : ∀ u ∈ Icc a b, 1 - S.mu u v ≤ (1 / 256 : ℝ))
    (hcharge : ∀ u ∈ Icc a b, S.Q u v ^ 2 / S.r u v ^ 2 ≤ (1 / 1024 : ℝ) * S.mu u v)
    (hflux : ∀ u ∈ Icc a b, (1 - S.mu u v) / (2 * (-S.nu u v)) * ‖S.xi u v‖ ^ 2 ≤
      18 * (1 - S.mu u v) * F u + (9 / 4 : ℝ) * (1 - S.mu u v) * (-S.nu u v))
    (hinner : ∀ t ∈ Icc a b, (∫ u in a..t, F u) ≤ 7 * S.r a v / 16) :
    Real.log (1/(256*(1-S.mu a v)))≤(63/2:ℝ) ∧
      Real.exp (-32)/256<1-S.mu a v := by
  have hp (u : ℝ) (hu : u∈Icc a b) : (u,v)∈D := hs ⟨hu.1,hu.2,rfl⟩
  have hr₀ := hS.r_pos (a,v) (hp a ⟨le_rfl,hab⟩) (hab.trans_lt hbv)
  have hr (u : ℝ) (hu : u∈Icc a b) := hS.r_pos (u,v) (hp u hu) (hu.2.trans_lt hbv)
  have hsub (t : ℝ) (ht : t∈Icc a b) : uIcc a t⊆uIcc a b := by
    rw [uIcc_of_le ht.1,uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl ht.2
  have hrad (t : ℝ) (ht : t∈Icc a b) : S.r a v/2<S.r t v := by
    have hs' : inSeg a t v⊆D := fun p hp=>hs (inSeg_subset_inSeg le_rfl ht.2 hp)
    have hm := outer_flux_budget_of_moving_flux hS ht.1 (ht.2.trans_lt hbv) hs'
      (hF.mono_set (hsub t ht))
      (fun u hu=>hF0 u ⟨hu.1,hu.2.trans ht.2⟩)
      (fun u hu=>hgap u ⟨hu.1,hu.2.trans ht.2⟩)
      (fun u hu=>hcharge u ⟨hu.1,hu.2.trans ht.2⟩)
      (fun u hu=>hflux u ⟨hu.1,hu.2.trans ht.2⟩) (hinner t ht)
    exact (mass_radius_persistence_of_budget hS ht.1 (ht.2.trans_lt hbv) hs' hinit hm).2
  have cr := Calculus.continuousOn_in_section hS.cont_r hs
  let k := fun u=>36*F u/S.r u v
  have hk : IntervalIntegrable k volume a b := by
    have ck : ContinuousOn (fun u=>(36:ℝ)/S.r u v) (Icc a b) :=
      continuousOn_const.div cr (fun u hu=>(hr u hu).ne')
    have h := hF.continuousOn_mul (by simpa only [uIcc_of_le hab] using ck)
    convert h using 1
    funext u
    dsimp [k]
    ring
  have hupper : ∀u∈Icc a b,k u≤(72/S.r a v)*F u := by
    intro u hu
    have h := div_le_div_of_nonneg_left (mul_nonneg (by norm_num : (0:ℝ)≤36) (hF0 u hu))
      (div_pos hr₀ (by norm_num : (0:ℝ)<2)) (hrad u hu).le
    change 36*F u/S.r u v≤36*F u/(S.r a v/2) at h
    dsimp [k]
    convert h using 1; field_simp [hr₀.ne']; ring
  have hkbound : (∫u in a..b,k u)≤(63/2:ℝ) := by
    have h := intervalIntegral.integral_mono_on hab hk
      (hF.const_mul (72/S.r a v)) hupper
    rw [intervalIntegral.integral_const_mul] at h
    have hh := mul_le_mul_of_nonneg_left (hinner b ⟨hab,le_rfl⟩)
      (div_nonneg (by norm_num : (0:ℝ)≤72) hr₀.le)
    have heq : (72/S.r a v)*(7*S.r a v/16)=(63/2:ℝ) := by field_simp [hr₀.ne']; norm_num
    exact h.trans (hh.trans_eq heq)
  have hd := gap_differential_inequality_of_flux hS hab hbv hs hgap hcharge hflux
  apply logarithmic_recovery_of_integral_bound hab (incoming_gap_ac hS hab hbv hs)
    (hS.one_sub_mu_pos (a,v) (hp a ⟨le_rfl,hab⟩)) hend hk _ hkbound
  filter_upwards [hd] with u hu
  convert hu using 1; dsimp [k]; ring

end EmcsfAcExtension.Global.Annulus

namespace EmcsfAcExtension.Global.Gap

/-- [internal] Weighted Cauchy–Schwarz for the actual scalar derivative on a positive-radius
outgoing annulus. The lower radius in the second factor is fixed. -/
theorem scalar_oscillation_cauchy_schwarz {e u a b : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    S.r u a ^ 2 * ‖S.phi u a - S.phi u b‖ ^ 2 ≤
      (∫ v in a..b, S.lam u v * (1 - S.mu u v) * ‖S.theta u v / S.lam u v‖ ^ 2) *
      (∫ v in a..b, S.lam u v / (1 - S.mu u v) * (S.r u a / S.r u v) ^ 2) := by
  have hp (v : ℝ) (hv : v ∈ Icc a b) : (u, v) ∈ D := hs ⟨rfl, hv⟩
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have ct := Calculus.continuousOn_out_section hS.cont_theta hs
  have cg : ContinuousOn (fun v => 1 - S.mu u v) (Icc a b) :=
    continuousOn_const.sub (Calculus.continuousOn_out_section (continuousOn_mu hS) hs)
  have hr (v : ℝ) (hv : v ∈ Icc a b) := hS.r_pos (u, v) (hp v hv) (hua.trans_le hv.1)
  have hl (v : ℝ) (hv : v ∈ Icc a b) := hS.lam_pos (u, v) (hp v hv)
  have hg (v : ℝ) (hv : v ∈ Icc a b) := hS.one_sub_mu_pos (u, v) (hp v hv)
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have cx := ct.div (Complex.continuous_ofReal.comp_continuousOn cl)
    (fun v hv => Complex.ofReal_ne_zero.mpr (hl v hv).ne')
  let f := fun v => Real.sqrt (S.lam u v) * Real.sqrt (1 - S.mu u v) *
    ‖S.theta u v / S.lam u v‖
  let g := fun v => Real.sqrt (S.lam u v) / Real.sqrt (1 - S.mu u v) *
    (S.r u a / S.r u v)
  have cf : ContinuousOn f (Icc a b) := (cl.sqrt.mul cg.sqrt).mul cx.norm
  have cgg : ContinuousOn g (Icc a b) :=
    (cl.sqrt.div cg.sqrt (fun v hv => (Real.sqrt_pos.mpr (hg v hv)).ne')).mul
      (continuousOn_const.div cr (fun v hv => (hr v hv).ne'))
  have fsq (v : ℝ) (hv : v ∈ Icc a b) : f v ^ 2 =
      S.lam u v * (1 - S.mu u v) * ‖S.theta u v / S.lam u v‖ ^ 2 := by
    dsimp [f]
    rw [mul_pow, mul_pow, Real.sq_sqrt (hl v hv).le, Real.sq_sqrt (hg v hv).le]
  have gsq (v : ℝ) (hv : v ∈ Icc a b) : g v ^ 2 =
      S.lam u v / (1 - S.mu u v) * (S.r u a / S.r u v) ^ 2 := by
    dsimp [g]
    rw [mul_pow, div_pow, Real.sq_sqrt (hl v hv).le, Real.sq_sqrt (hg v hv).le]
  have fg (v : ℝ) (hv : v ∈ Icc a b) :
      ‖(S.r u a : ℂ) * S.phiV u v‖ = f v * g v := by
    have he : f v * g v = Real.sqrt (S.lam u v) ^ 2 *
        (S.r u a / S.r u v) * ‖S.theta u v / S.lam u v‖ := by
      dsimp [f, g]
      field_simp [(Real.sqrt_pos.mpr (hg v hv)).ne']
    rw [he, Real.sq_sqrt (hl v hv).le]
    simp only [Fields.phiV, norm_mul, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (hr a ha), abs_of_pos (hr v hv), abs_of_pos (hl v hv)]
    field_simp [(hl v hv).ne', (hr v hv).ne']
  have hphi := (hS.eq_out u a b hua hab hs).2.2.2.2.2.1
  have hidentity : (S.r u a : ℂ) * (S.phi u b - S.phi u a) =
      ∫ v in a..b, (S.r u a : ℂ) * S.phiV u v := by
    rw [hphi.2, intervalIntegral.integral_const_mul]
  have hnorm := intervalIntegral.norm_integral_le_integral_norm (μ := volume) hab
    (f := fun v => (S.r u a : ℂ) * S.phiV u v)
  rw [← hidentity] at hnorm
  rw [intervalIntegral.integral_congr (fun v hv => fg v (by
    simpa only [uIcc_of_le hab] using hv))] at hnorm
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr a ha)] at hnorm
  have hsq := (sq_le_sq₀ (mul_nonneg (hr a ha).le (norm_nonneg _))
    ((mul_nonneg (hr a ha).le (norm_nonneg _)).trans hnorm)).mpr hnorm
  have hcs := hsq.trans (Annulus.scalar_cauchy_schwarz hab cf cgg)
  rw [intervalIntegral.integral_congr (fun v hv => fsq v (by
    simpa only [uIcc_of_le hab] using hv)), intervalIntegral.integral_congr (fun v hv => gsq v (by
    simpa only [uIcc_of_le hab] using hv))] at hcs
  simpa only [mul_pow, norm_sub_rev] using hcs

/-- [internal] The rowwise scalar oscillation bound without a lower interior gap bound.
The fixed finite coefficient Λ is the stipulated upper bound for λ/(1-μ). -/
theorem outgoing_scalar_oscillation {e u v Λ : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (huv : u < v) (hv : v ≤ 0) (hs : outSeg u v 0 ⊆ D)
    (hm : 0 ≤ S.m u v)
    (hopt : ∀ w ∈ Icc v 0, S.lam u w / (1 - S.mu u w) ≤ Λ) :
    S.r u v ^ 2 * ‖S.phi u v - S.phi u 0‖ ^ 2 ≤ 2 * Λ * S.m u 0 * (-u) := by
  have hp (w : ℝ) (hw : w ∈ Icc v 0) : (u, w) ∈ D := hs ⟨rfl, hw⟩
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have cg : ContinuousOn (fun w => 1 - S.mu u w) (Icc v 0) :=
    continuousOn_const.sub (Calculus.continuousOn_out_section (continuousOn_mu hS) hs)
  have hr (w : ℝ) (hw : w ∈ Icc v 0) := hS.r_pos (u, w) (hp w hw) (huv.trans_le hw.1)
  have hl (w : ℝ) (hw : w ∈ Icc v 0) := hS.lam_pos (u, w) (hp w hw)
  have hg (w : ℝ) (hw : w ∈ Icc v 0) := hS.one_sub_mu_pos (u, w) (hp w hw)
  have hΛ : 0 ≤ Λ :=
    (div_nonneg (hl v ⟨le_rfl, hv⟩).le (hg v ⟨le_rfl, hv⟩).le).trans (hopt v ⟨le_rfl, hv⟩)
  have hA := (Annulus.annular_masses hS huv hv hs).2.1
  have hA' : (∫ w in v..0, S.lam u w * (1 - S.mu u w) *
      ‖S.theta u w / S.lam u w‖ ^ 2) ≤ 2 * S.m u 0 := by linarith only [hA, hm]
  have hA0 := (Annulus.annular_masses hS huv hv hs).1
  have hm0 : 0 ≤ S.m u 0 := hm.trans (mass_out_le hS huv.le hv hs)
  have cB : ContinuousOn (fun w => S.lam u w / (1 - S.mu u w) *
      (S.r u v / S.r u w) ^ 2) (Icc v 0) :=
    (cl.div cg (fun w hw => (hg w hw).ne')).mul
      ((continuousOn_const.div cr (fun w hw => (hr w hw).ne')).pow 2)
  have hB0 : 0 ≤ ∫ w in v..0, S.lam u w / (1 - S.mu u w) *
      (S.r u v / S.r u w) ^ 2 :=
    intervalIntegral.integral_nonneg hv (fun w hw =>
      mul_nonneg (div_nonneg (hl w hw).le (hg w hw).le) (sq_nonneg _))
  have hB : (∫ w in v..0, S.lam u w / (1 - S.mu u w) *
      (S.r u v / S.r u w) ^ 2) ≤ Λ * (-v) := by
    have hh := intervalIntegral.integral_mono_on (μ := volume) hv
      (cB.intervalIntegrable_of_Icc hv) (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ =>
          Λ) volume v 0)
      (fun w hw => by
        have hrad : S.r u v ≤ S.r u w := radius_out_le (S := S) hS huv.le hw.1 (by
          rintro ⟨x, y⟩ ⟨rfl, hvy, hyw⟩
          exact hs ⟨rfl, hvy, hyw.trans hw.2⟩)
        have hratio : 0 ≤ S.r u v / S.r u w ∧ S.r u v / S.r u w ≤ 1 :=
          ⟨div_nonneg (hr v ⟨le_rfl, hv⟩).le (hr w hw).le,
            (div_le_one (hr w hw)).mpr hrad⟩
        exact (mul_le_of_le_one_right
          (div_nonneg (hl w hw).le (hg w hw).le)
          (show (S.r u v / S.r u w) ^ 2 ≤ 1 by nlinarith only [hratio.1, hratio.2])).trans (hopt w
              hw))
    simpa only [intervalIntegral.integral_const, smul_eq_mul, zero_sub, mul_comm] using hh
  have hcs := scalar_oscillation_cauchy_schwarz hS huv hv hs
  have hAB := (mul_le_mul_of_nonneg_right hA' hB0).trans
    (mul_le_mul_of_nonneg_left hB (mul_nonneg (by norm_num) hm0))
  have htime : (2 * Λ * S.m u 0) * (-v) ≤ (2 * Λ * S.m u 0) * (-u) :=
    mul_le_mul_of_nonneg_left (show -v ≤ -u by linarith only [huv])
      (mul_nonneg (mul_nonneg (by norm_num) hΛ) hm0)
  exact (hcs.trans hAB).trans (by nlinarith only [htime])

/-- [node cg:global-scaled-scalar] Absolute scalar size on the complete
outgoing row, including its regular axis. The supplied finite optical bound
Λ is uniform on this row and may depend on the fixed solution. The numerical
constants are universal and independent of the solution, coupling, and labels. -/
theorem global_scaled_scalar {e u Λ : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hu : u < 0) (hs : outSeg u u 0 ⊆ D)
    (hopt : ∀ w ∈ Icc u 0, S.lam u w / (1 - S.mu u w) ≤ Λ)
    {v : ℝ} (hv : v ∈ Icc u 0) :
    S.r u v * ‖S.phi u v‖ ≤ S.r u 0 * ‖S.phi u 0‖ +
      Real.sqrt (2 * Λ * S.m u 0 * (-u)) := by
  have haxis := hS.axis u (hs ⟨rfl, le_rfl, hu.le⟩)
  have hR := hS.r_pos (u, 0) (hs ⟨rfl, hu.le, le_rfl⟩) hu
  rcases hv.1.eq_or_lt with rfl | huv
  · rw [haxis.1, zero_mul]
    exact add_nonneg (mul_nonneg hR.le (norm_nonneg _)) (Real.sqrt_nonneg _)
  · have hsv : outSeg u v 0 ⊆ D := fun p hp => hs (outSeg_subset_outSeg huv.le le_rfl hp)
    have hcone : outSeg u u v ⊆ D := fun p hp => hs (outSeg_subset_outSeg le_rfl hv.2 hp)
    have hm : 0 ≤ S.m u v := by
      have h := mass_out_le hS le_rfl huv.le hcone
      rw [haxis.2.1] at h
      exact h
    have hosc := outgoing_scalar_oscillation hS huv hv.2 hsv hm
      (fun w hw => hopt w ⟨huv.le.trans hw.1, hw.2⟩)
    have hr := hS.r_pos (u, v) (hs ⟨rfl, hv⟩) huv
    have hrad := radius_out_le hS huv.le hv.2 hsv
    have hosc' : S.r u v * ‖S.phi u v - S.phi u 0‖ ≤
        Real.sqrt (2 * Λ * S.m u 0 * (-u)) := by
      apply Real.le_sqrt_of_sq_le
      simpa only [mul_pow] using hosc
    have htri := norm_add_le (S.phi u v - S.phi u 0) (S.phi u 0)
    rw [sub_add_cancel] at htri
    calc
      _ ≤ S.r u v * (‖S.phi u v - S.phi u 0‖ + ‖S.phi u 0‖) :=
        mul_le_mul_of_nonneg_left htri hr.le
      _ = S.r u v * ‖S.phi u v - S.phi u 0‖ + S.r u v * ‖S.phi u 0‖ := by ring
      _ ≤ Real.sqrt (2 * Λ * S.m u 0 * (-u)) + S.r u 0 * ‖S.phi u 0‖ :=
        add_le_add hosc' (mul_le_mul_of_nonneg_right hrad (norm_nonneg _))
      _ = _ := add_comm _ _

end EmcsfAcExtension.Global.Gap
