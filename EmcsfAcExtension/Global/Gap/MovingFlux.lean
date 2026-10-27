/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Global.Gap.AnnularFlux
public import EmcsfAcExtension.Global.Gap.Collar
import EmcsfAcExtension.Local.Calculus.Reconstruction

/-! # Moving-collar scalar flux algebra

The exact coefficients `9/4` are uniform in the solution and collar. The
geometric ratio and scalar/electric integral estimates are explicit inputs
of the internal algebraic lemma. Source: charged_SF_new_version.tex:L1711–1726.
-/

public section

namespace EmcsfAcExtension.Global.Annulus

/-- [internal] The final complex quadratic calculation for a moving collar.
The ratio and transport bounds are discharged by their separate geometric
and integral proofs before this can close `cg:moving-flux`. -/
theorem moving_flux_algebra {A₁ A₂ n g d F₁ : ℝ} {z I E : ℂ}
    (hn : 0 < n) (hg : 0 ≤ g) (hd : 0 < d) (hA₁ : 0 ≤ A₁)
    (hA₂ : A₂ = g / (2 * n))
    (hratio : A₂ ≤ (g / (d * (1 - (1 / 1024 : ℝ)))) * A₁)
    (hI : ‖I‖ ^ 2 ≤ 2 * n ^ 2 / (1 - (1 / 1024 : ℝ)))
    (hE : ‖E‖ ^ 2 ≤ (1 / 1024 : ℝ) * n ^ 2 / 4096)
    (hF : A₁ * ‖z‖ ^ 2 ≤ F₁) :
    A₂*‖z+I+E‖^2 ≤ 9*g/(4*d)*F₁+(9/4:ℝ)*g*n := by
  have hA₂0 : 0 ≤ A₂ := by rw [hA₂]; positivity
  have hy := young_norm_sq (z+I) E (by norm_num : (0:ℝ)<1/1024)
  have hy' := young_norm_sq z I (by norm_num : (0:ℝ)<1)
  norm_num at hy hy'
  have hz := mul_le_mul_of_nonneg_right hratio (sq_nonneg ‖z‖)
  have hF₀ : 0 ≤ F₁ := (mul_nonneg hA₁ (sq_nonneg _)).trans hF
  have hc : 0 ≤ g/(d*(1-(1/1024:ℝ))) := by positivity
  have hf := mul_le_mul_of_nonneg_left hF hc
  have hi := mul_le_mul_of_nonneg_left hI hA₂0
  have he := mul_le_mul_of_nonneg_left hE hA₂0
  have hyw := mul_le_mul_of_nonneg_left hy hA₂0
  have hyw' := mul_le_mul_of_nonneg_left hy' hA₂0
  have heqI : (g/(2*n))*(2*n^2/(1-(1/1024:ℝ))) = g*n*(1024/1023) := by
    field_simp [hn.ne']
    ; ring
  have heqE : (g/(2*n))*((1/1024:ℝ)*n^2/4096) = g*n/8388608 := by
    field_simp [hn.ne']
    ; ring
  rw [hA₂,heqI] at hi
  rw [hA₂,heqE] at he
  have hmain : A₂*‖z+I+E‖^2 ≤ (2050/1023:ℝ)*(g/d)*F₁ +
      ((2050/1023:ℝ)+(1025/8388608:ℝ))*g*n := by
    have hcoeff : g/(d*(1-(1/1024:ℝ))) = (1024/1023:ℝ)*(g/d) := by ring
    rw [hcoeff] at hf hz
    rw [←hA₂] at hi he
    nlinarith only [hyw,hyw',hz,hf,hi,he]
  have hprod : 0 ≤ (g/d)*F₁ := by positivity
  have hgn : 0 ≤ g*n := mul_nonneg hg hn.le
  have htarget : 9*g/(4*d)*F₁ = (9/4:ℝ)*((g/d)*F₁) := by ring
  rw [htarget]
  nlinarith only [hmain,hprod,hgn]


end EmcsfAcExtension.Global.Annulus

open Set MeasureTheory

namespace EmcsfAcExtension.Global.Annulus

/-- [node lem:charged-conditional-gap#collar-electric-mass]
The electric annular mass is bounded by `ε` times radial width, with
`ε=1/1024`, uniformly in the solution, coupling and annulus. -/
theorem collar_electric_mass {e δ u a b : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u u b ⊆ D) (hδ : 0 < δ ∧ δ ≤ 1)
    (hmu : ∀ v ∈ Icc u b, 0 ≤ S.mu u v)
    (hgap : ∀ v ∈ Icc u b, δ ≤ 1 - S.mu u v)
    (hsmall : ∀ v ∈ Icc u b, |e| * S.r u v * ‖S.phi u v‖ ≤ δ / 64) :
    2*((S.m u b-S.m u a)-(1/2:ℝ)*(∫v in a..b,
      S.lam u v*(1-S.mu u v)*‖S.theta u v/S.lam u v‖^2)) ≤
        (1/1024:ℝ)*(S.r u b-S.r u a) := by
  have hs' : outSeg u a b⊆D := fun p hp=>hs (outSeg_subset_outSeg hua.le le_rfl hp)
  have hp (v : ℝ) (hv : v∈Icc a b) : (u,v)∈D := hs' ⟨rfl,hv⟩
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs'
  have cq := Calculus.continuousOn_out_section hS.cont_Q hs'
  have cr := Calculus.continuousOn_out_section hS.cont_r hs'
  have csrc := cl.mul ((cq.pow 2).div (cr.pow 2) (fun v hv=>
    pow_ne_zero _ (hS.r_pos (u,v) (hp v hv) (hua.trans_le hv.1)).ne'))
  have hpoint (v : ℝ) (hv : v∈Icc a b) :
      S.lam u v*(S.Q u v^2/S.r u v^2)≤S.lam u v*(1/1024:ℝ) := by
    have huv := hua.trans_le hv.1
    have hvb : v∈Icc u b := ⟨huv.le,hv.2⟩
    have hrel := Gap.relative_charge hS huv
      (fun p hp=>hs (outSeg_subset_outSeg le_rfl hv.2 hp)) hδ (hmu v hvb)
      (fun x hx=>hgap x ⟨hx.1,hx.2.trans hv.2⟩)
      (fun x hx=>hsmall x ⟨hx.1,hx.2.trans hv.2⟩)
    apply mul_le_mul_of_nonneg_left _ (hS.lam_pos (u,v) (hp v hv)).le
    have hg := hS.one_sub_mu_pos (u,v) (hp v hv)
    exact (hrel.1.trans hrel.2).trans (by linarith only [hg])
  have h := intervalIntegral.integral_mono_on hab
    (csrc.intervalIntegrable_of_Icc (μ:=volume) hab)
    ((cl.mul continuousOn_const).intervalIntegrable_of_Icc (μ:=volume) hab) hpoint
  change (∫v in a..b,S.lam u v*(S.Q u v^2/S.r u v^2))≤
    (∫v in a..b,S.lam u v*(1/1024:ℝ)) at h
  rw [intervalIntegral.integral_mul_const,
    ←(Calculus.out_integralForm hS hua.le hab hs').1.2] at h
  rw [(annular_masses hS hua hab hs').2.2]
  nlinarith only [h]

/-- [internal] Positive annular mass and electric control turn the annular
ratio into the reciprocal collar estimate, without dividing by scalar mass. -/
theorem collar_ratio_algebra {r₂ n₁ n₂ g₁ g₂ A d : ℝ}
    (hr₂ : 0 < r₂) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hg₁ : 0 < g₁) (hg₂ : 0 < g₂)
    (hd : 0 < d) (hratio : 1 + A / (g₂ * r₂) ≤ n₂ * g₁ / (n₁ * g₂))
    (hmass : d * (1 - (1 / 1024 : ℝ)) * r₂ ≤ A + g₂ * r₂) :
    g₂*n₁/(g₁*n₂)≤g₂/(d*(1-(1/1024:ℝ))) := by
  have hh := (le_div_iff₀ (mul_pos hn₁ hg₂)).mp hratio
  have hh' : (A+g₂*r₂)*n₁≤n₂*g₁*r₂ := by
    have h := mul_le_mul_of_nonneg_right hh hr₂.le
    have heq : (1+A/(g₂*r₂))*(n₁*g₂)*r₂=(A+g₂*r₂)*n₁ := by
      field_simp [hg₂.ne',hr₂.ne']
      ; ring
    rw [heq] at h
    exact h
  have hm := mul_le_mul_of_nonneg_right hmass hn₁.le
  have hi : n₁*(d*(1-(1/1024:ℝ)))≤g₁*n₂ := by
    nlinarith only [hm,hh',hr₂]
  apply (div_le_div_iff₀ (mul_pos hg₁ hn₂) (by positivity : 0<d*(1-(1/1024:ℝ)))).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hi hg₂.le]

end EmcsfAcExtension.Global.Annulus

namespace EmcsfAcExtension.Global.Gap

/-- [node cg:collar-ratio]
The reciprocal annular optical ratio on an actual fractional collar. The
fixed perturbation is `1/1024`, uniformly in all solution and collar data. -/
theorem collar_ratio {e δ u a b d : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u u b ⊆ D) (hδ : 0 < δ ∧ δ ≤ 1)
    (hmu : ∀ v ∈ Icc u b, 0 ≤ S.mu u v)
    (hgap : ∀ v ∈ Icc u b, δ ≤ 1 - S.mu u v)
    (hsmall : ∀ v ∈ Icc u b, |e| * S.r u v * ‖S.phi u v‖ ≤ δ / 64)
    (hd : 0 < d) (hcollar : S.r u a = (1 - d) * S.r u b) :
    (1-S.mu u b)*(-S.nu u a)/((1-S.mu u a)*(-S.nu u b))≤
      (1-S.mu u b)/(d*(1-(1/1024:ℝ))) := by
  have hs' : outSeg u a b⊆D := fun p hp=>hs (outSeg_subset_outSeg hua.le le_rfl hp)
  have ha : (u,a)∈D := hs' ⟨rfl,le_rfl,hab⟩
  have hb : (u,b)∈D := hs' ⟨rfl,hab,le_rfl⟩
  have hr₂ := hS.r_pos (u,b) hb (hua.trans_le hab)
  have hratio := Annulus.ratio hS hua hab hs hδ hmu hgap hsmall
  have hel := Annulus.collar_electric_mass hS hua hab hs hδ hmu hgap hsmall
  apply Annulus.collar_ratio_algebra hr₂
    (neg_pos.mpr (hS.nu_neg (u,a) ha)) (neg_pos.mpr (hS.nu_neg (u,b) hb))
    (hS.one_sub_mu_pos (u,a) ha) (hS.one_sub_mu_pos (u,b) hb) hd hratio
  have hr₁ := hS.r_pos (u,a) ha hua
  have hm₁ : 2*S.m u a<S.r u a := by
    have hm := (div_lt_iff₀ hr₁).mp (sub_pos.mp (hS.one_sub_mu_pos (u,a) ha))
    simpa only [one_mul] using hm
  have heq : (1-S.mu u b)*S.r u b=S.r u b-2*S.m u b := by
    dsimp [Fields.mu]
    field_simp [hr₂.ne']
  rw [heq]
  nlinarith only [hel,hm₁,hcollar]

end EmcsfAcExtension.Global.Gap

namespace EmcsfAcExtension.Global.Annulus

variable {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}

/-- [internal] The exact collar weight derivative in null labels. -/
theorem collar_weight_hasDerivAt (hS : IsSolution e S D) {u a b x : ℝ}
    (hua : u < a) (hs : outSeg u a b ⊆ D) (hx : x ∈ Ioo a b) :
    HasDerivAt (fun v => S.nu u v ^ 2 / S.r u v)
      (S.lam u x * S.nu u x ^ 2 / S.r u x ^ 2 *
        (2 * ((S.mu u x - S.Q u x ^ 2 / S.r u x ^ 2) / (1 - S.mu u x)) - 1)) x := by
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have dr : HasDerivAt (S.r u) (S.lam u x) x := by
    apply Local.hasDerivAt_of_integralForm_interior hx (cl.mono Ioo_subset_Icc_self)
    intro c d hc hcd hd
    exact (hS.eq_out u c d (hua.trans hc) hcd (by
      rintro ⟨s,t⟩ ⟨rfl, hmem⟩
      exact hs ⟨rfl, hc.le.trans hmem.1, hmem.2.trans hd.le⟩)).1
  have hp := hs (show (u,x) ∈ outSeg u a b from ⟨rfl,hx.1.le,hx.2.le⟩)
  have hr := (hS.r_pos (u,x) hp (hua.trans hx.1)).ne'
  have hg := (hS.one_sub_mu_pos (u,x) hp).ne'
  have hd := ((Gap.nu_out_hasDerivAt hS hua hs hx).pow 2).div dr hr
  convert hd using 1; dsimp only [Pi.div_apply, Pi.pow_apply, Fields.rUV];
    field_simp [hr,hg]; ring

/-- [internal] The collar expansion bounds its scalar Cauchy–Schwarz weight.
The coefficient `2/(1-1/1024)` is uniform in all solution and cone parameters. -/
theorem collar_weight_integral_of_expansion {δ : ℝ} (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u u b ⊆ D)
    (hδ : 0 < δ ∧ δ ≤ 1) (hmu : ∀ v ∈ Icc u b, 0 ≤ S.mu u v)
    (hgap : ∀ v ∈ Icc u b, δ ≤ 1 - S.mu u v)
    (hsmall : ∀ v ∈ Icc u b, |e| * S.r u v * ‖S.phi u v‖ ≤ δ / 64)
    (hexp : ∀ v ∈ Icc a b,
      1 ≤ (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v)) :
    (∫ v in a..b, S.nu u v ^ 2 / (1 - S.mu u v) * (S.lam u v / S.r u v ^ 2)) ≤
      (2 / (1 - (1/1024:ℝ))) *
        (S.nu u b ^ 2 / S.r u b - S.nu u a ^ 2 / S.r u a) ∧
    (∫ v in a..b, S.nu u v ^ 2 / (1 - S.mu u v) * (S.lam u v / S.r u v ^ 2)) ≤
      (2 / (1 - (1/1024:ℝ))) * S.nu u b ^ 2 / S.r u b := by
  have hs' : outSeg u a b ⊆ D := fun p hp => hs (outSeg_subset_outSeg hua.le le_rfl hp)
  have hp (v : ℝ) (hv : v ∈ Icc a b) : (u,v) ∈ D := hs' ⟨rfl,hv⟩
  have cr := Calculus.continuousOn_out_section hS.cont_r hs'
  have cn := Calculus.continuousOn_out_section hS.cont_nu hs'
  have cm := Calculus.continuousOn_out_section hS.cont_m hs'
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs'
  have cq := Calculus.continuousOn_out_section hS.cont_Q hs'
  have hr v (hv : v ∈ Icc a b) := hS.r_pos (u,v) (hp v hv) (hua.trans_le hv.1)
  have hg v (hv : v ∈ Icc a b) := hS.one_sub_mu_pos (u,v) (hp v hv)
  have cg : ContinuousOn (fun v => 1 - S.mu u v) (Icc a b) :=
    continuousOn_const.sub ((continuousOn_const.mul cm).div cr (fun v hv => (hr v hv).ne'))
  have ct : ContinuousOn (fun v =>
      (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v)) (Icc a b) :=
    (((continuousOn_const.mul cm).div cr (fun v hv => (hr v hv).ne')).sub
      ((cq.pow 2).div (cr.pow 2) (fun v hv => pow_ne_zero _ (hr v hv).ne'))).div cg
      (fun v hv => (hg v hv).ne')
  have cw : ContinuousOn (fun v => S.nu u v ^ 2 / S.r u v) (Icc a b) :=
    (cn.pow 2).div cr (fun v hv => (hr v hv).ne')
  have cB : ContinuousOn (fun v => S.nu u v ^ 2 / (1 - S.mu u v) *
      (S.lam u v / S.r u v ^ 2)) (Icc a b) :=
    ((cn.pow 2).div cg (fun v hv => (hg v hv).ne')).mul
      (cl.div (cr.pow 2) (fun v hv => pow_ne_zero _ (hr v hv).ne'))
  have cW : ContinuousOn (fun v => S.lam u v * S.nu u v ^ 2 / S.r u v ^ 2 *
      (2 * ((S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v)) - 1))
      (Icc a b) :=
    ((cl.mul (cn.pow 2)).div (cr.pow 2) (fun v hv => pow_ne_zero _ (hr v hv).ne')).mul
      ((continuousOn_const.mul ct).sub continuousOn_const)
  have hcoef v (hv : v ∈ Icc a b) : 1 / (1 - S.mu u v) ≤
      (2 / (1 - (1/1024:ℝ))) *
        (2 * ((S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v)) - 1) := by
    have huv : u < v := hua.trans_le hv.1
    have hmem : v ∈ Icc u b := ⟨huv.le,hv.2⟩
    have hc := Gap.relative_charge hS huv
      (fun p hp => hs (outSeg_subset_outSeg le_rfl hv.2 hp)) hδ (hmu v hmem)
      (fun s hs => hgap s ⟨hs.1,hs.2.trans hv.2⟩)
      (fun s hs => hsmall s ⟨hs.1,hs.2.trans hv.2⟩)
    have hq := hc.1.trans hc.2
    have ht : 1 - S.mu u v ≤ S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2 := by
      simpa only [one_mul] using (le_div_iff₀ (hg v hv)).mp (hexp v hv)
    have hm : (1/2:ℝ) ≤ S.mu u v := by
      have hq0 : 0 ≤ S.Q u v ^ 2 / S.r u v ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
      linarith only [ht,hq0]
    have hc' : (1-(1/1024:ℝ)) ≤ 2 * (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) := by
      nlinarith only [hq,hm]
    apply (div_le_iff₀ (hg v hv)).mpr
    have he : ((2 / (1 - (1/1024:ℝ))) *
        (2 * ((S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v)) - 1)) *
        (1 - S.mu u v) = (2 / (1 - (1/1024:ℝ))) *
          (2 * (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) - (1 - S.mu u v)) := by
      field_simp [(hg v hv).ne']
    rw [he]
    nlinarith only [hc',ht]
  have hB := intervalIntegral.integral_mono_on hab
    (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab cB)
    (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab
      (cW.const_mul (2 / (1 - (1/1024:ℝ))))) (fun v hv => by
        have hfactor : 0 ≤ S.lam u v * S.nu u v ^ 2 / S.r u v ^ 2 :=
          div_nonneg (mul_nonneg (hS.lam_pos (u,v) (hp v hv)).le (sq_nonneg _)) (sq_nonneg _)
        have h := mul_le_mul_of_nonneg_left (hcoef v hv) hfactor
        convert h using 1 <;> ring)
  change (∫ v in a..b, S.nu u v ^ 2 / (1 - S.mu u v) * (S.lam u v / S.r u v ^ 2)) ≤
    ∫ v in a..b, (2 / (1 - (1/1024:ℝ))) * (S.lam u v * S.nu u v ^ 2 / S.r u v ^ 2 *
      (2 * ((S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v)) - 1)) at hB
  have hW := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab cw
    (fun v hv => collar_weight_hasDerivAt hS hua hs' hv)
    (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab cW)
  rw [intervalIntegral.integral_const_mul,hW] at hB
  refine ⟨hB, hB.trans ?_⟩
  have ha : a ∈ Icc a b := ⟨le_rfl,hab⟩
  have hwa := div_nonneg (sq_nonneg (S.nu u a)) (hr a ha).le
  calc
    _ ≤ (2 / (1 - (1/1024:ℝ))) * (S.nu u b ^ 2 / S.r u b) :=
      mul_le_mul_of_nonneg_left (sub_le_self _ hwa) (by norm_num)
    _ = _ := by ring

/-- [internal] The scalar collar error under a proved collar expansion bound.
The coefficient is exactly `2/(1-1/1024)` on twice the scalar mass. -/
theorem scalar_collar_error_of_expansion {δ : ℝ} (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u u b ⊆ D)
    (hδ : 0 < δ ∧ δ ≤ 1) (hmu : ∀ v ∈ Icc u b, 0 ≤ S.mu u v)
    (hgap : ∀ v ∈ Icc u b, δ ≤ 1 - S.mu u v)
    (hsmall : ∀ v ∈ Icc u b, |e| * S.r u v * ‖S.phi u v‖ ≤ δ / 64)
    (hexp : ∀ v ∈ Icc a b,
      1 ≤ (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v)) :
    ‖∫ v in a..b, ((-S.nu u v / S.r u v : ℝ) : ℂ) * S.theta u v‖ ^ 2 ≤
      (2 / (1 - (1/1024:ℝ))) *
        (∫ v in a..b, S.lam u v * (1 - S.mu u v) * ‖S.theta u v / S.lam u v‖ ^ 2) *
        S.nu u b ^ 2 / S.r u b := by
  have hs' : outSeg u a b ⊆ D := fun p hp => hs (outSeg_subset_outSeg hua.le le_rfl hp)
  have hA : 0 ≤ ∫ v in a..b, S.lam u v * (1 - S.mu u v) *
      ‖S.theta u v / S.lam u v‖ ^ 2 := by
    have h := (annular_masses hS hua hab hs').1
    linarith only [h]
  have hB := (collar_weight_integral_of_expansion hS hua hab hs hδ hmu hgap hsmall hexp).2
  have h := (weighted_scalar_cauchy_schwarz hS hua hab hs').trans
    (mul_le_mul_of_nonneg_left hB hA)
  convert h using 1; ring


end EmcsfAcExtension.Global.Annulus

namespace EmcsfAcExtension.Global.Gap

/-- [internal] The actual moving-collar scalar flux comparison after the
collar expansion estimate has been proved. All constants are fixed. -/
theorem moving_flux_of_expansion {e δ u a b : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u u b ⊆ D) (hδ : 0 < δ ∧ δ ≤ 1)
    (hmu : ∀ v ∈ Icc u b, 0 ≤ S.mu u v)
    (hgap : ∀ v ∈ Icc u b, δ ≤ 1 - S.mu u v)
    (hsmall : ∀ v ∈ Icc u b, |e| * S.r u v * ‖S.phi u v‖ ≤ δ / 64)
    (hcollar : S.r u a = (7 / 8 : ℝ) * S.r u b)
    (hexp : ∀ v ∈ Icc a b, 1 ≤ (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v)) :
    (1-S.mu u b)/(2*(-S.nu u b))*‖S.xi u b‖^2≤
      18*(1-S.mu u b)*(-S.mU u a)+(9/4:ℝ)*(1-S.mu u b)*(-S.nu u b) := by
  have hs' : outSeg u a b⊆D := fun p hp=>hs (outSeg_subset_outSeg hua.le le_rfl hp)
  have ha : (u,a)∈D := hs' ⟨rfl,le_rfl,hab⟩
  have hb : (u,b)∈D := hs' ⟨rfl,hab,le_rfl⟩
  have hr₁ := hS.r_pos (u,a) ha hua
  have hr₂ := hS.r_pos (u,b) hb (hua.trans_le hab)
  have hn₁ := neg_pos.mpr (hS.nu_neg (u,a) ha)
  have hn₂ := neg_pos.mpr (hS.nu_neg (u,b) hb)
  have hg₁ := hS.one_sub_mu_pos (u,a) ha
  have hg₂ := hS.one_sub_mu_pos (u,b) hb
  let I : ℂ := ∫v in a..b,((-S.nu u v/S.r u v:ℝ):ℂ)*S.theta u v
  let E : ℂ := (-Complex.I)*(∫v in a..b,
    ((e*S.Q u v*(-S.nu u v)*S.lam u v/((1-S.mu u v)*S.r u v):ℝ):ℂ)*S.phi u v)
  have hratio := collar_ratio hS hua hab hs hδ hmu hgap hsmall
    (by norm_num : (0:ℝ)<1/8) (show S.r u a=(1-(1/8:ℝ))*S.r u b by linarith only [hcollar])
  have hA₁ : 0≤(1-S.mu u a)/(2*(-S.nu u a)) := by positivity
  have hratio' := mul_le_mul_of_nonneg_right hratio hA₁
  have heq : ((1-S.mu u b)*(-S.nu u a)/((1-S.mu u a)*(-S.nu u b)))*
      ((1-S.mu u a)/(2*(-S.nu u a)))=(1-S.mu u b)/(2*(-S.nu u b)) := by
    field_simp [hg₁.ne',hn₁.ne',hn₂.ne',(hS.nu_neg (u,a) ha).ne,(hS.nu_neg (u,b) hb).ne]
  rw [heq] at hratio'
  have hmasses := Annulus.annular_masses hS hua hab hs'
  have hm₁ : 0≤S.m u a := by
    have h := (le_div_iff₀ hr₁).mp (hmu a ⟨hua.le,hab⟩)
    linarith only [h]
  have hm₂ : 2*S.m u b<S.r u b := by
    simpa only [one_mul] using (div_lt_iff₀ hr₂).mp (sub_pos.mp hg₂)
  have hA : (∫v in a..b,S.lam u v*(1-S.mu u v)*‖S.theta u v/S.lam u v‖^2)≤S.r u b := by
    linarith only [hmasses.2.1,hm₁,hm₂]
  have hscalar := Annulus.scalar_collar_error_of_expansion hS hua hab hs hδ hmu hgap hsmall hexp
  have hI : ‖I‖^2≤2*(-S.nu u b)^2/(1-(1/1024:ℝ)) := by
    have hc : 0≤(2/(1-(1/1024:ℝ)))*S.nu u b^2/S.r u b := by positivity
    have hh := mul_le_mul_of_nonneg_right hA hc
    have heq : S.r u b*((2/(1-(1/1024:ℝ)))*S.nu u b^2/S.r u b)=
      2*(-S.nu u b)^2/(1-(1/1024:ℝ)) := by field_simp [hr₂.ne']
    rw [heq] at hh
    change ‖I‖^2≤_ at hscalar
    exact hscalar.trans (by convert hh using 1; ring)
  have hwidth : (S.r u b-S.r u a)/S.r u a≤1 := by
    apply (div_le_iff₀ hr₁).mpr
    linarith only [hcollar,hr₂]
  have hlog := Annulus.log_sq_le_width hr₁ (radius_out_le hS hua.le hab hs') hwidth
  have he := em_error hS hua hab hs hδ hmu hgap hsmall
  have hE : ‖E‖^2≤(1/1024:ℝ)*(-S.nu u b)^2/4096 := by
    have hsquare := pow_le_pow_left₀ (norm_nonneg E) he 2
    have hlog₁ := hlog.2.trans hwidth
    have hh := mul_le_mul_of_nonneg_left hlog₁ (sq_nonneg ((-S.nu u b)/2048))
    rw [mul_pow] at hsquare
    change ‖E‖^2≤_ at hsquare
    nlinarith only [hsquare,hh]
  have hF : (1-S.mu u a)/(2*(-S.nu u a))*‖S.xi u a‖^2≤-S.mU u a := by
    rw [Annulus.incoming_flux_decomposition S u a]
    have he : 0≤(-S.nu u a)*S.Q u a^2/(2*S.r u a^2) := by positivity
    linarith only [he]
  have h := Annulus.moving_flux_algebra hn₂ hg₂.le (by norm_num : (0:ℝ)<1/8) hA₁ rfl
    hratio' hI hE hF
  have hxi := Annulus.xi_decomposition hS hua hab hs'
  change S.xi u b=S.xi u a+I+E at hxi
  rw [←hxi] at h
  convert h using 1; ring

end EmcsfAcExtension.Global.Gap

namespace EmcsfAcExtension.Global.Gap

/-- [node cg:scalar-collar-error]
The actual scalar collar error below an outer gap `1/256`. Its exact
coefficient is `2/(1-ε)` on twice the scalar mass, uniformly in all data. -/
theorem scalar_collar_error {e δ u₀ B : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle u₀ B)) (hδ : 0 < δ ∧ δ ≤ 1)
    (hmu : ∀ p ∈ triangle u₀ B, 0 ≤ S.mu p.1 p.2)
    (hgap : ∀ p ∈ triangle u₀ B, δ ≤ 1 - S.mu p.1 p.2)
    (hsmall : ∀ p ∈ triangle u₀ B, |e| * S.r p.1 p.2 * ‖S.phi p.1 p.2‖ ≤ δ / 64)
    {u a b : ℝ} (hu : u₀ ≤ u) (hua : u < a) (hab : a < b) (hb : b ≤ B)
    (hcollar : S.r u a = (1 - (1 / 8 : ℝ)) * S.r u b) (hnear : 1 - S.mu u b ≤ (1 / 256 : ℝ)) :
    ‖∫v in a..b,((-S.nu u v/S.r u v:ℝ):ℂ)*S.theta u v‖^2≤
      (2/(1-(1/1024:ℝ)))*(∫v in a..b,S.lam u v*(1-S.mu u v)*
        ‖S.theta u v/S.lam u v‖^2)*S.nu u b^2/S.r u b := by
  have hs : outSeg u u b⊆triangle u₀ B := by
    rintro ⟨x,y⟩ ⟨rfl,huy,hyb⟩
    exact ⟨hu,huy,hyb.trans hb⟩
  apply Annulus.scalar_collar_error_of_expansion hS hua hab.le hs hδ
    (fun x hx=>hmu (u,x) (hs ⟨rfl,hx⟩))
    (fun x hx=>hgap (u,x) (hs ⟨rfl,hx⟩))
    (fun x hx=>hsmall (u,x) (hs ⟨rfl,hx⟩))
  intro x hx
  exact (collar_expansion hS hδ hmu hgap hsmall hu hua hab hb hcollar hnear x hx).2.le

/-- [node cg:moving-flux]
The actual scalar incoming-flux comparison on the one-eighth collar.
The coefficient `18` equals `9/(4d)` for `d=1/8`; both it and `9/4` are
uniform in all solution, coupling, gap and triangle parameters. -/
theorem moving_flux {e δ u₀ B : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle u₀ B)) (hδ : 0 < δ ∧ δ ≤ 1)
    (hmu : ∀ p ∈ triangle u₀ B, 0 ≤ S.mu p.1 p.2)
    (hgap : ∀ p ∈ triangle u₀ B, δ ≤ 1 - S.mu p.1 p.2)
    (hsmall : ∀ p ∈ triangle u₀ B, |e| * S.r p.1 p.2 * ‖S.phi p.1 p.2‖ ≤ δ / 64)
    {u a b : ℝ} (hu : u₀ ≤ u) (hua : u < a) (hab : a < b) (hb : b ≤ B)
    (hcollar : S.r u a = (1 - (1 / 8 : ℝ)) * S.r u b) (hnear : 1 - S.mu u b ≤ (1 / 256 : ℝ)) :
    (1-S.mu u b)/(2*(-S.nu u b))*‖S.xi u b‖^2≤
      18*(1-S.mu u b)*(-S.mU u a)+(9/4:ℝ)*(1-S.mu u b)*(-S.nu u b) := by
  have hs : outSeg u u b⊆triangle u₀ B := by
    rintro ⟨x,y⟩ ⟨rfl,huy,hyb⟩
    exact ⟨hu,huy,hyb.trans hb⟩
  apply moving_flux_of_expansion hS hua hab.le hs hδ
    (fun x hx=>hmu (u,x) (hs ⟨rfl,hx⟩))
    (fun x hx=>hgap (u,x) (hs ⟨rfl,hx⟩))
    (fun x hx=>hsmall (u,x) (hs ⟨rfl,hx⟩))
  · convert hcollar using 1; ring
  · intro x hx
    exact (collar_expansion hS hδ hmu hgap hsmall hu hua hab hb hcollar hnear x hx).2.le

end EmcsfAcExtension.Global.Gap

namespace EmcsfAcExtension.Global.Annulus

/-- [node lem:charged-conditional-gap#collar-weight-derivative]
The actual radial weight inequality on the interior of a near-trapped collar.
The null derivative is divided by its positive radial Jacobian `λ`. The
coefficient `2/(1-1/1024)` is exact and uniform in all solution data. -/
theorem collar_weight_derivative {e δ u₀ B : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle u₀ B)) (hδ : 0 < δ ∧ δ ≤ 1)
    (hmu : ∀ p ∈ triangle u₀ B, 0 ≤ S.mu p.1 p.2)
    (hgap : ∀ p ∈ triangle u₀ B, δ ≤ 1 - S.mu p.1 p.2)
    (hsmall : ∀ p ∈ triangle u₀ B, |e| * S.r p.1 p.2 * ‖S.phi p.1 p.2‖ ≤ δ / 64)
    {u a b x : ℝ} (hu : u₀ ≤ u) (hua : u < a) (hab : a < b) (hb : b ≤ B)
    (hcollar : S.r u a = (1 - (1 / 8 : ℝ)) * S.r u b) (hnear : 1 - S.mu u b ≤ (1 / 256 : ℝ))
    (hx : x ∈ Ioo a b) :
    S.nu u x^2/((1-S.mu u x)*S.r u x^2)≤
      (2/(1-(1/1024:ℝ)))*(deriv (fun v=>S.nu u v^2/S.r u v) x/S.lam u x) := by
  have hp : (u,x)∈triangle u₀ B := ⟨hu,(hua.trans hx.1).le,hx.2.le.trans hb⟩
  have hg := hS.one_sub_mu_pos (u,x) hp
  have ht := (Gap.collar_expansion hS hδ hmu hgap hsmall hu hua hab hb hcollar hnear
    x (Ioo_subset_Icc_self hx)).2.le
  have hs : outSeg u u x⊆triangle u₀ B := by
    rintro ⟨p,q⟩ ⟨rfl,huq,hqx⟩
    exact ⟨hu,huq,hqx.trans (hx.2.le.trans hb)⟩
  have hc := Gap.relative_charge hS (hua.trans hx.1) hs hδ (hmu (u,x) hp)
    (fun y hy=>hgap (u,y) (hs ⟨rfl,hy⟩)) (fun y hy=>hsmall (u,y) (hs ⟨rfl,hy⟩))
  have hq := hc.1.trans hc.2
  have ht' : 1-S.mu u x≤S.mu u x-S.Q u x^2/S.r u x^2 := by
    simpa only [one_mul] using (le_div_iff₀ hg).mp ht
  have hm : (1/2:ℝ)≤S.mu u x := by
    have hq0 : 0≤S.Q u x^2/S.r u x^2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
    linarith only [ht',hq0]
  have hc' : (1-(1/1024:ℝ))≤2*(S.mu u x-S.Q u x^2/S.r u x^2) := by
    nlinarith only [hq,hm]
  have hcoef : 1/(1-S.mu u x)≤(2/(1-(1/1024:ℝ)))*
      (2*((S.mu u x-S.Q u x^2/S.r u x^2)/(1-S.mu u x))-1) := by
    apply (div_le_iff₀ hg).mpr
    have heq : ((2/(1-(1/1024:ℝ)))*
        (2*((S.mu u x-S.Q u x^2/S.r u x^2)/(1-S.mu u x))-1))*(1-S.mu u x)=
        (2/(1-(1/1024:ℝ)))*(2*(S.mu u x-S.Q u x^2/S.r u x^2)-(1-S.mu u x)) := by
      field_simp [hg.ne']
    rw [heq]
    nlinarith only [ht',hc']
  have hder := collar_weight_hasDerivAt hS hua (show outSeg u a b⊆triangle u₀ B from by
    rintro ⟨p,q⟩ ⟨rfl,haq,hqb⟩
    exact ⟨hu,hua.le.trans haq,hqb.trans hb⟩) hx
  have hh := mul_le_mul_of_nonneg_left hcoef
    (div_nonneg (sq_nonneg (S.nu u x)) (sq_nonneg (S.r u x)))
  rw [hder.deriv]
  have hl := (hS.lam_pos (u,x) hp).ne'
  convert hh using 1 <;> field_simp [hl]

end EmcsfAcExtension.Global.Annulus
