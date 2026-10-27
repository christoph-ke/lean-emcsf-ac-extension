/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Global.Gap.Annulus
import EmcsfAcExtension.Infra.AC.Quotient

/-! # Quadratic comparisons for charged annular flux

All constants are exact and uniform in the solution, coupling and annulus.
The scalar comparison includes vanishing annular scalar mass. Source:
charged_SF_new_version.tex:L1599–1627 and approved internal project record (P2)–(A6).
-/

public section

open Set MeasureTheory Filter Topology

namespace EmcsfAcExtension.Global.Annulus

/-- [internal] Weighted Young inequality for the norm square, with no phase choice. -/
theorem young_norm_sq {E : Type*} [NormedAddCommGroup E]
    (z w : E) {ε : ℝ} (hε : 0 < ε) :
    ‖z + w‖ ^ 2 ≤ (1 + ε) * ‖z‖ ^ 2 + (1 + ε⁻¹) * ‖w‖ ^ 2 := by
  have ht : ‖z + w‖ ^ 2 ≤ (‖z‖ + ‖w‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_add_le z w) 2
  have hs := sq_nonneg (ε * ‖z‖ - ‖w‖)
  have hi : ε * ε⁻¹ = 1 := mul_inv_cancel₀ hε.ne'
  have hh : ε * ((1 + ε) * ‖z‖ ^ 2 + (1 + ε⁻¹) * ‖w‖ ^ 2 -
      (‖z‖ + ‖w‖) ^ 2) = (ε * ‖z‖ - ‖w‖) ^ 2 := by
    field_simp [hε.ne']
    ; ring
  have hn : 0 ≤ (1 + ε) * ‖z‖ ^ 2 + (1 + ε⁻¹) * ‖w‖ ^ 2 -
      (‖z‖ + ‖w‖) ^ 2 := by
    apply nonneg_of_mul_nonneg_left _ hε
    rw [mul_comm, hh]
    exact hs
  linarith only [ht, hn]

/-- [internal] The scalar endpoint comparison from a radial ratio and scalar
integral bound. This includes zero annular scalar mass. -/
theorem scalar_flux_of_ratio {r₁ r₂ n₁ n₂ g₁ g₂ A : ℝ} {z I : ℂ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hwidth : r₁ ≤ r₂) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hg₂ : 0 < g₂) (hA : 0 ≤ A)
    (hratio : 1 + A / (g₂ * r₂) ≤ g₁ * n₂ / (n₁ * g₂))
    (hI : ‖I‖ ^ 2 ≤ A * n₂ ^ 2 * (r₂ - r₁) / (g₂ * r₁ * r₂)) :
    g₂ / (2 * n₂) * ‖z + I‖ ^ 2 - g₁ / (2 * n₁) * ‖z‖ ^ 2 ≤
      n₂ * (r₂ - r₁) / (2 * r₁ * r₂) * (A + g₂ * r₂) := by
  rcases hA.eq_or_lt with hA | hA
  · rw [← hA, zero_mul, zero_mul, zero_div] at hI
    have hIz : I = 0 := norm_eq_zero.mp (by nlinarith only [hI, sq_nonneg ‖I‖, norm_nonneg I])
    rw [hIz, add_zero]
    have hc : g₂ / (2 * n₂) ≤ g₁ / (2 * n₁) := by
      rw [← hA, zero_div, add_zero] at hratio
      apply (div_le_div_iff₀ (by positivity : 0 < 2 * n₂) (by positivity : 0 < 2 * n₁)).mpr
      have h := (le_div_iff₀ (mul_pos hn₁ hg₂)).mp hratio
      nlinarith only [h]
    have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖z‖)
    have hw := sub_nonneg.mpr hwidth
    have hright : 0 ≤ n₂ * (r₂-r₁) / (2*r₁*r₂) * (A+g₂*r₂) := by positivity
    linarith only [hm, hright]
  · let q := A / (g₂ * r₂)
    have hq : 0 < q := div_pos hA (mul_pos hg₂ hr₂)
    have hy := young_norm_sq z I hq
    have hc : (g₂ / (2*n₂)) * (1+q) ≤ g₁ / (2*n₁) := by
      have hh := (le_div_iff₀ (mul_pos hn₁ hg₂)).mp hratio
      change (1+q)*(n₁*g₂) ≤ g₁*n₂ at hh
      calc
        (g₂/(2*n₂))*(1+q) = ((1+q)*(n₁*g₂))/(2*n₁*n₂) := by
          field_simp [hn₁.ne',hn₂.ne']
        _ ≤ (g₁*n₂)/(2*n₁*n₂) := div_le_div_of_nonneg_right hh (by positivity)
        _ = g₁/(2*n₁) := by field_simp [hn₁.ne',hn₂.ne']
    have hy' := mul_le_mul_of_nonneg_left hy (show 0 ≤ g₂/(2*n₂) by positivity)
    have hc' := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖z‖)
    have hcoef : 0 ≤ g₂/(2*n₂)*(1+q⁻¹) := by positivity
    have hi' := mul_le_mul_of_nonneg_left hI hcoef
    have he : g₂/(2*n₂)*(1+q⁻¹) * (A*n₂^2*(r₂-r₁)/(g₂*r₁*r₂)) =
        n₂*(r₂-r₁)/(2*r₁*r₂)*(A+g₂*r₂) := by
      dsimp [q]
      field_simp [hA.ne', hg₂.ne', hr₁.ne', hr₂.ne', hn₂.ne']
    rw [he] at hi'
    nlinarith only [hy', hc', hi']

/-- [internal] Bootstrap scalar smallness and relative charge bound the current
with the exact coefficient `1/2048`, uniformly in all parameters. -/
theorem em_current_bound {e Q r g δ : ℝ} {φ : ℂ}
    (hr : 0 < r) (hδ : 0 < δ) (hg : δ ≤ g)
    (hsmall : |e| * r * ‖φ‖ ≤ δ / 64)
    (hcharge : Q ^ 2 / r ^ 2 ≤ (1 / 1024 : ℝ)) :
    |e| * |Q| * ‖φ‖/g ≤ (1/2048:ℝ) := by
  have hg0 : 0 < g := hδ.trans_le hg
  have hq : |Q| ≤ r/32 := by
    apply (sq_le_sq₀ (abs_nonneg Q) (by positivity : 0 ≤ r/32)).mp
    have hh := (div_le_iff₀ (sq_pos_of_pos hr)).mp hcharge
    rw [sq_abs]
    nlinarith only [hh]
  apply (div_le_iff₀ hg0).mpr
  calc
    |e| * |Q| * ‖φ‖ ≤ |e| * (r/32)*‖φ‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hq (abs_nonneg e)) (norm_nonneg φ)
    _ = (|e| * r*‖φ‖)/32 := by ring
    _ ≤ (δ/64)/32 := div_le_div_of_nonneg_right hsmall (by norm_num)
    _ ≤ (1/2048:ℝ)*g := by linarith only [hg]

/-- [internal] Restore the electromagnetic perturbation and electric flux
without division by annular scalar mass. -/
theorem annular_flux_perturbation {A₁ A₂ B F₁ E₁ E₂ n : ℝ} {z I E : ℂ}
    (hA₂ : 0 ≤ A₂) (hE₁ : 0 ≤ E₁)
    (hF₁ : F₁ = A₁ * ‖z‖ ^ 2 + E₁)
    (hbase : A₂ * ‖z + I‖ ^ 2 - A₁ * ‖z‖ ^ 2 ≤ B)
    (herr : A₂ * 1025 * ‖E‖ ^ 2 ≤ B / 1024)
    (hel : E₂ ≤ n / 2048) :
    (A₂*‖z+I+E‖^2+E₂)-F₁ ≤
      (1/1024:ℝ)*F₁+(1+2*(1/1024:ℝ))*B+n/2048 := by
  have h := young_norm_sq (z+I) E (by norm_num : (0:ℝ)<1/1024)
  norm_num at h
  have hy := mul_le_mul_of_nonneg_left h hA₂
  nlinarith only [hy,hbase,herr,hel,hF₁,hE₁]

end EmcsfAcExtension.Global.Annulus

namespace EmcsfAcExtension.Global.Annulus

/-- [internal] The complete scalar-flux comparison, retaining the exact
intermediate bracket and covering zero scalar annular mass. All coefficients
are uniform in the solution, coupling, bootstrap gap and annulus. -/
theorem scalar_flux_comparison {e δ u a b : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u u b ⊆ D) (hδ : 0 < δ ∧ δ ≤ 1)
    (hmu : ∀ v ∈ Icc u b, 0 ≤ S.mu u v)
    (hgap : ∀ v ∈ Icc u b, δ ≤ 1 - S.mu u v)
    (hsmall : ∀ v ∈ Icc u b, |e| * S.r u v * ‖S.phi u v‖ ≤ δ / 64) :
    let A := ∫ v in a..b, S.lam u v * (1 - S.mu u v) *
      ‖S.theta u v / S.lam u v‖ ^ 2
    let I := ∫ v in a..b, ((-S.nu u v / S.r u v : ℝ) : ℂ) * S.theta u v
    (1 - S.mu u b) / (2 * (-S.nu u b)) * ‖S.xi u a + I‖ ^ 2 -
      (1 - S.mu u a) / (2 * (-S.nu u a)) * ‖S.xi u a‖ ^ 2 ≤
        (-S.nu u b) * (S.r u b - S.r u a) / (2 * S.r u a * S.r u b) *
          (A + (1 - S.mu u b) * S.r u b) ∧
    (-S.nu u b) * (S.r u b - S.r u a) / (2 * S.r u a * S.r u b) *
      (A + (1 - S.mu u b) * S.r u b) ≤
        (-S.nu u b) * (S.r u b - S.r u a) / (2 * S.r u a) := by
  dsimp only
  have hs' : outSeg u a b ⊆ D := fun p hp => hs (outSeg_subset_outSeg hua.le le_rfl hp)
  have ha : (u, a) ∈ D := hs' ⟨rfl, le_rfl, hab⟩
  have hb : (u, b) ∈ D := hs' ⟨rfl, hab, le_rfl⟩
  have hr₁ := hS.r_pos (u, a) ha hua
  have hr₂ := hS.r_pos (u, b) hb (hua.trans_le hab)
  have hn₁ := neg_pos.mpr (hS.nu_neg (u, a) ha)
  have hn₂ := neg_pos.mpr (hS.nu_neg (u, b) hb)
  have hg₂ := hS.one_sub_mu_pos (u, b) hb
  have hmasses := annular_masses hS hua hab hs'
  have hA : 0 ≤ ∫ v in a..b, S.lam u v * (1 - S.mu u v) *
      ‖S.theta u v / S.lam u v‖ ^ 2 := by linarith only [hmasses.1]
  have hrat := ratio hS hua hab hs hδ hmu hgap hsmall
  have hI := annular_scalar_integral hS hua hab hs hδ hmu hgap hsmall
  have hwidth := Gap.radius_out_le hS hua.le hab hs'
  constructor
  · apply scalar_flux_of_ratio hr₁ hr₂ hwidth hn₁ hn₂ hg₂ hA
    · simpa only [mul_comm] using hrat
    · simpa only [neg_sq] using hI
  · have hm₁ : 0 ≤ S.m u a := by
      have hm := (le_div_iff₀ hr₁).mp (hmu a ⟨hua.le, hab⟩)
      linarith only [hm]
    have heq : (1 - S.mu u b) * S.r u b = S.r u b - 2 * S.m u b := by
      dsimp [Fields.mu]
      field_simp [hr₂.ne']
    have hbracket : (∫ v in a..b, S.lam u v * (1 - S.mu u v) *
        ‖S.theta u v / S.lam u v‖ ^ 2) + (1-S.mu u b)*S.r u b ≤ S.r u b := by
      rw [heq]
      linarith only [hmasses.2.1, hm₁]
    have hc : 0 ≤ (-S.nu u b)*(S.r u b-S.r u a)/(2*S.r u a*S.r u b) :=
      div_nonneg (mul_nonneg hn₂.le (sub_nonneg.mpr hwidth)) (by positivity)
    calc
      _ ≤ ((-S.nu u b)*(S.r u b-S.r u a)/(2*S.r u a*S.r u b))*S.r u b :=
        mul_le_mul_of_nonneg_left hbracket hc
      _ = _ := by field_simp [hr₂.ne']

/-- [node lem:charged-conditional-gap#positive-scalar-mass-flux-comparison]
The optimized scalar comparison on an actual annulus. The scalar mass is
represented by its literal outgoing integral. Both constants are exact and
uniform; no positive lower bound for the scalar mass is imposed. -/
theorem positive_scalar_mass_flux_comparison {e δ u a b : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u u b ⊆ D) (hδ : 0 < δ ∧ δ ≤ 1)
    (hmu : ∀ v ∈ Icc u b, 0 ≤ S.mu u v)
    (hgap : ∀ v ∈ Icc u b, δ ≤ 1 - S.mu u v)
    (hsmall : ∀ v ∈ Icc u b, |e| * S.r u v * ‖S.phi u v‖ ≤ δ / 64)
    (_hpos : 0 < ∫ v in a..b, S.lam u v * (1 - S.mu u v) *
      ‖S.theta u v / S.lam u v‖ ^ 2) :
    let A := ∫ v in a..b, S.lam u v * (1 - S.mu u v) *
      ‖S.theta u v / S.lam u v‖ ^ 2
    let I := ∫ v in a..b, ((-S.nu u v / S.r u v : ℝ) : ℂ) * S.theta u v
    (1 - S.mu u b) / (2 * (-S.nu u b)) * ‖S.xi u a + I‖ ^ 2 -
      (1 - S.mu u a) / (2 * (-S.nu u a)) * ‖S.xi u a‖ ^ 2 ≤
        (-S.nu u b) * (S.r u b - S.r u a) / (2 * S.r u a * S.r u b) *
          (A + (1 - S.mu u b) * S.r u b) ∧
    (-S.nu u b) * (S.r u b - S.r u a) / (2 * S.r u a * S.r u b) *
      (A + (1 - S.mu u b) * S.r u b) ≤
        (-S.nu u b) * (S.r u b - S.r u a) / (2 * S.r u a) :=
  scalar_flux_comparison hS hua hab hs hδ hmu hgap hsmall

end EmcsfAcExtension.Global.Annulus

namespace EmcsfAcExtension.Global.Gap
/-- [internal] Exact characteristic FTC for the logarithm of the positive radius. -/
theorem log_radius_integralForm {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    IntegralForm (fun v=>Real.log (S.r u v)) (fun v=>S.lam u v/S.r u v) a b := by
  have hp (v : ℝ) (hv : v∈Icc a b) : (u,v)∈D := hs ⟨rfl,hv⟩
  have nr (v : ℝ) (hv : v∈Icc a b) : S.r u v≠0 :=
    (hS.r_pos (u,v) (hp v hv) (hua.trans_le hv.1)).ne'
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have hi := (cl.div cr nr).intervalIntegrable_of_Icc (μ:=volume) hab
  have hrow := Calculus.out_section hS hua.le hab hs
  have hr₁ := hS.r_pos (u,a) (hp a ⟨le_rfl,hab⟩) hua
  have hac := hrow.1.1.log_of_pos_le hr₁ (fun v hv=> by
    rw [uIcc_of_le hab] at hv
    have hrform := (hS.eq_out u a v hua hv.1 (fun p hp'=>hs
      ⟨hp'.1,hp'.2.1,hp'.2.2.trans hv.2⟩)).1
    have hnonneg := intervalIntegral.integral_nonneg (μ:=volume) hv.1
      (fun x hx=>(hS.lam_pos (u,x) (hp x ⟨hx.1,hx.2.trans hv.2⟩)).le)
    rw [←hrform.2] at hnonneg
    exact sub_nonneg.mp hnonneg)
  have hd : ∀ᵐ v, v∈uIcc a b → HasDerivAt (fun v=>Real.log (S.r u v))
      (S.lam u v/S.r u v) v := by
    rw [←ae_restrict_iff' measurableSet_uIcc,uIcc_of_le hab]
    filter_upwards [hrow.1.2,ae_restrict_mem measurableSet_Icc] with v hv hmem
    exact hv.log (nr v hmem)
  exact ⟨hi,(hac.integral_eq_sub_of_ae_hasDerivAt_normed hi hd).symm⟩
end EmcsfAcExtension.Global.Gap

namespace EmcsfAcExtension.Global.Gap
/-- [node cg:em-error]
The electromagnetic transport error has exact coefficient `1/2048`, equal to
`√ε/64` for `ε=1/1024`. Uniform in all solution and annulus parameters. -/
theorem em_error {e δ u a b : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hua : u < a) (hab : a ≤ b) (hs : outSeg u u b ⊆ D)
    (hδ : 0 < δ ∧ δ ≤ 1)
    (hmu : ∀ v ∈ Icc u b, 0 ≤ S.mu u v)
    (hgap : ∀ v ∈ Icc u b, δ ≤ 1 - S.mu u v)
    (hsmall : ∀ v ∈ Icc u b, |e| * S.r u v * ‖S.phi u v‖ ≤ δ / 64) :
    ‖(-Complex.I)*(∫v in a..b,
      ((e*S.Q u v*(-S.nu u v)*S.lam u v/
        ((1-S.mu u v)*S.r u v):ℝ):ℂ)*S.phi u v)‖ ≤
      (-S.nu u b)/2048*Real.log (S.r u b/S.r u a) := by
  have habs : outSeg u a b⊆D := fun p hp=>hs (outSeg_subset_outSeg hua.le le_rfl hp)
  have hp (v : ℝ) (hv : v∈Icc a b) : (u,v)∈D := habs ⟨rfl,hv⟩
  have hr (v : ℝ) (hv : v∈Icc a b) := hS.r_pos (u,v) (hp v hv) (hua.trans_le hv.1)
  have hn (v : ℝ) (hv : v∈Icc a b) : 0< -S.nu u v := neg_pos.mpr (hS.nu_neg (u,v) (hp v hv))
  have hl (v : ℝ) (hv : v∈Icc a b) := hS.lam_pos (u,v) (hp v hv)
  have hg (v : ℝ) (hv : v∈Icc a b) := hS.one_sub_mu_pos (u,v) (hp v hv)
  have cr := Calculus.continuousOn_out_section hS.cont_r habs
  have cl := Calculus.continuousOn_out_section hS.cont_lam habs
  have cn := Calculus.continuousOn_out_section hS.cont_nu habs
  have cq := Calculus.continuousOn_out_section hS.cont_Q habs
  have cp := Calculus.continuousOn_out_section hS.cont_phi habs
  have cmu := Calculus.continuousOn_out_section (continuousOn_mu hS) habs
  let f := fun v=> ((e*S.Q u v*(-S.nu u v)*S.lam u v/
        ((1-S.mu u v)*S.r u v):ℝ):ℂ)*S.phi u v
  have cf : ContinuousOn f (Icc a b) := by
    exact (Complex.continuous_ofReal.comp_continuousOn
      ((((continuousOn_const.mul cq).mul cn.neg).mul cl).div
        ((continuousOn_const.sub cmu).mul cr)
        (fun v hv=>mul_ne_zero (hg v hv).ne' (hr v hv).ne'))).mul cp
  have hbound (v : ℝ) (hv : v∈Icc a b) :
      ‖f v‖≤(-S.nu u b)/2048*(S.lam u v/S.r u v) := by
    have huv := hua.trans_le hv.1
    have hvb : v∈Icc u b := ⟨huv.le,hv.2⟩
    have hrel := relative_charge hS huv
      (fun p hp=>hs (outSeg_subset_outSeg le_rfl hv.2 hp)) hδ (hmu v hvb)
      (fun x hx=>hgap x ⟨hx.1,hx.2.trans hv.2⟩)
      (fun x hx=>hsmall x ⟨hx.1,hx.2.trans hv.2⟩)
    have hq : S.Q u v^2/S.r u v^2 ≤ (1/1024:ℝ) := by
      have hm := hS.one_sub_mu_pos (u,v) (hp v hv)
      exact (hrel.1.trans hrel.2).trans (by linarith only [hm])
    have hcur := Annulus.em_current_bound (hr v hv) hδ.1 (hgap v hvb) (hsmall v hvb) hq
    have hnu : -S.nu u v ≤ -S.nu u b := by
      have hh := nu_out_antitone hS huv hv.2 hs hδ hmu hgap hsmall
      linarith only [hh]
    have heq : ‖f v‖ = (|e| * |S.Q u v| * ‖S.phi u v‖/(1-S.mu u v))*
        (-S.nu u v)*(S.lam u v/S.r u v) := by
      dsimp [f]
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_div,abs_mul,abs_mul,abs_mul,
        abs_mul,abs_of_pos (hn v hv),abs_of_pos (hl v hv),
        abs_of_pos (hg v hv),abs_of_pos (hr v hv)]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [heq]
    calc
      _ ≤ (1/2048:ℝ)*(-S.nu u v)*(S.lam u v/S.r u v) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcur (hn v hv).le) (div_nonneg (hl v hv).le (hr v hv).le)
      _ ≤ (-S.nu u b)/2048*(S.lam u v/S.r u v) := by
        have hh := mul_le_mul_of_nonneg_right hnu
          (mul_nonneg (by norm_num : (0:ℝ)≤1/2048) (div_nonneg (hl v hv).le (hr v hv).le))
        nlinarith only [hh]
  have csrc := cl.div cr (fun v hv=>(hr v hv).ne')
  have hi := cf.intervalIntegrable_of_Icc (μ:=volume) hab
  have hlog := log_radius_integralForm hS hua hab habs
  have ha0 := (hr a ⟨le_rfl,hab⟩).ne'
  have hb0 := (hr b ⟨hab,le_rfl⟩).ne'
  calc
    _ = ‖∫v in a..b,f v‖ := by rw [norm_mul]; simp only [norm_neg,Complex.norm_I,one_mul]; rfl
    _ ≤ ∫v in a..b,‖f v‖ := intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫v in a..b,(-S.nu u b)/2048*(S.lam u v/S.r u v) :=
      intervalIntegral.integral_mono_on hab hi.norm
        ((csrc.intervalIntegrable_of_Icc (μ:=volume) hab).const_mul _) hbound
    _ = _ := by rw [intervalIntegral.integral_const_mul,←hlog.2,Real.log_div hb0 ha0]
end EmcsfAcExtension.Global.Gap

namespace EmcsfAcExtension.Global.Annulus
/-- [internal] The squared logarithm is bounded by radial fractional width. -/
theorem log_sq_le_width {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hw : r₁ ≤ r₂)
    (hwidth : (r₂ - r₁) / r₁ ≤ 1) :
    0≤Real.log (r₂/r₁) ∧ Real.log (r₂/r₁)^2≤(r₂-r₁)/r₁ := by
  have hr₂ : 0<r₂ := hr₁.trans_le hw
  have hL0 := Real.log_nonneg ((le_div_iff₀ hr₁).mpr (by simpa))
  have hlog := Real.log_le_sub_one_of_pos (div_pos hr₂ hr₁)
  have heq : r₂/r₁-1=(r₂-r₁)/r₁ := by field_simp
  rw [heq] at hlog
  have hx : 0≤(r₂-r₁)/r₁ := div_nonneg (sub_nonneg.mpr hw) hr₁.le
  exact ⟨hL0,(pow_le_pow_left₀ hL0 hlog 2).trans (by nlinarith only [hx,hwidth])⟩

/-- [internal] The fixed electromagnetic error consumes at most one `ε` of
the annular geometric term. All displayed constants are exact. -/
theorem annular_error_bound {n r D g L : ℝ} {E : ℂ}
    (hn : 0 < n) (hr : 0 < r) (hD : 0 ≤ D) (hg : 0 ≤ g) (hg₁ : g ≤ 1)
    (_hL : 0 ≤ L) (hLsq : L ^ 2 ≤ D / r) (hE : ‖E‖ ≤ n / 2048 * L) :
    g/(2*n)*1025*‖E‖^2 ≤ (n*D/(2*r))/1024 := by
  have hE2 := (pow_le_pow_left₀ (norm_nonneg E) hE 2).trans
    (show (n/2048*L)^2≤(n/2048)^2*(D/r) from by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left hLsq (sq_nonneg _))
  have hi := mul_le_mul_of_nonneg_left hE2
    (show 0≤g/(2*n)*1025 by positivity)
  have heq : (g/(2*n)*1025)*((n/2048)^2*(D/r)) =
      (1025/4194304:ℝ)*g*(n*D/(2*r)) := by field_simp [hn.ne',hr.ne']; ring
  rw [heq] at hi
  have hB : 0≤n*D/(2*r) := by positivity
  have hgB := mul_le_mul_of_nonneg_right hg₁ hB
  nlinarith only [hi,hB,hgB]

end EmcsfAcExtension.Global.Annulus

namespace EmcsfAcExtension.Global.Gap

/-- [node cg:annular-flux]
The total incoming flux comparison on an actual outgoing annulus. It holds
also for zero annular scalar mass. Its constants are independent of the
solution, coupling, triangle, gap bootstrap and annulus. -/
theorem annular_flux {e δ u a b : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u u b ⊆ D) (hδ : 0 < δ ∧ δ ≤ 1)
    (hmu : ∀ v ∈ Icc u b, 0 ≤ S.mu u v)
    (hgap : ∀ v ∈ Icc u b, δ ≤ 1 - S.mu u v)
    (hsmall : ∀ v ∈ Icc u b, |e| * S.r u v * ‖S.phi u v‖ ≤ δ / 64)
    (hwidth : (S.r u b - S.r u a) / S.r u a ≤ 1) :
    (-S.mU u b)-(-S.mU u a) ≤ (1/1024:ℝ)*(-S.mU u a) +
      (1+2*(1/1024:ℝ))*((-S.nu u b)*(S.r u b-S.r u a)/(2*S.r u a)) +
      (-S.nu u b)/2048 := by
  have hs' : outSeg u a b ⊆ D := fun p hp=>hs (outSeg_subset_outSeg hua.le le_rfl hp)
  have ha : (u,a)∈D := hs' ⟨rfl,le_rfl,hab⟩
  have hb : (u,b)∈D := hs' ⟨rfl,hab,le_rfl⟩
  have hr₁ := hS.r_pos (u,a) ha hua
  have hn₁ := neg_pos.mpr (hS.nu_neg (u,a) ha)
  have hn₂ := neg_pos.mpr (hS.nu_neg (u,b) hb)
  have hg₂ := hS.one_sub_mu_pos (u,b) hb
  have hrad := radius_out_le hS hua.le hab hs'
  let I : ℂ := ∫v in a..b,((-S.nu u v/S.r u v:ℝ):ℂ)*S.theta u v
  let E : ℂ := (-Complex.I)*(∫v in a..b,
    ((e*S.Q u v*(-S.nu u v)*S.lam u v/((1-S.mu u v)*S.r u v):ℝ):ℂ)*S.phi u v)
  have hbase := Annulus.scalar_flux_comparison hS hua hab hs hδ hmu hgap hsmall
  have hbase' := hbase.1.trans hbase.2
  have hlog := Annulus.log_sq_le_width hr₁ hrad hwidth
  have herr := Annulus.annular_error_bound hn₂ hr₁ (sub_nonneg.mpr hrad) hg₂.le
    (by linarith only [hmu b ⟨hua.le.trans hab,le_rfl⟩]) hlog.1 hlog.2
    (em_error hS hua hab hs hδ hmu hgap hsmall)
  have hcharge := relative_charge hS (hua.trans_le hab) hs hδ
    (hmu b ⟨hua.le.trans hab,le_rfl⟩) hgap hsmall
  have hq : S.Q u b^2/S.r u b^2 ≤ (1/1024:ℝ) :=
    (hcharge.1.trans hcharge.2).trans (by linarith only [hg₂])
  have hel : (-S.nu u b)*S.Q u b^2/(2*S.r u b^2) ≤ (-S.nu u b)/2048 := by
    have hh := mul_le_mul_of_nonneg_left hq (div_nonneg hn₂.le (by norm_num : (0:ℝ)≤2))
    convert hh using 1 <;> ring
  have hE₁ : 0 ≤ (-S.nu u a)*S.Q u a^2/(2*S.r u a^2) := by positivity
  have h := Annulus.annular_flux_perturbation (z:=S.xi u a) (I:=I) (E:=E)
    (div_nonneg hg₂.le (by positivity)) hE₁
    (Annulus.incoming_flux_decomposition S u a) hbase' herr hel
  have hxi := Annulus.xi_decomposition hS hua hab hs'
  change S.xi u b=S.xi u a+I+E at hxi
  rw [←hxi] at h
  rw [←Annulus.incoming_flux_decomposition S u b] at h
  exact h

end EmcsfAcExtension.Global.Gap

namespace EmcsfAcExtension.Global.Annulus

/-- [node lem:charged-conditional-gap#zero-scalar-mass-flux-comparison]
Zero annular scalar mass makes the scalar transport integral vanish and the
optical ratio constant. The E-free flux comparison follows without division
by scalar mass. All coefficients are exact and uniform in all parameters. -/
theorem zero_scalar_mass_flux_comparison {e δ u a b : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hua : u < a) (hab : a < b)
    (hs : outSeg u u b ⊆ D) (hδ : 0 < δ ∧ δ ≤ 1)
    (hmu : ∀ v ∈ Icc u b, 0 ≤ S.mu u v)
    (hgap : ∀ v ∈ Icc u b, δ ≤ 1 - S.mu u v)
    (hsmall : ∀ v ∈ Icc u b, |e| * S.r u v * ‖S.phi u v‖ ≤ δ / 64)
    (hzero : (∫ v in a..b, S.lam u v * (1 - S.mu u v) * ‖S.theta u v / S.lam u v‖ ^ 2) = 0) :
    (∫v in a..b,((-S.nu u v/S.r u v:ℝ):ℂ)*S.theta u v)=0 ∧
      EqOn (fun v=>(1-S.mu u v)/(-S.nu u v))
        (fun _=>(1-S.mu u a)/(-S.nu u a)) (Icc a b) ∧
      (1-S.mu u b)/(2*(-S.nu u b))*‖S.xi u a+
        (∫v in a..b,((-S.nu u v/S.r u v:ℝ):ℂ)*S.theta u v)‖^2-
        (1-S.mu u a)/(2*(-S.nu u a))*‖S.xi u a‖^2=0 := by
  have hs' : outSeg u a b⊆D := fun p hp=>hs (outSeg_subset_outSeg hua.le le_rfl hp)
  have hp (v : ℝ) (hv : v∈Icc a b) : (u,v)∈D := hs' ⟨rfl,hv⟩
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs'
  have ct := Calculus.continuousOn_out_section hS.cont_theta hs'
  have cg : ContinuousOn (fun v=>1-S.mu u v) (Icc a b) := continuousOn_const.sub
    (Calculus.continuousOn_out_section (Gap.continuousOn_mu hS) hs')
  have cx := ct.div (Complex.continuous_ofReal.comp_continuousOn cl)
    (fun v hv=>Complex.ofReal_ne_zero.mpr (hS.lam_pos (u,v) (hp v hv)).ne')
  let f := fun v=>S.lam u v*(1-S.mu u v)*‖S.theta u v/S.lam u v‖^2
  have cf : ContinuousOn f (Icc a b) := (cl.mul cg).mul (cx.norm.pow 2)
  have hf0 (v : ℝ) (hv : v∈Icc a b) : 0≤f v :=
    mul_nonneg (mul_nonneg (hS.lam_pos (u,v) (hp v hv)).le
      (hS.one_sub_mu_pos (u,v) (hp v hv)).le) (sq_nonneg _)
  have hnonneg : 0≤ᵐ[volume.restrict (Ioc a b)] f :=
    (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall
      (fun v hv=>hf0 v (Ioc_subset_Icc_self hv)))
  have hfae : f=ᵐ[volume.restrict (Ioc a b)] (fun _=>0) :=
    (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hab.le hnonneg
      (cf.intervalIntegrable_of_Icc hab.le)).mp hzero
  have hfae' : f=ᵐ[volume.restrict (Icc a b)] (fun _=>0) := by
    rwa [Measure.restrict_congr_set Ioc_ae_eq_Icc] at hfae
  have hfzero := Measure.eqOn_Icc_of_ae_eq volume hab.ne hfae' cf continuousOn_const
  have hI := annular_scalar_integral hS hua hab.le hs hδ hmu hgap hsmall
  rw [hzero,zero_mul,zero_mul,zero_div] at hI
  have hI0 : (∫v in a..b,((-S.nu u v/S.r u v:ℝ):ℂ)*S.theta u v)=0 :=
    norm_eq_zero.mp (by nlinarith only [hI,sq_nonneg ‖∫v in a..b,
      ((-S.nu u v/S.r u v:ℝ):ℂ)*S.theta u v‖,norm_nonneg (∫v in a..b,
      ((-S.nu u v/S.r u v:ℝ):ℂ)*S.theta u v)])
  have hconst : EqOn (fun v=>(1-S.mu u v)/(-S.nu u v))
      (fun _=>(1-S.mu u a)/(-S.nu u a)) (Icc a b) := by
    intro x hx
    have hr := radial_ratio_integral hS hua hx.1
      (fun p hp=>hs' (outSeg_subset_outSeg le_rfl hx.2 hp))
    have hi : (∫v in a..x,S.lam u v*(1-S.mu u v)/((-S.nu u v)*S.r u v)*
        ‖S.theta u v/S.lam u v‖^2)=0 := by
      rw [show (0:ℝ)=∫v in a..x,(0:ℝ) by simp]
      apply intervalIntegral.integral_congr
      intro v hv
      rw [uIcc_of_le hx.1] at hv
      calc
        _ = f v/((-S.nu u v)*S.r u v) := by dsimp [f]; ring
        _ = 0 := by rw [hfzero ⟨hv.1,hv.2.trans hx.2⟩]; simp
    rw [hi] at hr
    exact (sub_eq_zero.mp hr).symm
  refine ⟨hI0,hconst,?_⟩
  rw [hI0,add_zero]
  have heq : (1-S.mu u b)/(2*(-S.nu u b))=(1-S.mu u a)/(2*(-S.nu u a)) := by
    have h := hconst ⟨hab.le,le_rfl⟩
    convert congrArg (fun y=>y/2) h using 1 <;> ring
  rw [heq,sub_self]

end EmcsfAcExtension.Global.Annulus
