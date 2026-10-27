/- Copyright (c) 2026. All rights reserved. -/

module

public import EmcsfAcExtension.Frozen.IsSolution
public import EmcsfAcExtension.Global.Defs.Stages
public import EmcsfAcExtension.Global.Interaction.PairSource
public import EmcsfAcExtension.Global.Interaction.PairKernel
import EmcsfAcExtension.Global.Calculus.Sections
import EmcsfAcExtension.Global.Renormalized.Radial
import Mathlib.Tactic

/-!
# Boundary budget kernels

The actual boundary scalar/boundary curvature source at
`charged_SF_new_version.tex:L3665–L3672` is integrated with its damping-power kernel
before applying the weighted boundary budget. The estimate covers complete
stages, including assigned connectors, with coefficients fixed before data.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Global.InteractionEstimate

/-- [internal]
The elementary quadratic majorant for the boundary product. The coefficient
is one, uniformly for every nonnegative incoming amplitude and mass ratio,
provided the outgoing amplitude is at most one. -/
theorem boundary_product_le_quadratic {y z μ : ℝ}
    (hy : 0 ≤ y) (hy1 : y ≤ 1) (hz : 0 ≤ z) :
    y * (μ + y * z) ≤ y ^ 2 + z ^ 2 + μ ^ 2 := by
  have hfirst : y * μ ≤ (y ^ 2 + μ ^ 2) / 2 := by
    nlinarith [sq_nonneg (y - μ)]
  have hsecond : y ^ 2 * z ≤ (y ^ 2 + z ^ 2) / 2 := by
    have hyz : y * z ≤ (y ^ 2 + z ^ 2) / 2 := by
      nlinarith [sq_nonneg (y - z)]
    have hyy : y ^ 2 * z ≤ y * z := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hy1) (mul_nonneg hy hz)]
    exact hyy.trans hyz
  nlinarith [sq_nonneg μ, sq_nonneg z]

/-- [internal]
The actual complex boundary amplitudes, mass ratio, and weighted incoming
clock are continuous on the construction interval. -/
theorem continuousOn_boundary_traces
    {e ui u₀ u₁ v₀ ρ : ℝ} {S : Fields} {vb : ℝ → ℝ} {N : ℕ}
    (hS : IsSolution e S (origDomain ui))
    (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) :
    ContinuousOn (fun u => ‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖)
        (Icc u₀ u₁) ∧
      ContinuousOn (fun u => ‖S.xi u (vb u) / (S.nu u (vb u) : ℂ)‖)
        (Icc u₀ u₁) ∧
      ContinuousOn (fun u => S.mu u (vb u)) (Icc u₀ u₁) ∧
      ContinuousOn (fun u => -S.nu u (vb u) / S.r u (vb u)) (Icc u₀ u₁) := by
  have hp : ContinuousOn (fun u => (u, vb u)) (Icc u₀ u₁) :=
    continuousOn_id.prodMk B.cont
  have cr := hS.cont_r.comp hp B.mem
  have cm := hS.cont_m.comp hp B.mem
  have cl := hS.cont_lam.comp hp B.mem
  have cn := hS.cont_nu.comp hp B.mem
  have ct := hS.cont_theta.comp hp B.mem
  have cx := hS.cont_xi.comp hp B.mem
  have hr (u : ℝ) (hu : u ∈ Icc u₀ u₁) : S.r u (vb u) ≠ 0 :=
    (hS.r_pos (u, vb u) (B.mem u hu) (B.off_axis u hu)).ne'
  have hl (u : ℝ) (hu : u ∈ Icc u₀ u₁) : (S.lam u (vb u) : ℂ) ≠ 0 := by
    exact_mod_cast (hS.lam_pos (u, vb u) (B.mem u hu)).ne'
  have hn (u : ℝ) (hu : u ∈ Icc u₀ u₁) : (S.nu u (vb u) : ℂ) ≠ 0 := by
    exact_mod_cast (hS.nu_neg (u, vb u) (B.mem u hu)).ne
  exact ⟨(ct.div (Complex.continuous_ofReal.comp_continuousOn cl) hl).norm,
    (cx.div (Complex.continuous_ofReal.comp_continuousOn cn) hn).norm,
    (continuousOn_const.mul cm).div cr hr, cn.neg.div cr hr⟩

/-- [internal]
The boundary/boundary product is bounded by the actual full-stage budget,
with exact coefficient one. It holds on a stage including its connector;
the coefficient is independent of coupling, radius, scale and duration.
This is the final budget step in `charged_SF_new_version.tex:L3668–L3672`; the selected
spacetime source is reconstructed and estimated below. -/
theorem boundary_boundary_kernel_of_budget
    {e ui u₀ u₁ v₀ ρ F : ℝ} {S : Fields} {vb : ℝ → ℝ} {N : ℕ}
    (hS : IsSolution e S (origDomain ui))
    (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) {E : Fin N → ℝ}
    (hE : BoundaryBudgets S ui u₀ u₁ v₀ ρ vb N B E)
    (hF : F ≤ 1)
    (hy : ∀ u ∈ Icc u₀ u₁, ‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖ ≤ F)
    (n : Fin N) :
    (∫ u in (B.cuts n.castSucc)..(B.cuts n.succ),
      ‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖ *
        (S.mu u (vb u) +
          ‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖ *
          ‖S.xi u (vb u) / (S.nu u (vb u) : ℂ)‖) *
        (-S.nu u (vb u)) / S.r u (vb u)) ≤ E n := by
  have hstage : B.cuts n.castSucc ≤ B.cuts n.succ :=
    (B.split n).1.trans (B.split n).2
  have hsub : Icc (B.cuts n.castSucc) (B.cuts n.succ) ⊆ Icc u₀ u₁ := by
    intro u hu
    constructor
    · rw [← B.first]
      exact (B.ordered (Fin.zero_le _)).trans hu.1
    · rw [← B.last]
      exact hu.2.trans (B.ordered (Fin.le_last _))
  obtain ⟨cy, cz, cμ, cw⟩ := continuousOn_boundary_traces hS B
  have cprod := (cy.mul (cμ.add (cy.mul cz))).mul cw
  have cquad := ((cy.pow 2).add (cz.pow 2) |>.add (cμ.pow 2)).mul cw
  have hi₁ := (cprod.mono hsub).intervalIntegrable_of_Icc (μ := volume) hstage
  have hi₂ := (cquad.mono hsub).intervalIntegrable_of_Icc (μ := volume) hstage
  have hbound :
      (∫ u in (B.cuts n.castSucc)..(B.cuts n.succ),
        ‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖ *
          (S.mu u (vb u) +
            ‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖ *
            ‖S.xi u (vb u) / (S.nu u (vb u) : ℂ)‖) *
          (-S.nu u (vb u) / S.r u (vb u))) ≤
      ∫ u in (B.cuts n.castSucc)..(B.cuts n.succ),
        (‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖ ^ 2 +
          ‖S.xi u (vb u) / (S.nu u (vb u) : ℂ)‖ ^ 2 + S.mu u (vb u) ^ 2) *
          (-S.nu u (vb u) / S.r u (vb u)) := by
    apply intervalIntegral.integral_mono_on hstage hi₁ hi₂
    intro u hu
    apply mul_le_mul_of_nonneg_right
      (boundary_product_le_quadratic (norm_nonneg _) ((hy u (hsub hu)).trans hF)
        (norm_nonneg _))
    exact div_nonneg (neg_pos.mpr (hS.nu_neg (u, vb u) (B.mem u (hsub hu)))).le
      (hS.r_pos (u, vb u) (B.mem u (hsub hu)) (B.off_axis u (hsub hu))).le
  simp only [← mul_div_assoc] at hbound
  exact hbound.trans (hE n).2.2

end EmcsfAcExtension.Global.InteractionEstimate



namespace EmcsfAcExtension.Global.InteractionEstimate

/-- [internal]
The full complex boundary curvature has its quadratic field majorant.
The coefficient is one, uniformly in all fields and physical parameters. -/
theorem curvature_norm_le (S : Fields) (u v : ℝ)
    (hmu : 0 ≤ S.mu u v) (hgap : 0 ≤ 1 - S.mu u v) :
    ‖Local.curv S u v‖ ≤ S.mu u v +
      ‖S.theta u v / S.lam u v‖ * ‖S.xi u v / S.nu u v‖ := by
  rw [Renormalized.curv_eq]
  calc
    _ ≤ ‖(S.mu u v : ℂ)‖ + ‖(1 - S.mu u v : ℝ) *
        (S.theta u v / S.lam u v) * starRingEnd ℂ (S.xi u v / S.nu u v)‖ := by
      simpa only [Complex.ofReal_sub, Complex.ofReal_one] using
        norm_add_le (S.mu u v : ℂ) (((1 - S.mu u v : ℝ) : ℂ) *
          (S.theta u v / S.lam u v) * starRingEnd ℂ (S.xi u v / S.nu u v))
    _ = S.mu u v + (1 - S.mu u v) *
        (‖S.theta u v / S.lam u v‖ * ‖S.xi u v / S.nu u v‖) := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hmu,
        abs_of_nonneg hgap, Complex.norm_conj]
      ring
    _ ≤ _ := by
      have hh : 1 - S.mu u v ≤ 1 := by linarith only [hmu]
      exact add_le_add le_rfl (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hh
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)))

/-- [internal]
Exact outgoing-row cost of the boundary scalar and boundary curvature.
The coefficient `3Λ²/(δc(3-F²-ε))` depends only on the fixed stops,
uniformly in the solution and row. Its boundary product is subsequently
integrated with the actual stage budget.
Source: charged_SF_new_version.tex:L3665–L3672; internal project record `(bb)`. -/
theorem boundary_boundary_row_cost {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b δ c Λ F ε : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D)
    (hδ : 0 < δ) (hc : 0 < c) (hF : 0 ≤ F)
    (hp : 0 < 3 - F ^ 2 - ε)
    (hstop : ∀ v ∈ Icc a b, 0 ≤ S.mu u v ∧ δ ≤ 1 - S.mu u v ∧
      c ≤ S.lam u v ∧ S.lam u v ≤ Λ ∧
      ‖S.theta u v / S.lam u v‖ ≤ F ∧ S.mu u v / (1 - S.mu u v) ≤ ε) :
    (∫⁻ v in Icc a b, ENNReal.ofReal
      ‖curvatureScalarSource S u v (radialYBoundary S u a v)
        (radialCurvatureBoundary S u a v)‖) ≤
      ENNReal.ofReal ((3 * Λ ^ 2 / (δ * c * (3 - F ^ 2 - ε))) *
        (‖S.theta u a / S.lam u a‖ *
          (S.mu u a + ‖S.theta u a / S.lam u a‖ * ‖S.xi u a / S.nu u a‖) *
          (-S.nu u a) / S.r u a)) := by
  let p := 1 - F ^ 2
  let M := S.mu u a + ‖S.theta u a / S.lam u a‖ * ‖S.xi u a / S.nu u a‖
  let A := 3 * Λ ^ 2 / δ * S.r u a * ‖S.theta u a / S.lam u a‖ * M
  have hr (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.r u v :=
    hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
  have hM : 0 ≤ M := add_nonneg (hstop a ⟨le_rfl, hab⟩).1 (by positivity)
  have hra := hr a ⟨le_rfl, hab⟩
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hpoint (v : ℝ) (hv : v ∈ Icc a b) :
      ‖curvatureScalarSource S u v (radialYBoundary S u a v)
        (radialCurvatureBoundary S u a v)‖ ≤
        A * (((-S.nu u v) / S.r u v ^ 3) * (S.r u a / S.r u v) ^ p) := by
    have hst := hstop v hv
    have hrv := hr v hv
    have hni := (hS.nu_neg (u, v) (hs ⟨rfl, hv⟩)).le
    have hn0 := neg_nonneg.mpr hni
    have hl := (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)).le
    have hY := (ct_y_split hS hua hv.1
      (fun z hz => hs ⟨hz.1, hz.2.1, hz.2.2.trans hv.2⟩) hF
      (fun x hx => (hstop x ⟨hx.1, hx.2.trans hv.2⟩).2.2.2.2.1)).1
    have hC : ‖radialCurvatureBoundary S u a v‖ ≤ (S.r u a / S.r u v) * M := by
      rw [radialCurvatureBoundary, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (div_pos (hr a ⟨le_rfl, hab⟩) (hr v hv))]
      exact mul_le_mul_of_nonneg_left
        (curvature_norm_le S u a (hstop a ⟨le_rfl, hab⟩).1
          (hS.one_sub_mu_pos (u, a) (hs ⟨rfl, le_rfl, hab⟩)).le) (by positivity)
    have hy0 : 0 ≤ ‖S.theta u a / S.lam u a‖ * (S.r u a / S.r u v) ^ p := by positivity
    calc
      _ ≤ (3 * Λ ^ 2 * (‖S.theta u a / S.lam u a‖ * (S.r u a / S.r u v) ^ p) / δ) *
          ((-S.nu u v) / S.r u v ^ 2) * ‖radialCurvatureBoundary S u a v‖ :=
        curvature_scalar_source_le S u v δ Λ _ _ _ hδ (hr v hv) hni hl hst.2.2.2.1
          hst.2.1 hY
      _ ≤ (3 * Λ ^ 2 * (‖S.theta u a / S.lam u a‖ * (S.r u a / S.r u v) ^ p) / δ) *
          ((-S.nu u v) / S.r u v ^ 2) * ((S.r u a / S.r u v) * M) :=
        mul_le_mul_of_nonneg_left hC (by positivity)
      _ = _ := by dsimp [A]; ring
  calc
    _ ≤ ∫⁻ v in Icc a b, ENNReal.ofReal A *
        ENNReal.ofReal (((-S.nu u v) / S.r u v ^ 3) * (S.r u a / S.r u v) ^ p) := by
      apply setLIntegral_mono' measurableSet_Icc
      intro v hv
      rw [← ENNReal.ofReal_mul hA]
      exact ENNReal.ofReal_le_ofReal (hpoint v hv)
    _ = ENNReal.ofReal A * ∫⁻ v in Icc a b,
        ENNReal.ofReal (((-S.nu u v) / S.r u v ^ 3) * (S.r u a / S.r u v) ^ p) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal A *
        ENNReal.ofReal ((-S.nu u a) / (c * (2 + p - ε) * S.r u a ^ 2)) := by
      gcongr
      exact outgoing_inverse_cube_power_kernel hS hua hab hs hc
        (by dsimp [p]; linarith only [hp])
        (fun v hv => (hstop v hv).2.2.1) (fun v hv => (hstop v hv).2.2.2.2.2)
    _ = _ := by
      rw [← ENNReal.ofReal_mul hA]
      congr 1
      dsimp [A, M, p]
      have hden : 2 + (1 - F ^ 2) - ε = 3 - F ^ 2 - ε := by ring
      rw [hden]
      field_simp [hδ.ne', hc.ne', hp.ne', (hr a ⟨le_rfl, hab⟩).ne']

end EmcsfAcExtension.Global.InteractionEstimate

namespace EmcsfAcExtension.Global.InteractionEstimate

/-- [node prop:ct-interaction#boundary-boundary-source]
Spacetime cost of the actual boundary scalar/boundary curvature source on
a full stage, including its connector. The positive coefficient depends
only on `δ,c,Λ,F,ε`, before all physical data, budgets, stage count, radii,
and durations. The actual weighted boundary budget discharges the time
integral; no stage duration or inverse stage energy occurs.
Source: charged_SF_new_version.tex:L3665–L3672; internal project record `(bb)`. -/
theorem boundary_boundary_source (δ c Λ F ε : ℝ)
    (hδ : 0 < δ) (hc : 0 < c) (hcΛ : c ≤ Λ) (hF : 0 ≤ F) (hF1 : F ≤ 1)
    (hp : 0 < 3 - F ^ 2 - ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (e ui u₀ u₁ v₀ ρ : ℝ) (S : Fields) (vb : ℝ → ℝ)
      (N : ℕ) (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) (E : Fin N → ℝ),
      IsSolution e S (origDomain ui) → BoundaryBudgets S ui u₀ u₁ v₀ ρ vb N B E →
      ExteriorStops S (exteriorDomain ui u₀ u₁ vb) δ c Λ F ε → ∀ n : Fin N,
      (∫⁻ u in Icc (B.cuts n.castSucc) (B.cuts n.succ), ∫⁻ v in Icc (vb u) 0,
        ENNReal.ofReal ‖curvatureScalarSource S u v (radialYBoundary S u (vb u) v)
          (radialCurvatureBoundary S u (vb u) v)‖) ≤ ENNReal.ofReal (C * E n) := by
  let K := 3 * Λ ^ 2 / (δ * c * (3 - F ^ 2 - ε))
  have hΛ := hc.trans_le hcΛ
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro e ui u₀ u₁ v₀ ρ S vb N B E hS hE hstop n
  have hstage : B.cuts n.castSucc ≤ B.cuts n.succ :=
    (B.split n).1.trans (B.split n).2
  have hsub : Icc (B.cuts n.castSucc) (B.cuts n.succ) ⊆ Icc u₀ u₁ := by
    intro u hu
    constructor
    · rw [← B.first]
      exact (B.ordered (Fin.zero_le _)).trans hu.1
    · rw [← B.last]
      exact hu.2.trans (B.ordered (Fin.le_last _))
  have hrow (u : ℝ) (hu : u ∈ Icc u₀ u₁) : outSeg u (vb u) 0 ⊆ origDomain ui := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    dsimp only at hx
    subst x
    exact ⟨(B.mem u hu).1, (B.mem u hu).2.1,
      (B.off_axis u hu).le.trans hv.1, hv.2⟩
  have hst (u : ℝ) (hu : u ∈ Icc u₀ u₁) (v : ℝ) (hv : v ∈ Icc (vb u) 0) :=
    hstop (u, v) ⟨hrow u hu ⟨rfl, hv⟩, hu.1, hu.2, hv.1⟩
  let f := fun u => ‖S.theta u (vb u) / S.lam u (vb u)‖ *
    (S.mu u (vb u) + ‖S.theta u (vb u) / S.lam u (vb u)‖ *
      ‖S.xi u (vb u) / S.nu u (vb u)‖) * (-S.nu u (vb u)) / S.r u (vb u)
  obtain ⟨cy, cz, cμ, cw⟩ := continuousOn_boundary_traces hS B
  have ifull : IntervalIntegrable f volume (B.cuts n.castSucc) (B.cuts n.succ) := by
    simpa only [f, Pi.mul_apply, Pi.add_apply, mul_div_assoc] using!
      (((cy.mul (cμ.add (cy.mul cz))).mul cw).mono hsub).intervalIntegrable_of_Icc
        (μ := volume) hstage
  have hf0 : ∀ u ∈ Icc (B.cuts n.castSucc) (B.cuts n.succ), 0 ≤ f u := by
    intro u hu
    have hui := hsub hu
    have hvb : vb u ≤ 0 := (B.mem u hui).2.2.2
    have hμ := (hst u hui (vb u) ⟨le_rfl, hvb⟩).1
    have hn := neg_pos.mpr (hS.nu_neg (u, vb u) (B.mem u hui))
    have hr := hS.r_pos (u, vb u) (B.mem u hui) (B.off_axis u hui)
    dsimp [f]
    positivity
  calc
    _ ≤ ∫⁻ u in Icc (B.cuts n.castSucc) (B.cuts n.succ), ENNReal.ofReal (K * f u) := by
      apply setLIntegral_mono' measurableSet_Icc
      intro u hu
      have hui := hsub hu
      exact boundary_boundary_row_cost hS (B.off_axis u hui)
        (B.mem u hui).2.2.2 (hrow u hui) hδ hc hF hp (fun v hv =>
          ⟨(hst u hui v hv).1, (hst u hui v hv).2.1, (hst u hui v hv).2.2.1,
            (hst u hui v hv).2.2.2.1, (hst u hui v hv).2.2.2.2.1,
            (hst u hui v hv).2.2.2.2.2.1⟩)
    _ = ENNReal.ofReal K * ∫⁻ u in Icc (B.cuts n.castSucc) (B.cuts n.succ),
        ENNReal.ofReal (f u) := by
      simp_rw [ENNReal.ofReal_mul hK.le]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal K * ENNReal.ofReal (E n) := by
      gcongr
      rw [← ofReal_integral_eq_lintegral_ofReal
        ((intervalIntegrable_iff_integrableOn_Icc_of_le hstage).mp ifull)
        (ae_restrict_of_forall_mem measurableSet_Icc hf0),
        integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hstage]
      apply ENNReal.ofReal_le_ofReal
      exact boundary_boundary_kernel_of_budget hS B hE hF1
        (fun u hu => (hst u hu (vb u) ⟨le_rfl, (B.mem u hu).2.2.2⟩).2.2.2.2.1) n
    _ = _ := (ENNReal.ofReal_mul hK.le).symm

end EmcsfAcExtension.Global.InteractionEstimate

namespace EmcsfAcExtension.Global.InteractionEstimate

/-- [internal] Every complete stage lies inside the finite construction
interval, including the endpoints of its assigned connector. -/
theorem finite_boundary_stage_subset {ui u₀ u₁ v₀ ρ : ℝ} {S : Fields}
    {vb : ℝ → ℝ} {N : ℕ} (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) (n : Fin N) :
    Icc (B.cuts n.castSucc) (B.cuts n.succ) ⊆ Icc u₀ u₁ := by
  intro u hu
  constructor
  · rw [← B.first]
    exact (B.ordered (Fin.zero_le _)).trans hu.1
  · rw [← B.last]
    exact hu.2.trans (B.ordered (Fin.le_last _))

/-- [internal]
The actual quadratic boundary budget controls its nonnegative integral on
any measurable or disconnected portion of a stage, with exact coefficient
one. It is uniform in the stage, solution, and all physical scales. -/
theorem boundary_budget_lintegral {e ui u₀ u₁ v₀ ρ : ℝ} {S : Fields}
    {vb : ℝ → ℝ} {N : ℕ} (hS : IsSolution e S (origDomain ui))
    (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) {E : Fin N → ℝ}
    (hE : BoundaryBudgets S ui u₀ u₁ v₀ ρ vb N B E) (n : Fin N)
    {U : Set ℝ} (hsub : U ⊆ Icc (B.cuts n.castSucc) (B.cuts n.succ)) :
    (∫⁻ u in U, ENNReal.ofReal
      ((‖S.theta u (vb u) / S.lam u (vb u)‖ ^ 2 +
        ‖S.xi u (vb u) / S.nu u (vb u)‖ ^ 2 + S.mu u (vb u) ^ 2) *
        (-S.nu u (vb u)) / S.r u (vb u))) ≤ ENNReal.ofReal (E n) := by
  have hab := (B.split n).1.trans (B.split n).2
  obtain ⟨cy, cz, cμ, cw⟩ := continuousOn_boundary_traces hS B
  have ci := (((cy.pow 2).add (cz.pow 2)).add (cμ.pow 2)).mul cw
  have ii := (ci.mono (finite_boundary_stage_subset B n)).intervalIntegrable_of_Icc
    (μ := volume) hab
  let f := fun u => (‖S.theta u (vb u) / S.lam u (vb u)‖ ^ 2 +
    ‖S.xi u (vb u) / S.nu u (vb u)‖ ^ 2 + S.mu u (vb u) ^ 2) *
      (-S.nu u (vb u)) / S.r u (vb u)
  have if' : IntervalIntegrable f volume (B.cuts n.castSucc) (B.cuts n.succ) := by
    simpa only [f, Pi.mul_apply, Pi.add_apply, Pi.pow_apply, mul_div_assoc] using! ii
  have hf0 : ∀ u ∈ Icc (B.cuts n.castSucc) (B.cuts n.succ), 0 ≤ f u := by
    intro u hu
    have hui := finite_boundary_stage_subset B n hu
    have hn := (neg_pos.mpr (hS.nu_neg (u, vb u) (B.mem u hui))).le
    have hr := (hS.r_pos (u, vb u) (B.mem u hui) (B.off_axis u hui)).le
    dsimp only [f]
    positivity
  calc
    _ ≤ ∫⁻ u in Icc (B.cuts n.castSucc) (B.cuts n.succ), ENNReal.ofReal (f u) :=
      lintegral_mono_set hsub
    _ = ENNReal.ofReal (∫ u in (B.cuts n.castSucc)..(B.cuts n.succ), f u) := by
      rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
        ofReal_integral_eq_lintegral_ofReal
          ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp if')
          (ae_restrict_of_forall_mem measurableSet_Icc hf0)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hE n).2.2

end EmcsfAcExtension.Global.InteractionEstimate
