module

public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Defs.Interaction
public import EmcsfAcExtension.Global.Defs.Stages
public import EmcsfAcExtension.Global.Defs.Domains
public import EmcsfAcExtension.Global.Interaction.ClosuresScalar
import EmcsfAcExtension.Global.Closure.Profiles
import EmcsfAcExtension.Global.Closure.Optics
import EmcsfAcExtension.Global.Interaction.ClosuresProfiles
import EmcsfAcExtension.Global.Interaction.WrappersSource
import EmcsfAcExtension.Global.Interaction.RadialY
import EmcsfAcExtension.Global.Terminal.Mass
import EmcsfAcExtension.Global.Calculus.Sections
import EmcsfAcExtension.Local.Calculus.Sections
import EmcsfAcExtension.Local.Calculus.Reconstruction
import EmcsfAcExtension.Local.Calculus.RelativeCharge
import Mathlib.Tactic

/-! # Exact charge and radial reconstruction on a finite stopped exterior

The canonical background and charge profile are derived from stopped data.
The boundary mass smallness is the preceding stopped-budget conclusion.
Source: `charged_SF_new_version.tex:L4023–L4026`, `L4054–L4060`.
-/

public section

open Set MeasureTheory Complex Filter Topology
open scoped ENNReal

namespace EmcsfAcExtension.Global.Closure

private theorem charge_increment_for_closure {e M₀ F : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) (hM : 0 ≤ M₀) (_hF : 0 ≤ F)
    (hphi : ∀ v ∈ Icc a b, ‖S.phi u v‖ ≤ M₀)
    (hy : ∀ v ∈ Icc a b, ‖S.theta u v / S.lam u v‖ ≤ F) :
    |S.Q u b - S.Q u a| ≤ |e| * M₀ * F * (S.r u b ^ 2 - S.r u a ^ 2) / 2 := by
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have hr (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.r u v :=
    hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
  have hl (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.lam u v := hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)
  have form := (hS.eq_out u a b hua hab hs).2.2.2.1
  have im := (cl.mul cr).intervalIntegrable_of_Icc hab (μ := volume)
  have hp (v : ℝ) (hv : v ∈ Icc a b) : ‖S.QV e u v‖ ≤ |e| * M₀ * F * (S.lam u v * S.r u v) := by
    have ht : ‖S.theta u v‖ ≤ S.lam u v * F := by
      have hh := hy v hv
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hl v hv)] at hh
      simpa only [mul_comm] using (div_le_iff₀ (hl v hv)).mp hh
    simp only [Fields.QV, Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos (hr v hv)]
    calc
      _ ≤ |e| * S.r u v * (‖S.phi u v‖ * ‖S.theta u v‖) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (abs_nonneg _) (hr v hv).le)
        simpa only [norm_mul, Complex.norm_conj] using
          Complex.abs_im_le_norm (starRingEnd ℂ (S.phi u v) * S.theta u v)
      _ ≤ |e| * S.r u v * (M₀ * (S.lam u v * F)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (hphi v hv) ht (norm_nonneg _) hM)
          (mul_nonneg (abs_nonneg _) (hr v hv).le)
      _ = _ := by ring
  have hi := intervalIntegral.integral_mono_on hab form.1.norm
    (im.const_mul (|e| * M₀ * F)) hp
  rw [intervalIntegral.integral_const_mul] at hi
  dsimp only [Pi.mul_apply] at hi
  have hdr (v : ℝ) (hv : v ∈ Ioo a b) : HasDerivAt (S.r u) (S.lam u v) v := by
    apply Local.hasDerivAt_of_integralForm_interior hv (cl.mono Ioo_subset_Icc_self)
    intro c d hac hcd hdb
    exact (hS.eq_out u c d (hua.trans hac) hcd (fun p hp =>
      hs ⟨hp.1, hac.le.trans hp.2.1, hp.2.2.trans hdb.le⟩)).1
  have hmom : (∫ v in a..b, S.lam u v * S.r u v) = (S.r u b ^ 2 - S.r u a ^ 2) / 2 := by
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab (cr.pow 2)
      (f' := fun v => 2 * (S.lam u v * S.r u v)) (fun v hv => ?_) (im.const_mul 2)
    · rw [intervalIntegral.integral_const_mul] at heq
      simp only [Pi.pow_apply] at heq
      linarith only [heq]
    · apply ((hdr v hv).pow 2).congr_deriv
      norm_num only [Nat.reduceSub, pow_one, Nat.cast_ofNat]
      ring
  rw [hmom] at hi
  calc
    _ = ‖∫ v in a..b, S.QV e u v‖ := by rw [← form.2, Real.norm_eq_abs]
    _ ≤ _ := (intervalIntegral.norm_integral_le_integral_norm hab).trans hi
    _ = _ := by ring

/-- [node sec:charged-closure#exterior-charge-profile]
The exact Maxwell increment and quadratic exterior charge profile. The
positive coefficient is universal, chosen before the solution, coupling,
stops and late entry. The boundary mass bound is the preceding stopped
budget smallness; no scalar or charge profile is assumed.
Source: charged_SF_new_version.tex:L4023–L4026. -/
theorem exterior_charge_profile :
    ∃ C > 0, ∀ (ui e : ℝ) (S : Fields),
      OriginalData ui e S → SignedTerminalBound ui S → ∀ Jstop : ℝ,
      ∃ a ∈ Ioo ui 0, ∀ (u₀ u₁ v₀ R₀ δ c Λ F ε ρ : ℝ)
        (vb : ℝ → ℝ) (N : ℕ) (_B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N),
        a ≤ u₀ → ExteriorBox δ c Λ F ε ρ →
        ExteriorStops S (exteriorDomain ui u₀ u₁ vb) δ c Λ F ε →
        S.r u₀ 0 = R₀ → (∀ u ∈ Icc u₀ u₁, R₀ / 2 ≤ S.r u 0) →
        (interactionNorm e S (exteriorDomain ui u₀ u₁ vb) u₀ v₀).toReal ≤ Jstop →
        (∀ u ∈ Icc u₀ u₁, S.m u (vb u) / S.r u (vb u) ≤ F ^ 2) →
        let M := Interaction.scalarBackground ui R₀ c F Jstop S
        ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc (vb u) 0,
          |S.Q u v| ≤ |S.Q u (vb u)| +
            (|e| * M * F / 2) * (S.r u v ^ 2 - S.r u (vb u) ^ 2) ∧
          |S.Q u v| ≤ C * |e| * M * F * S.r u v ^ 2 := by
  obtain ⟨C, hC, hcharge⟩ := ct_charge_profile
  refine ⟨C, hC, ?_⟩
  intro ui e S h hs Jstop
  obtain ⟨a, ha, hcharge⟩ := hcharge ui e S h hs Jstop
  refine ⟨a, ha, ?_⟩
  intro u₀ u₁ v₀ R₀ δ c Λ F ε ρ vb N B hau hbox hstop hR₀ hhalf hJ hmass
  dsimp only
  have d := stopped_profile_data h B hbox hstop hR₀ hhalf hJ
  let M := Interaction.scalarBackground ui R₀ c F Jstop S
  intro u hu v hv
  have hrow := d.exterior_segment hu hv
  have hphi (x : ℝ) (hx : x ∈ Icc (vb u) v) : ‖S.phi u x‖ ≤ M :=
    ct_m0 h d (u, x) (d.row_mem hu ⟨hx.1, hx.2.trans hv.2⟩)
  have hy (x : ℝ) (hx : x ∈ Icc (vb u) v) :
      ‖S.theta u x / S.lam u x‖ ≤ F := (hstop (u, x) (hrow ⟨rfl, hx⟩)).2.2.2.2.1
  have hinc := charge_increment_for_closure h.solution (B.off_axis u hu) hv.1
    (fun p hp => (hrow hp).1) (zero_le_one.trans (d.one_le_background h hu))
    hbox.2.2.2.2.1 hphi hy
  have hQ := hcharge u₀ u₁ v₀ R₀ δ c Λ F ε vb _ (fun _ => F ^ 2)
    hau d (fun u hu => ⟨hmass u hu, le_rfl⟩) u hu v hv
  have hr := h.solution.r_pos (u, v) (d.row_mem hu hv).1
    ((B.off_axis u hu).trans_le hv.1)
  refine ⟨?_, (div_le_iff₀ (sq_pos_of_pos hr)).mp (hQ.1.trans hQ.2)⟩
  have htri : |S.Q u v| ≤ |S.Q u (vb u)| + |S.Q u v - S.Q u (vb u)| := by
    simpa only [Real.norm_eq_abs] using norm_le_norm_add_norm_sub' (S.Q u v) (S.Q u (vb u))
  have hinc' : |S.Q u v - S.Q u (vb u)| ≤
      (|e| * M * F / 2) * (S.r u v ^ 2 - S.r u (vb u) ^ 2) := by
    convert hinc using 1; ring
  exact htri.trans (add_le_add le_rfl hinc')

/-- [node sec:charged-closure#radial-reconstruction]
Pointwise scalar reconstruction and ordinary mass reconstruction, with the
source radial supremum and electric remainder. The positive coefficient
is universal before the development, stopping parameters, shrinking scales
and finite construction. `J` is the actual incoming envelope norm and `M`
the canonical stopped background. Source: charged_SF_new_version.tex:L4054–L4060. -/
theorem radial_reconstruction :
    ∃ C > 0, ∀ (ui e : ℝ) (S : Fields),
      OriginalData ui e S → SignedTerminalBound ui S → ∀ Jstop : ℝ,
      ∃ a ∈ Ioo ui 0, ∀ (u₀ u₁ v₀ R₀ δ c Λ F ε ρ : ℝ)
        (vb : ℝ → ℝ) (N : ℕ) (_B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N),
        a ≤ u₀ → ExteriorBox δ c Λ F ε ρ →
        ExteriorStops S (exteriorDomain ui u₀ u₁ vb) δ c Λ F ε →
        S.r u₀ 0 = R₀ → (∀ u ∈ Icc u₀ u₁, R₀ / 2 ≤ S.r u 0) →
        (interactionNorm e S (exteriorDomain ui u₀ u₁ vb) u₀ v₀).toReal ≤ Jstop →
        (∀ u ∈ Icc u₀ u₁, S.m u (vb u) / S.r u (vb u) ≤ F ^ 2) →
        let J := (interactionNorm e S (exteriorDomain ui u₀ u₁ vb) u₀ v₀).toReal
        let z := Local.sigma e (Interaction.scalarBackground ui R₀ c F Jstop S) (2 * R₀)
        ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc (vb u) 0,
          ‖S.theta u v / (S.lam u v : ℂ)‖ ≤
            ‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖ + c⁻¹ * J ∧
          S.mu u v ≤ 2 * S.m u (vb u) / S.r u (vb u) +
            (sSup ((fun x => ‖S.theta u x / (S.lam u x : ℂ)‖) '' Icc (vb u) v)) ^ 2 +
              C * z := by
  obtain ⟨Cm, hCm, hmass⟩ := InteractionEstimate.radial_mass_reconstruction_of_stopped
  refine ⟨2 * Cm, by positivity, ?_⟩
  intro ui e S h hs Jstop
  obtain ⟨a, ha, hmass⟩ := hmass ui e S h hs Jstop
  refine ⟨a, ha, ?_⟩
  intro u₀ u₁ v₀ R₀ δ c Λ F ε ρ vb N B hau hbox hstop hR₀ hhalf hJ hmb
  dsimp only
  have d := stopped_profile_data h B hbox hstop hR₀ hhalf hJ
  have hm := hmass u₀ u₁ v₀ R₀ δ c Λ F ε vb _ (fun _ => F ^ 2) hau d
    (fun u hu => ⟨hmb u hu, le_rfl⟩)
  intro u hu v hv
  refine ⟨stopped_scalar_reconstruction h B hbox.2.2.1 hbox.2.2.2.2.1
    hbox.2.2.2.2.2.1.le hstop u hu v hv, ?_⟩
  let y := fun x => ‖S.theta u x / (S.lam u x : ℂ)‖
  let Y := sSup (y '' Icc (vb u) v)
  have hrow := d.exterior_segment hu hv
  have hsrow : outSeg u (vb u) v ⊆ origDomain ui := fun p hp => (hrow hp).1
  have hrb := h.solution.r_pos (u, vb u) (B.mem u hu) (B.off_axis u hu)
  have hrv := h.solution.r_pos (u, v) (d.row_mem hu hv).1 ((B.off_axis u hu).trans_le hv.1)
  have hl (x : ℝ) (hx : x ∈ Icc (vb u) v) := h.solution.lam_pos (u, x) (hsrow ⟨rfl, hx⟩)
  have cl := Calculus.continuousOn_out_section h.solution.cont_lam hsrow
  have ct := Calculus.continuousOn_out_section h.solution.cont_theta hsrow
  have cy : ContinuousOn y (Icc (vb u) v) :=
    (ct.div (continuous_ofReal.comp_continuousOn cl)
      (fun x hx => ofReal_ne_zero.mpr (hl x hx).ne')).norm
  have hY (x : ℝ) (hx : x ∈ Icc (vb u) v) : y x ≤ Y :=
    le_csSup (isCompact_Icc.bddAbove_image cy) ⟨x, hx, rfl⟩
  have hY0 : 0 ≤ Y := (norm_nonneg _).trans (hY (vb u) ⟨le_rfl, hv.1⟩)
  have hI := intervalIntegral.integral_mono_on (μ := volume) hv.1
    ((cl.mul (cy.pow 2)).intervalIntegrable_of_Icc hv.1)
    ((cl.const_mul (Y ^ 2)).intervalIntegrable_of_Icc hv.1) (fun x hx => by
      change S.lam u x * (y x) ^ 2 ≤ Y ^ 2 * S.lam u x
      have hy2 := (sq_le_sq₀ (norm_nonneg _) hY0).mpr (hY x hx)
      nlinarith only [mul_le_mul_of_nonneg_left hy2 (hl x hx).le])
  rw [intervalIntegral.integral_const_mul] at hI
  have hrad := (h.solution.eq_out u (vb u) v (B.off_axis u hu) hv.1
    (fun p hp => (hrow hp).1)).1
  rw [← hrad.2] at hI
  have hbr : S.r u (vb u) ≤ S.r u v := by
    have hn := intervalIntegral.integral_nonneg hv.1 (μ := volume) (fun x hx => (hl x hx).le)
    rw [← hrad.2] at hn
    linarith only [hn]
  have hmnonneg : 0 ≤ S.m u (vb u) :=
    (Terminal.mass_monotonicity h.solution (u, vb u) (B.mem u hu)).1
  have hmr : S.m u (vb u) / S.r u v ≤ S.m u (vb u) / S.r u (vb u) :=
    div_le_div_of_nonneg_left hmnonneg hrb hbr
  have hrR : S.r u v ≤ R₀ := by
    have hrow0 := d.exterior_segment hu ⟨(d.rows u hu).2.2.1, le_rfl⟩
    exact ((InteractionEstimate.outgoing_radius_calculus h.solution (B.off_axis u hu).le
      (d.rows u hu).2.2.1 (fun p hp => (hrow0 hp).1)).2.monotoneOn hv
      ⟨(d.rows u hu).2.2.1, le_rfl⟩ hv.2).trans (d.annulus u hu).2
  have hF2 : F ^ 2 ≤ 1 := by
    nlinarith only [hbox.2.2.2.2.1, hbox.2.2.2.2.2.1, sq_nonneg (F - 1)]
  have hR2 : S.r u v ^ 2 ≤ R₀ ^ 2 := pow_le_pow_left₀ hrv.le hrR 2
  have hFR : F ^ 2 * S.r u v ^ 2 ≤ R₀ ^ 2 :=
    (mul_le_mul_of_nonneg_right hF2 (sq_nonneg _)).trans (by simpa using hR2)
  have hmass' : S.m u v ≤ S.m u (vb u) + (1 / 2) * Y ^ 2 * S.r u v +
      Cm * e ^ 2 * (Interaction.scalarBackground ui R₀ c F Jstop S) ^ 2 *
        F ^ 2 * S.r u v ^ 3 := by
    have hI' : (∫ x in vb u..v, S.lam u x * y x ^ 2) ≤ Y ^ 2 * S.r u v := by
      exact hI.trans (mul_le_mul_of_nonneg_left (sub_le_self _ hrb.le) (sq_nonneg _))
    have hh := hm u hu v hv
    change S.m u v ≤ S.m u (vb u) + (1 / 2) *
      (∫ x in vb u..v, S.lam u x * y x ^ 2) + _ at hh
    linarith only [hh, hI']
  have hdiv := (div_le_div_of_nonneg_right hmass' hrv.le)
  have heq : (S.m u (vb u) + (1 / 2) * Y ^ 2 * S.r u v +
      Cm * e ^ 2 * (Interaction.scalarBackground ui R₀ c F Jstop S) ^ 2 *
        F ^ 2 * S.r u v ^ 3) / S.r u v =
      S.m u (vb u) / S.r u v + Y ^ 2 / 2 +
        Cm * e ^ 2 * (Interaction.scalarBackground ui R₀ c F Jstop S) ^ 2 *
          (F ^ 2 * S.r u v ^ 2) := by field_simp [hrv.ne']
  rw [heq] at hdiv
  have helectric := mul_le_mul_of_nonneg_left hFR
    (show 0 ≤ Cm * e ^ 2 * (Interaction.scalarBackground ui R₀ c F Jstop S) ^ 2 by positivity)
  change 2 * S.m u v / S.r u v ≤ 2 * S.m u (vb u) / S.r u (vb u) + Y ^ 2 +
    (2 * Cm) * Local.sigma e (Interaction.scalarBackground ui R₀ c F Jstop S) (2 * R₀)
  simp only [Local.sigma, mul_div_cancel_left₀ R₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have hsum := add_le_add (add_le_add hmr (le_rfl : Y ^ 2 / 2 ≤ Y ^ 2 / 2)) helectric
  have htwo := mul_le_mul_of_nonneg_left (hdiv.trans hsum)
    (by norm_num : (0 : ℝ) ≤ 2)
  convert htwo using 1 <;> ring

end EmcsfAcExtension.Global.Closure
