module

public import EmcsfAcExtension.Frozen.IsSolution
public import EmcsfAcExtension.Global.Closure.Continuation
public import EmcsfAcExtension.Global.Closure.Profiles
public import EmcsfAcExtension.Global.Closure.Absorption
public import EmcsfAcExtension.Global.Closure.Parameters
import EmcsfAcExtension.Global.Interaction.NEstimateOptics
import EmcsfAcExtension.Global.Closure.Entry
import EmcsfAcExtension.Global.Interaction.WrappersSource
import EmcsfAcExtension.Global.Interaction.PairTonelli
import EmcsfAcExtension.Global.Interaction.OutgoingOptics
import EmcsfAcExtension.Global.Interaction.BoundaryChain
import EmcsfAcExtension.Global.Terminal.OpticalUpper
import EmcsfAcExtension.Global.Terminal.Flux
import EmcsfAcExtension.Global.Api.Integrals
import Mathlib.Tactic

/-! # Strict optical improvements

The positive incoming exponent bounds the signed one. An exponent strictly
below `log 2` preserves the entry expansion margin `2c`; the outgoing
logarithmic estimate compares terminal and boundary clocks with factor `2`.
Source: `charged_SF_new_version.tex:L4062–L4072`.
-/

public section

open Set MeasureTheory
open Filter Topology
open scoped ENNReal

namespace EmcsfAcExtension.Global.Closure

/-- [internal]
The incoming expansion margin from the positive optical estimate.
The closure consumer obtains `hopt` from interaction on the actual stopped
history after substituting the produced profiles and budget sums. The
factor `2` is universal and does not depend on stage duration or scale. -/
theorem expansion_improvement_of_estimates {e c : ℝ} {S : Fields}
    {D : Set (ℝ × ℝ)} (hS : IsSolution e S D) {a b v : ℝ}
    (hab : a ≤ b) (hbv : b < v) (hs : inSeg a b v ⊆ D)
    (_hc : 0 < c) (hentry : 2 * c ≤ S.lam a v)
    (hq : ∀ u ∈ Icc a b, S.Q u v ^ 2 / S.r u v ^ 2 ≤ S.mu u v)
    (hopt : (∫ u in a..b, positiveExpIntegrand S u v) < Real.log 2) :
    0 ≤ (∫ u in a..b, signedExpIntegrand S u v) ∧
      (∫ u in a..b, signedExpIntegrand S u v) ≤
        (∫ u in a..b, positiveExpIntegrand S u v) ∧
      c < S.lam b v := by
  have hpoint (u : ℝ) (hu : u ∈ Icc a b) := signed_exponent_bounds
    (hS.r_pos (u, v) (hs ⟨hu.1, hu.2, rfl⟩) (hu.2.trans_lt hbv))
    (hS.nu_neg (u, v) (hs ⟨hu.1, hu.2, rfl⟩))
    (hS.one_sub_mu_pos (u, v) (hs ⟨hu.1, hu.2, rfl⟩)) (hq u hu)
  have hcont := Terminal.incoming_integrands_continuousOn hS hbv hs
  have hnonneg := intervalIntegral.integral_nonneg (μ := volume) hab (fun u hu => (hpoint u hu).1)
  have hle := intervalIntegral.integral_mono_on (μ := volume) hab
    (hcont.1.intervalIntegrable_of_Icc hab) (hcont.2.1.intervalIntegrable_of_Icc hab)
    (fun u hu => (hpoint u hu).2)
  refine ⟨hnonneg, hle, ?_⟩
  have hlog := (Terminal.incoming_log_lambda_integralForm hS hab hbv hs).2
  have hla := hS.lam_pos (a, v) (hs ⟨le_rfl, hab, rfl⟩)
  have hlb := hS.lam_pos (b, v) (hs ⟨hab, le_rfl, rfl⟩)
  have hr : S.lam a v / S.lam b v < 2 := by
    apply (Real.log_lt_log_iff (div_pos hla hlb) (by norm_num)).mp
    rw [Real.log_div hla.ne' hlb.ne']
    rw [intervalIntegral.integral_neg] at hlog
    linarith only [hlog, hle.trans_lt hopt]
  have hh := (div_lt_iff₀ hlb).mp hr
  linarith only [hh, hentry]

/-- [internal]
Radial reconstruction with the actual finite incoming norm. The coefficient
is exactly `c⁻¹`, uniform in all radii and finite cutoffs. The common label
envelope is constructed from the initial density and source history.
Source: charged_SF_new_version.tex:L4056–L4060. -/
theorem stopped_scalar_reconstruction {ui e a b v₀ ρ δ c Λ F ε : ℝ} {S : Fields}
    (h : OriginalData ui e S) {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui a b v₀ ρ vb N) (hc : 0 < c)
    (hF : 0 ≤ F) (hF1 : F ≤ 1)
    (hstop : ExteriorStops S (exteriorDomain ui a b vb) δ c Λ F ε) :
    ∀ u ∈ Icc a b, ∀ v ∈ Icc (vb u) 0,
      ‖S.theta u v / (S.lam u v : ℂ)‖ ≤ ‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖ +
        c⁻¹ * (interactionNorm e S (exteriorDomain ui a b vb) a v₀).toReal := by
  obtain ⟨_, hg, hg0, hmajor, hint, _⟩ := incoming_envelope h B
  let g := fun v => (incomingEnvelope e S (exteriorDomain ui a b vb) a v).toReal
  intro u hu v hv
  have hv₀ := InteractionEstimate.finite_boundary_label_bounds B u hu
  have hsub : Icc (vb u) v ⊆ Icc v₀ 0 := Icc_subset_Icc hv₀.1 hv.2
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hv.1).mpr (hg.mono_set hsub)
  have hraw : ∀ᵐ w ∂volume.restrict (Icc (vb u) v), ‖weightedJ S u w‖ ≤ g w := by
    filter_upwards [hmajor.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)),
      ae_restrict_mem measurableSet_Icc] with w hw hwm
    exact (hw u hu hwm.1).2
  have hrow : outSeg u (vb u) v ⊆ origDomain ui := by
    intro p hp
    exact (InteractionEstimate.finite_boundary_row B u hu
      ⟨hp.1, hp.2.1, hp.2.2.trans hv.2⟩).1
  have hy := InteractionEstimate.outgoing_scalar_pointwise h.solution (B.off_axis u hu) hv.1
    hrow hc hF hF1
    (fun w hw => (hstop (u, w) (InteractionEstimate.finite_boundary_row B u hu
      ⟨rfl, hw.1, hw.2.trans hv.2⟩)).2.2.1)
    (fun w hw => (hstop (u, w) (InteractionEstimate.finite_boundary_row B u hu
      ⟨rfl, hw.1, hw.2.trans hv.2⟩)).2.2.2.2.1) g hi hraw
  have hv00 : v₀ ≤ 0 := hv₀.1.trans hv₀.2
  have hwhole := (intervalIntegrable_iff_integrableOn_Icc_of_le hv00).mpr hg
  have hleft := intervalIntegral.integral_mono_interval hv₀.1 hv.1 hv.2
    (Filter.Eventually.of_forall hg0) hwhole
  apply hy.2.trans
  rw [hint] at hleft
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hleft (inv_nonneg.mpr hc.le))

/-- [internal]
Both optical bounds on every sufficiently late finite stopped exterior,
with the actual incoming norm and canonical scalar background. The uniform
coefficient depends only on the fixed box and finite-sum coefficient,
before the development, stopping budget, entry, radii, stages and duration.
The boundary budget and its sum come from the stage construction.
Source: charged_SF_new_version.tex:L4062–L4072. -/
theorem stopped_optics_of_budgets (δ c Λ F ε ρ Csum : ℝ)
    (hbox : ExteriorBox δ c Λ F ε ρ) (hCsum : 0 ≤ Csum) :
    ∃ C > 0, ∀ (ui e : ℝ) (S : Fields),
      OriginalData ui e S → SignedTerminalBound ui S → ∀ Jstop : ℝ,
      ∃ a ∈ Ioo ui 0, ∀ (u₀ u₁ v₀ R₀ εentry Svar : ℝ) (vb en : ℝ → ℝ)
        (N : ℕ) (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) (E : Fin N → ℝ),
        a ≤ u₀ → 0 ≤ εentry →
        ExteriorStops S (exteriorDomain ui u₀ u₁ vb) δ c Λ F ε →
        S.r u₀ 0 = R₀ → (∀ u ∈ Icc u₀ u₁, R₀ / 2 ≤ S.r u 0) →
        (interactionNorm e S (exteriorDomain ui u₀ u₁ vb) u₀ v₀).toReal ≤ Jstop →
        (∀ u ∈ Icc u₀ u₁, S.m u (vb u) / S.r u (vb u) ≤ en u ∧ en u ≤ F ^ 2) →
        BoundaryBudgets S ui u₀ u₁ v₀ ρ vb N B E →
        (∑ n, E n) ≤ Csum * (εentry + Svar ^ 2) →
        let J := (interactionNorm e S (exteriorDomain ui u₀ u₁ vb) u₀ v₀).toReal
        let ζ₂ := Local.sigma e (Interaction.scalarBackground ui R₀ c F Jstop S) (2 * R₀)
        (⨆ v ∈ Icc v₀ 0, ∫⁻ u in {u | (u, v) ∈ exteriorDomain ui u₀ u₁ vb},
          ENNReal.ofReal (positiveExpIntegrand S u v)) ≤
          ENNReal.ofReal (C * (εentry + Svar ^ 2 + J ^ 2 + ζ₂)) ∧
        ∀ u ∈ Icc u₀ u₁,
          Real.log ((-S.nu u 0) / (-S.nu u (vb u))) ≤
            C * (S.m u (vb u) / S.r u (vb u) +
              ‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖ ^ 2 + J ^ 2 + ζ₂) := by
  obtain ⟨Co, hCo, hoptics⟩ := Interaction.source_and_optics_of_stopped δ c Λ F ε ρ hbox
  let C := Co * (Csum + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  have hoC : Co ≤ C := by dsimp [C]; nlinarith only [mul_nonneg hCo.le hCsum]
  have hpC : Co * Csum ≤ C := by dsimp [C]; linarith only [hCo]
  refine ⟨C, hC, ?_⟩
  intro ui e S h hs Jstop
  obtain ⟨a, ha, ho⟩ := hoptics ui e S h hs Jstop
  refine ⟨a, ha, ?_⟩
  intro u₀ u₁ v₀ R₀ εentry Svar vb en N B E hau he hstop hR₀ hR hJ hmass hE hsum
  have d := stopped_profile_data h B hbox hstop hR₀ hR hJ
  obtain ⟨_, _, _, _, hint, _⟩ := incoming_envelope h B
  obtain ⟨_, hi, hout⟩ := ho u₀ u₁ v₀ R₀ vb _ en N B E hau d hmass hE
  rw [hint] at hi hout
  dsimp only
  constructor
  · apply hi.trans
    apply ENNReal.ofReal_le_ofReal
    have hz : 0 ≤ Local.sigma e (Interaction.scalarBackground ui R₀ c F Jstop S) (2 * R₀) := by
      unfold Local.sigma
      positivity
    have h₁ := mul_le_mul_of_nonneg_left hsum hCo.le
    have h₂ := mul_le_mul_of_nonneg_right hpC (add_nonneg he (sq_nonneg Svar))
    have h₃ := mul_le_mul_of_nonneg_right hoC (sq_nonneg
      (interactionNorm e S (exteriorDomain ui u₀ u₁ vb) u₀ v₀).toReal)
    have h₄ := mul_le_mul_of_nonneg_right hoC hz
    linarith only [h₁, h₂, h₃, h₄]
  · intro u hu
    apply (hout u hu).trans
    have hμ := (hstop _ (InteractionEstimate.finite_boundary_row B u hu
      ⟨rfl, le_rfl, (B.mem u hu).2.2.2⟩)).1
    have hm : 0 ≤ S.m u (vb u) / S.r u (vb u) := by
      have heq : S.m u (vb u) / S.r u (vb u) = S.mu u (vb u) / 2 := by
        unfold Fields.mu
        ring
      rw [heq]
      positivity
    apply mul_le_mul_of_nonneg_right hoC
    unfold Local.sigma
    positivity

/-- [internal]
Strict improvement of both scalar and mass stops from the actual finite
incoming norm and field budgets. The positive threshold depends only on
`c,F,ε` and the universal charge reconstruction coefficient, before the
development, stopping budget, entry row, radii and finite construction.
The charge profile is derived at the common late entry. The positive stage
count excludes the singleton entry, controlled separately by entry data.
Source: charged_SF_new_version.tex:L4056–L4061. -/
theorem scalar_mass_improvement_of_budgets (c F ε : ℝ) (hc : 0 < c)
    (hF : 0 < F) (hF1 : F < 1) (hε : 0 < ε) :
    ∃ η > 0, ∀ (ui e : ℝ) (S : Fields),
      OriginalData ui e S → SignedTerminalBound ui S → ∀ Jstop : ℝ,
      ∃ a ∈ Ioo ui 0, ∀ (u₀ u₁ v₀ R₀ δ Λ ρ : ℝ) (vb : ℝ → ℝ)
        (N : ℕ) (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) (E : Fin N → ℝ),
        a ≤ u₀ → 0 < N → ExteriorBox δ c Λ F ε ρ →
        ExteriorStops S (exteriorDomain ui u₀ u₁ vb) δ c Λ F ε →
        S.r u₀ 0 = R₀ → (∀ u ∈ Icc u₀ u₁, R₀ / 2 ≤ S.r u 0) →
        (interactionNorm e S (exteriorDomain ui u₀ u₁ vb) u₀ v₀).toReal ≤ Jstop →
        BoundaryBudgets S ui u₀ u₁ v₀ ρ vb N B E → (∑ n, E n) ≤ η →
        (interactionNorm e S (exteriorDomain ui u₀ u₁ vb) u₀ v₀).toReal ≤ η →
        Local.sigma e (Interaction.scalarBackground ui R₀ c F Jstop S) (2 * R₀) ≤ η →
        ∀ p ∈ exteriorDomain ui u₀ u₁ vb,
          ‖S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ)‖ < F ∧
          S.mu p.1 p.2 / (1 - S.mu p.1 p.2) < ε := by
  obtain ⟨Cm, hCm, hmass⟩ := InteractionEstimate.radial_mass_reconstruction_of_stopped
  let Y := fun t : ℝ => Real.sqrt t + c⁻¹ * t
  let P := fun t : ℝ => 2 * t + (Y t) ^ 2 + 2 * Cm * F ^ 2 * t
  have hY : ContinuousAt Y 0 := by dsimp [Y]; fun_prop
  have hP : ContinuousAt P 0 := by dsimp [P]; fun_prop
  have heps : 0 < ε / (1 + ε) := div_pos hε (by positivity)
  have hy0 : Y 0 < F := by simpa [Y] using hF
  have hp0 : P 0 < ε / (1 + ε) := by simpa [P, Y] using heps
  have ht : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 < t ∧ Y t < F ∧ P t < ε / (1 + ε) ∧ t < F ^ 2 := by
    filter_upwards [self_mem_nhdsWithin,
      (hY.tendsto.mono_left nhdsWithin_le_nhds).eventually (Iio_mem_nhds hy0),
      (hP.tendsto.mono_left nhdsWithin_le_nhds).eventually (Iio_mem_nhds hp0),
      nhdsWithin_le_nhds (Iio_mem_nhds (sq_pos_of_pos hF))] with t hpos hy hp ht
    exact ⟨hpos, hy, hp, ht⟩
  obtain ⟨η, hη, hYη, hPη, hηF⟩ := ht.exists
  refine ⟨η, hη, ?_⟩
  intro ui e S h hs Jstop
  obtain ⟨a, ha, hmass⟩ := hmass ui e S h hs Jstop
  refine ⟨a, ha, ?_⟩
  intro u₀ u₁ v₀ R₀ δ Λ ρ vb N B E hau hN hbox hstop hR₀ hR hJ hE hsum hJη hzη
  have d := stopped_profile_data h B hbox hstop hR₀ hR hJ
  have hb (u : ℝ) (hu : u ∈ Icc u₀ u₁) := boundary_budget_le_sum B hN E hE hu
  have hmnonneg (u : ℝ) (hu : u ∈ Icc u₀ u₁) : 0 ≤ S.m u (vb u) / S.r u (vb u) := by
    have heq : S.m u (vb u) / S.r u (vb u) = S.mu u (vb u) / 2 := by
      unfold Fields.mu
      ring
    rw [heq]
    exact div_nonneg (h.mu _ (B.mem u hu)).1 (by norm_num)
  have hmb (u : ℝ) (hu : u ∈ Icc u₀ u₁) : S.m u (vb u) / S.r u (vb u) ≤ η := by
    have hh := (hb u hu).trans hsum
    linarith only [hh, sq_nonneg (‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖)]
  have hboundary (u : ℝ) (hu : u ∈ Icc u₀ u₁) :
      ‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖ ≤ Real.sqrt η := by
    apply (Real.le_sqrt (norm_nonneg _) hη.le).mpr
    have hh := (hb u hu).trans hsum
    linarith only [hh, hmnonneg u hu]
  have hys (u : ℝ) (hu : u ∈ Icc u₀ u₁) (v : ℝ) (hv : v ∈ Icc (vb u) 0) :
      ‖S.theta u v / (S.lam u v : ℂ)‖ ≤ Y η := by
    apply (stopped_scalar_reconstruction h B hc hF.le hF1.le hstop u hu v hv).trans
    exact add_le_add (hboundary u hu) (mul_le_mul_of_nonneg_left hJη (inv_nonneg.mpr hc.le))
  have hm := hmass u₀ u₁ v₀ R₀ δ c Λ F ε vb _ (fun _ => F ^ 2) hau d
    (fun u hu => ⟨(hmb u hu).trans hηF.le, le_rfl⟩)
  intro p hp
  rcases p with ⟨u, v⟩
  have hu : u ∈ Icc u₀ u₁ := ⟨hp.2.1, hp.2.2.1⟩
  have hv : v ∈ Icc (vb u) 0 := ⟨hp.2.2.2, hp.1.2.2.2⟩
  have hsrow : outSeg u (vb u) v ⊆ origDomain ui :=
    fun p hp => (d.exterior_segment hu hv hp).1
  have hr := h.solution.r_pos _ hp.1 ((B.off_axis u hu).trans_le hv.1)
  have hrb := h.solution.r_pos _ (B.mem u hu) (B.off_axis u hu)
  have hrmono := (InteractionEstimate.outgoing_radius_calculus h.solution
    (B.off_axis u hu).le hv.1 hsrow).2.monotoneOn
  have hbr : S.r u (vb u) ≤ S.r u v := hrmono ⟨le_rfl, hv.1⟩ ⟨hv.1, le_rfl⟩ hv.1
  have hvr : S.r u v ≤ R₀ := by
    have hrow0 : outSeg u (vb u) 0 ⊆ origDomain ui :=
      fun p hp => (d.exterior_segment hu ⟨(d.rows u hu).2.2.1, le_rfl⟩ hp).1
    exact ((InteractionEstimate.outgoing_radius_calculus h.solution (B.off_axis u hu).le
      (d.rows u hu).2.2.1 hrow0).2.monotoneOn hv
      ⟨(d.rows u hu).2.2.1, le_rfl⟩ hv.2).trans (d.annulus u hu).2
  have hmbound : S.m u (vb u) ≤ η * S.r u v :=
    ((div_le_iff₀ hrb).mp (hmb u hu)).trans (mul_le_mul_of_nonneg_left hbr hη.le)
  have cl := Calculus.continuousOn_out_section h.solution.cont_lam hsrow
  have ct := Calculus.continuousOn_out_section h.solution.cont_theta hsrow
  have cy := ct.div (Complex.continuous_ofReal.comp_continuousOn cl)
    (fun x hx => Complex.ofReal_ne_zero.mpr
      (h.solution.lam_pos (u, x) (hsrow ⟨rfl, hx.1, hx.2⟩)).ne')
  have hrad := Interaction.radial_moment h.solution (B.off_axis u hu) hv.1 hsrow 0
  simp only [pow_zero, mul_one, Nat.cast_zero, zero_add, pow_one, div_one] at hrad
  have hI := intervalIntegral.integral_mono_on (μ := volume) hv.1
    ((cl.mul (cy.norm.pow 2)).intervalIntegrable_of_Icc hv.1)
    ((cl.const_mul ((Y η) ^ 2)).intervalIntegrable_of_Icc hv.1) (fun x hx => by
      change S.lam u x * ‖S.theta u x / (S.lam u x : ℂ)‖ ^ 2 ≤ (Y η) ^ 2 * S.lam u x
      have hy := hys u hu x ⟨hx.1, hx.2.trans hv.2⟩
      have hY0 : 0 ≤ Y η := by dsimp [Y]; positivity
      have hh := (sq_le_sq₀ (norm_nonneg _) hY0).mpr hy
      exact (mul_le_mul_of_nonneg_left hh
        (h.solution.lam_pos (u, x) (hsrow ⟨rfl, hx.1, hx.2⟩)).le).trans_eq (mul_comm _ _))
  change (∫ x in vb u..v, S.lam u x * ‖S.theta u x / (S.lam u x : ℂ)‖ ^ 2) ≤
    ∫ x in vb u..v, (Y η) ^ 2 * S.lam u x at hI
  rw [intervalIntegral.integral_const_mul, hrad] at hI
  have hI' : (∫ x in vb u..v, S.lam u x * ‖S.theta u x / S.lam u x‖ ^ 2) ≤
      (Y η) ^ 2 * S.r u v := by
    have hn := mul_nonneg (sq_nonneg (Y η)) hrb.le
    linarith only [hI, hn]
  let z := Local.sigma e (Interaction.scalarBackground ui R₀ c F Jstop S) (2 * R₀)
  have hscale : e ^ 2 * (Interaction.scalarBackground ui R₀ c F Jstop S) ^ 2 * S.r u v ^ 2 ≤ z := by
    dsimp only [z]
    rw [ct_zeta]
    exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ hr.le d.radius_pos.le).mpr hvr) (by positivity)
  have hem := mul_le_mul_of_nonneg_left hscale
    (show 0 ≤ 2 * Cm * F ^ 2 * S.r u v by positivity)
  have hm' := hm u hu v hv
  have hmu : S.mu u v ≤ 2 * η + (Y η) ^ 2 + 2 * Cm * F ^ 2 * z := by
    unfold Fields.mu
    apply (div_le_iff₀ hr).mpr
    linarith only [hm', hI', hmbound, hem]
  have hmuf : S.mu u v < ε / (1 + ε) := by
    have hz := mul_le_mul_of_nonneg_left hzη (show 0 ≤ 2 * Cm * F ^ 2 by positivity)
    have hupper : 2 * η + (Y η) ^ 2 + 2 * Cm * F ^ 2 * z ≤ P η := by
      dsimp only [P]
      linarith only [hz]
    exact hmu.trans_lt (hupper.trans_lt hPη)
  refine ⟨(hys u hu v hv).trans_lt hYη, ?_⟩
  apply (div_lt_iff₀ (h.solution.one_sub_mu_pos _ hp.1)).mpr
  have hh := (lt_div_iff₀ (show 0 < 1 + ε by positivity)).mp hmuf
  linarith only [hh]

/-- [internal]
Every proper incoming segment in a finite exterior is controlled by the
actual supremum of full incoming histories. The label stays in the
exterior at every earlier time by boundary monotonicity. The coefficient
is one; no optical estimate or finiteness premise is hidden in a real value.
-/
theorem incoming_integral_le_optical_bound {ui e a b v₀ ρ E : ℝ} {S : Fields}
    (h : OriginalData ui e S) {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui a b v₀ ρ vb N) (hE : 0 ≤ E)
    (hopt : (⨆ v ∈ Icc v₀ 0, ∫⁻ u in {u | (u, v) ∈ exteriorDomain ui a b vb},
      ENNReal.ofReal (positiveExpIntegrand S u v)) ≤ ENNReal.ofReal E)
    {u v : ℝ} (hu : u ∈ Icc a b) (hv : v ∈ Icc (vb u) 0) :
    (∫ s in a..u, positiveExpIntegrand S s v) ≤ E := by
  have hist (s : ℝ) (hs : s ∈ Icc a u) :
      (s, v) ∈ exteriorDomain ui a b vb := by
    have hs' : s ∈ Icc a b := ⟨hs.1, hs.2.trans hu.2⟩
    exact InteractionEstimate.finite_boundary_row B s hs'
      ⟨rfl, (B.mono hs' hu hs.2).trans hv.1, hv.2⟩
  have hs : inSeg a u v ⊆ origDomain ui := by
    rintro ⟨s, w⟩ ⟨hsa, hsu, rfl⟩
    exact (hist s ⟨hsa, hsu⟩).1
  have huv : u < v := (B.off_axis u hu).trans_le hv.1
  have hc := Terminal.incoming_integrands_continuousOn h.solution huv hs
  have hn (s : ℝ) (hs' : s ∈ Icc a u) : 0 ≤ positiveExpIntegrand S s v := by
    have hp := (hist s hs').1
    exact div_nonneg (mul_nonneg (neg_pos.mpr (h.solution.nu_neg _ hp)).le (h.mu _ hp).1)
      (mul_nonneg (h.solution.one_sub_mu_pos _ hp).le
        (h.solution.r_pos _ hp (hs'.2.trans_lt huv)).le)
  have heq := Interaction.ofReal_interval_integral hu.1 (hc.2.1.intervalIntegrable_of_Icc hu.1) hn
  have hv₀ : v ∈ Icc v₀ 0 :=
    ⟨(InteractionEstimate.finite_boundary_label_bounds B u hu).1.trans hv.1, hv.2⟩
  have hh : ENNReal.ofReal (∫ s in a..u, positiveExpIntegrand S s v) ≤ ENNReal.ofReal E := by
    rw [heq]
    calc
      (∫⁻ s in Icc a u, ENNReal.ofReal (positiveExpIntegrand S s v)) ≤
          ∫⁻ s in {s | (s, v) ∈ exteriorDomain ui a b vb},
            ENNReal.ofReal (positiveExpIntegrand S s v) :=
        lintegral_mono_set (fun s hs => hist s hs)
      _ ≤ (⨆ w ∈ Icc v₀ 0,
          ∫⁻ s in {s | (s, w) ∈ exteriorDomain ui a b vb},
            ENNReal.ofReal (positiveExpIntegrand S s w)) := le_iSup₂_of_le v hv₀ le_rfl
      _ ≤ ENNReal.ofReal E := hopt
  exact (ENNReal.ofReal_le_ofReal_iff hE).mp hh

/-- [internal]
The uniform positive optical bound strictly improves the expansion at
every point of the finite exterior, using its actual entry label. The
uniform exponent is supplied by `stopped_optics_of_budgets`; the entry
margin is supplied by the proper entry family. The factor two is universal.
Source: charged_SF_new_version.tex:L4067–L4072. -/
theorem stopped_expansion_improvement_of_optics {ui e a b v₀ ρ δ c Λ F ε E : ℝ}
    {S : Fields} (h : OriginalData ui e S) {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui a b v₀ ρ vb N) (hc : 0 < c)
    (hstop : ExteriorStops S (exteriorDomain ui a b vb) δ c Λ F ε)
    (hentry : ∀ v ∈ Icc v₀ 0, 2 * c ≤ S.lam a v)
    (hE : 0 ≤ E) (hsmall : E < Real.log 2)
    (hopt : (⨆ v ∈ Icc v₀ 0, ∫⁻ u in {u | (u, v) ∈ exteriorDomain ui a b vb},
      ENNReal.ofReal (positiveExpIntegrand S u v)) ≤ ENNReal.ofReal E) :
    ∀ p ∈ exteriorDomain ui a b vb, c < S.lam p.1 p.2 := by
  rintro ⟨u, v⟩ hp
  have hu : u ∈ Icc a b := ⟨hp.2.1, hp.2.2.1⟩
  have hv : v ∈ Icc (vb u) 0 := ⟨hp.2.2.2, hp.1.2.2.2⟩
  have hist (s : ℝ) (hs : s ∈ Icc a u) :
      (s, v) ∈ exteriorDomain ui a b vb :=
    InteractionEstimate.finite_boundary_row B s ⟨hs.1, hs.2.trans hu.2⟩
      ⟨rfl, (B.mono ⟨hs.1, hs.2.trans hu.2⟩ hu hs.2).trans hv.1, hv.2⟩
  have hseg : inSeg a u v ⊆ origDomain ui := by
    rintro ⟨s, w⟩ ⟨hsa, hsu, rfl⟩
    exact (hist s ⟨hsa, hsu⟩).1
  have hq (s : ℝ) (hs : s ∈ Icc a u) : S.Q s v ^ 2 / S.r s v ^ 2 ≤ S.mu s v := by
    have hh := hstop _ (hist s hs)
    exact hh.2.2.2.2.2.2.trans (by linarith only [hh.1])
  exact (expansion_improvement_of_estimates h.solution hu.1
    ((B.off_axis u hu).trans_le hv.1) hseg hc
    (hentry v ⟨(InteractionEstimate.finite_boundary_label_bounds B u hu).1.trans hv.1, hv.2⟩)
    hq ((incoming_integral_le_optical_bound h B hE hopt hu hv).trans_lt hsmall)).2.2

/-- [internal]
Strict incoming expansion and outgoing clock improvements on every finite
stopped exterior. The actual optical estimates, scalar and charge profiles,
and boundary mass bound are derived from the field budgets. The positive
coefficient depends only on the fixed box, before the development, stopping
budget, entry, finite path and every duration. Only the numerical smallness
of the resulting optical error remains for the entry choice.
Source: charged_SF_new_version.tex:L4062–L4072. -/
theorem expansion_clock_improvement_of_budgets (δ c Λ F ε ρ : ℝ)
    (hbox : ExteriorBox δ c Λ F ε ρ) :
    ∃ C > 0, ∀ (ui e : ℝ) (S : Fields),
      OriginalData ui e S → SignedTerminalBound ui S → ∀ Jstop : ℝ,
      ∃ a ∈ Ioo ui 0, ∀ (u₀ u₁ v₀ R₀ : ℝ) (vb : ℝ → ℝ)
        (N : ℕ) (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) (E : Fin N → ℝ),
        a ≤ u₀ → 0 < N →
        ExteriorStops S (exteriorDomain ui u₀ u₁ vb) δ c Λ F ε →
        S.r u₀ 0 = R₀ → (∀ u ∈ Icc u₀ u₁, R₀ / 2 ≤ S.r u 0) →
        (interactionNorm e S (exteriorDomain ui u₀ u₁ vb) u₀ v₀).toReal ≤ Jstop →
        BoundaryBudgets S ui u₀ u₁ v₀ ρ vb N B E → (∑ n, E n) ≤ F ^ 2 →
        (∀ v ∈ Icc v₀ 0, 2 * c ≤ S.lam u₀ v) →
        let J := (interactionNorm e S (exteriorDomain ui u₀ u₁ vb) u₀ v₀).toReal
        let ζ₂ := Local.sigma e (Interaction.scalarBackground ui R₀ c F Jstop S) (2 * R₀)
        C * ((∑ n, E n) + J ^ 2 + ζ₂) < Real.log 2 →
        (∀ p ∈ exteriorDomain ui u₀ u₁ vb, c < S.lam p.1 p.2) ∧
        ∀ u ∈ Icc u₀ u₁, (-S.nu u 0) / (-S.nu u (vb u)) < 2 := by
  obtain ⟨C, hC, hoptics⟩ := Interaction.source_and_optics_of_stopped δ c Λ F ε ρ hbox
  refine ⟨C, hC, ?_⟩
  intro ui e S h hs Jstop
  obtain ⟨a, ha, ho⟩ := hoptics ui e S h hs Jstop
  refine ⟨a, ha, ?_⟩
  intro u₀ u₁ v₀ R₀ vb N B E hau hN hstop hR₀ hR hJ hE hsum hentry
  dsimp only
  intro hsmall
  have d := stopped_profile_data h B hbox hstop hR₀ hR hJ
  have hb (u : ℝ) (hu : u ∈ Icc u₀ u₁) := boundary_budget_le_sum B hN E hE hu
  have hmass (u : ℝ) (hu : u ∈ Icc u₀ u₁) :
      S.m u (vb u) / S.r u (vb u) ≤ F ^ 2 ∧ F ^ 2 ≤ F ^ 2 := by
    refine ⟨?_, le_rfl⟩
    have hh := (hb u hu).trans hsum
    linarith only [hh, sq_nonneg (‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖)]
  obtain ⟨_, _, _, _, hint, _⟩ := incoming_envelope h B
  obtain ⟨_, hi, hout⟩ := ho u₀ u₁ v₀ R₀ vb _ (fun _ => F ^ 2) N B E hau d hmass hE
  rw [hint] at hi hout
  let J := (interactionNorm e S (exteriorDomain ui u₀ u₁ vb) u₀ v₀).toReal
  let z := Local.sigma e (Interaction.scalarBackground ui R₀ c F Jstop S) (2 * R₀)
  let Q := C * ((∑ n, E n) + J ^ 2 + z)
  have hE0 : 0 ≤ ∑ n, E n := Finset.sum_nonneg (fun n _ => (hE n).1)
  have hz : 0 ≤ z := by dsimp [z, Local.sigma]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hi' : (⨆ v ∈ Icc v₀ 0,
      ∫⁻ u in {u | (u, v) ∈ exteriorDomain ui u₀ u₁ vb},
        ENNReal.ofReal (positiveExpIntegrand S u v)) ≤ ENNReal.ofReal Q := by
    apply hi.trans_eq
    congr 1
    dsimp only [Q, J, z]
    ring
  refine ⟨stopped_expansion_improvement_of_optics h B hbox.2.2.1 hstop hentry hQ hsmall hi', ?_⟩
  intro u hu
  have hlog : Real.log ((-S.nu u 0) / (-S.nu u (vb u))) ≤ Q := by
    apply (hout u hu).trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    linarith only [hb u hu]
  have hp := B.mem u hu
  exact clock_ratio_of_estimates (h.solution.nu_neg _ hp)
    (h.solution.nu_neg (u, 0) ⟨hp.1, hp.2.1, hp.2.1.le, le_rfl⟩) hlog hsmall

/-- [internal]
All five literal stops strictly improve on an available nonempty finite
path, from the produced field budgets, the actual two interaction estimates
and the mixed-clock bound. Only numerical smallness conditions on those
quantities remain. The five coefficients depend on the fixed box and sum
coefficient, before the development, entry row, energies and finite path.
The quantitative closed bound is retained with the same fixed coefficient.
No strict field or stopping conclusion is an input of this helper.
Source: charged_SF_new_version.tex:L4045–L4083. -/
theorem strict_finite_stops_of_budgets (δ c Λ F ε ρ Csum : ℝ)
    (hbox : ExteriorBox δ c Λ F ε ρ) (hF : 0 < F) (hε : 0 < ε) (hCsum : 0 ≤ Csum) :
    ∃ εstop η A ηfield Copt : ℝ,
      0 < εstop ∧ 0 < η ∧ 0 < A ∧ 0 < ηfield ∧ 0 < Copt ∧
      ∀ (ui e : ℝ) (S : Fields), OriginalData ui e S → SignedTerminalBound ui S →
      ∃ a ∈ Ioo ui 0, ∀ (u₀ u₁ v₀ R₀ εentry K εrun : ℝ) (vb : ℝ → ℝ)
        (N : ℕ) (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) (E T : Fin N → ℝ),
      a ≤ u₀ → 0 < N → 0 ≤ εentry → εrun ≤ εstop → S.r u₀ 0 = R₀ →
      (∀ u ∈ Icc u₀ u₁, ∀ w ∈ Icc u 0, δ ≤ 1 - S.mu u w) →
      BoundaryBudgets S ui u₀ u₁ v₀ ρ vb N B E → (∑ n, E n) ≤ F ^ 2 →
      (∀ n, 0 < T n) →
      ∀ γ : ∀ n, ClockCylinder S (origDomain ui) (B.radii n) 0 (T n),
      (∀ n, (γ n).U 0 = B.cuts n.castSucc ∧ (γ n).U (T n) = B.cool n) →
      (∀ n, ∀ τ ∈ Icc 0 (T n), vb ((γ n).U τ) = (γ n).V τ) →
      (∀ v ∈ Icc v₀ 0, 2 * c ≤ S.lam u₀ v) →
      cylinderClock S vb u₀ u₁ ≤ K → 2 * K < R₀ / 4 →
      let J := (interactionNorm e S (exteriorDomain ui u₀ u₁ vb) u₀ v₀).toReal
      let V := ∑ n, (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal
      let z := Local.sigma e (Interaction.scalarBackground ui R₀ c F εstop S) (2 * R₀)
      let L := A * ((initialInteraction S u₀ v₀).toReal + εentry + z)
      FiniteCutoffStops S ui u₀ R₀ vb (fun _ => J) (fun _ => V) δ c Λ F ε εrun u₁ →
      (∑ n, E n) ≤ Csum * (εentry + V ^ 2) →
      (∑ n, Real.sqrt (E n)) ≤ Csum * (Real.sqrt εentry + V) →
      εentry + z ≤ η → L < εrun → (∑ n, E n) ≤ ηfield →
      L ≤ ηfield → z ≤ ηfield → Copt * ((∑ n, E n) + L ^ 2 + z) < Real.log 2 →
      StrictFiniteCutoffStops S ui u₀ R₀ vb (fun _ => J) (fun _ => V) δ c Λ F ε εrun u₁ ∧
        J + V ≤ L := by
  obtain ⟨εstop, η, A, hs, hη, hA, hclosed⟩ :=
    closed_interaction_of_budgets δ c Λ F ε ρ Csum hbox hCsum
  obtain ⟨ηfield, hηfield, hfields⟩ :=
    scalar_mass_improvement_of_budgets c F ε hbox.2.2.1 hF hbox.2.2.2.2.2.1 hε
  obtain ⟨Copt, hCopt, hoptics⟩ := expansion_clock_improvement_of_budgets δ c Λ F ε ρ hbox
  refine ⟨εstop, η, A, ηfield, Copt, hs, hη, hA, hηfield, hCopt, ?_⟩
  intro ui e S h hsigned
  obtain ⟨a₁, ha₁, hclosed⟩ := hclosed ui e S h hsigned
  obtain ⟨a₂, ha₂, hfields⟩ := hfields ui e S h hsigned εstop
  obtain ⟨a₃, ha₃, hoptics⟩ := hoptics ui e S h hsigned εstop
  refine ⟨max a₁ (max a₂ a₃), ⟨ha₁.1.trans_le (le_max_left _ _),
    max_lt ha₁.2 (max_lt ha₂.2 ha₃.2)⟩, ?_⟩
  intro u₀ u₁ v₀ R₀ εentry K εrun vb N B E T hau hN he hrun hR hcore hE hEF hT γ
    hends hgraph hentry hclock hclocksmall
  dsimp only
  intro hstop hsum hhalf hηsmall hLsmall hEfield hLfield hzfield hoptSmall
  have ha₁u := (le_max_left a₁ (max a₂ a₃)).trans hau
  have ha₂u := ((le_max_left a₂ a₃).trans (le_max_right a₁ (max a₂ a₃))).trans hau
  have ha₃u := ((le_max_right a₂ a₃).trans (le_max_right a₁ (max a₂ a₃))).trans hau
  have hEeach (n : Fin N) : E n ≤ F ^ 2 :=
    (Finset.single_le_sum (fun i _ => (hE i).1) (Finset.mem_univ n)).trans hEF
  have hmass (u : ℝ) (hu : u ∈ Icc u₀ u₁) :
      S.m u (vb u) / S.r u (vb u) ≤ ∑ n, E n ∧ (∑ n, E n) ≤ F ^ 2 := by
    have hh := boundary_budget_le_sum B hN E hE hu
    exact ⟨by linarith only [hh, sq_nonneg ‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖], hEF⟩
  have hclosedBound := hclosed u₀ u₁ v₀ R₀ εentry vb (fun _ => ∑ n, E n) N B E T
    ha₁u he hstop.1 hR hstop.2.1 hcore hmass hE hEeach hT γ hends hgraph
    hsum hhalf hηsmall (hstop.2.2.trans hrun)
  have hV0 : 0 ≤ ∑ n, (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal :=
    Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  have hJle := le_trans (le_add_of_nonneg_right hV0) hclosedBound
  have hJstop := ((le_add_of_nonneg_right hV0).trans hstop.2.2).trans hrun
  have hJfield := hJle.trans hLfield
  have hstrictFields := hfields u₀ u₁ v₀ R₀ δ Λ ρ vb N B E ha₂u hN hbox
    hstop.1 hR hstop.2.1 hJstop
    hE hEfield hJfield hzfield
  have hoptSmall' : Copt * ((∑ n, E n) +
      (interactionNorm e S (exteriorDomain ui u₀ u₁ vb) u₀ v₀).toReal ^ 2 +
      Local.sigma e (Interaction.scalarBackground ui R₀ c F εstop S) (2 * R₀)) < Real.log 2 := by
    apply lt_of_le_of_lt ?_ hoptSmall
    gcongr
  obtain ⟨hexp, hratio⟩ := hoptics u₀ u₁ v₀ R₀ vb N B E ha₃u hN hstop.1 hR hstop.2.1
    hJstop hE hEF hentry hoptSmall'
  have hab : u₀ ≤ u₁ := by
    simpa only [B.first, B.last] using B.ordered (Fin.zero_le (Fin.last N))
  have hrat (u : ℝ) (hu : u ∈ Icc u₀ u₁) : -S.nu u 0 ≤ 2 * (-S.nu u (vb u)) :=
    ((div_lt_iff₀ (neg_pos.mpr (h.solution.nu_neg _ (B.mem u hu)))).mp (hratio u hu)).le
  have hrad := (radius_stop_improvement_of_estimates h.solution B hab hR hrat hclock hclocksmall).2
  have hRpos : 0 < R₀ := hR ▸ h.solution.r_pos (u₀, 0)
    ⟨(B.mem u₀ ⟨le_rfl, hab⟩).1, (B.mem u₀ ⟨le_rfl, hab⟩).2.1,
      (B.mem u₀ ⟨le_rfl, hab⟩).2.1.le, le_rfl⟩ (B.mem u₀ ⟨le_rfl, hab⟩).2.1
  refine ⟨⟨hstop.1, (fun p hp => ⟨hexp p hp, hstrictFields p hp⟩), ?_,
    hclosedBound.trans_lt hLsmall⟩, hclosedBound⟩
  intro u hu
  have hanti := (Terminal.terminal_radius_strictAntiOn h.solution).antitoneOn
    ⟨(B.mem u hu).1, (B.mem u hu).2.1⟩ ⟨(B.mem u₁ ⟨hab, le_rfl⟩).1,
      (B.mem u₁ ⟨hab, le_rfl⟩).2.1⟩ hu.2
  linarith only [hrad, hanti, hRpos]

/-- [internal]
One logarithmic envelope bounds the literal canonical scalar background,
including its terminal-annulus supremum. Its coefficient may depend on the
fixed development and `c,F,Jstop`; it precedes every entry tolerance, row,
radius and finite construction. This identifies the charged error in the
closed finite estimate with the logarithmic error used in cone assembly.
Source: charged_SF_new_version.tex:L3887–L3898, L3955–L4002. -/
theorem canonical_background_logarithmic (ui e c F Jstop : ℝ) (S : Fields)
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S)
    (hc : 0 < c) (hF : 0 ≤ F) (hF1 : F < 1) (hJstop : 0 ≤ Jstop) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a ∈ Ico ui 0,
      1 ≤ C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r a 0))) ∧
      Interaction.scalarBackground ui (S.r a 0) c F Jstop S ≤
        C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r a 0))) := by
  obtain ⟨B, _hB, hB1, hamp⟩ := amplitude_scale ui e c F Jstop S h hs hc hF hF1 hJstop
  let K := 1 + (F + c⁻¹ * Jstop) / (1 - F ^ 2)
  have hden : 0 < 1 - F ^ 2 := by nlinarith only [hF, hF1, sq_nonneg (F - 1)]
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let C := B + K
  have hC : 1 ≤ C := hB1.trans (le_add_of_nonneg_right hK)
  refine ⟨C, hC, ?_⟩
  intro a ha
  let L := 1 + Real.sqrt (Real.log (S.r ui 0 / S.r a 0))
  have hL : 1 ≤ L := le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hR := h.solution.r_pos (a, 0) ⟨ha.1, ha.2, ha.2.le, le_rfl⟩ ha.2
  have hsup : Interaction.terminalScalarSup ui (S.r a 0) S ≤ B * L := by
    apply csSup_le (show ((fun u => ‖S.phi u 0‖) ''
      {u | u ∈ Ico ui 0 ∧ S.r a 0 / 2 ≤ S.r u 0 ∧ S.r u 0 ≤ S.r a 0}).Nonempty from
      ⟨_, a, ⟨ha, half_le_self hR.le, le_rfl⟩, rfl⟩)
    rintro _ ⟨u, hu, rfl⟩
    exact ((hamp a ha).2 u hu.1 hu.2.1).1
  have hKL := mul_le_mul_of_nonneg_left hL hK
  constructor
  · exact one_le_mul_of_one_le_of_one_le hC hL
  · change 1 + Interaction.terminalScalarSup ui (S.r a 0) S +
      (F + c⁻¹ * Jstop) / (1 - F ^ 2) ≤ C * L
    dsimp only [C, K] at hKL ⊢
    nlinarith only [hsup, hKL]

end EmcsfAcExtension.Global.Closure
