module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import EmcsfAcExtension.Global.Closure.Profiles
public import EmcsfAcExtension.Global.Closure.Clock
public import EmcsfAcExtension.Global.Defs.Observation
import EmcsfAcExtension.Global.Closure.CutoffContinuity
import EmcsfAcExtension.Global.Closure.Continuation
import EmcsfAcExtension.Global.Closure.Stages
import EmcsfAcExtension.Global.Closure.StageSums
import EmcsfAcExtension.Global.Cooling.ObservationDischarge
import EmcsfAcExtension.Global.Observation.CylinderClock
import EmcsfAcExtension.Global.Observation.Energy
import EmcsfAcExtension.Global.Interaction.NEstimate
import Mathlib.Tactic

/-! # Field budgets and absorption for the stopped exterior

The simultaneous inequalities of `charged_SF_new_version.tex:L4028–L4052` are absorbed
before using strict improvement to continue a stage. All constants below
precede the entry quantities and every finite cutoff.
-/

public section

namespace EmcsfAcExtension.Global.Interaction

/-- [internal]
Numerical support for `eq:cc-closed`, in the internal project record template form.
The thresholds and final coefficient depend only on `c,C,F`, uniformly in
the entry density, entry energy, charged error, and accumulated variations.
The closure consumer supplies the two stopped inequalities and the finite
real values of the envelopes before applying this lemma. -/
theorem stopped_absorption (c C F : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hF : 0 ≤ F ∧ F ≤ 1) :
    ∃ δ η A : ℝ, 0 < δ ∧ 0 < η ∧ 0 < A ∧
      ∀ D₀ ε₀ ζ₂ J Svar : ℝ,
      0 ≤ D₀ → 0 ≤ ε₀ → 0 ≤ ζ₂ → 0 ≤ J → 0 ≤ Svar →
      ε₀ + ζ₂ ≤ η → J + Svar ≤ δ →
      J ≤ D₀ + C * (ε₀ + Svar ^ 2) + C * J * (ε₀ + Svar ^ 2) +
        C * F * J * (Real.sqrt ε₀ + Svar) + C * F * J ^ 2 + C * ζ₂ * (1 + J) →
      Svar ≤ c⁻¹ * J + C * (ε₀ + Svar ^ 2) + C * ζ₂ →
      J + Svar ≤ A * (D₀ + ε₀ + ζ₂) := by
  let δ := min 1 (min (1 / (2 * C)) (1 / (4 * C * (c⁻¹ + 3))))
  have hi : 0 < c⁻¹ := inv_pos.mpr hc
  have hF0 := hF.1
  have hF1 := hF.2
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hd1 : δ ≤ 1 := min_le_left _ _
  have hdC : C * δ ≤ 1 / 2 := by
    have hh : δ ≤ 1 / (2 * C) := (min_le_right _ _).trans (min_le_left _ _)
    have hh' := (le_div_iff₀ (by positivity : 0 < 2 * C)).mp hh
    linarith
  have hdcoef : (2 * c⁻¹ + 6) * (C * δ) ≤ 1 / 2 := by
    have hh : δ ≤ 1 / (4 * C * (c⁻¹ + 3)) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hh' := (le_div_iff₀ (by positivity : 0 < 4 * C * (c⁻¹ + 3))).mp hh
    nlinarith only [hh']
  let K := 2 + 4 * C
  let A := (1 + 2 * c⁻¹) * K + 2 * C
  refine ⟨δ, δ ^ 2, A, hd, sq_pos_of_pos hd, by dsimp [A, K]; positivity, ?_⟩
  intro D ε z J S hD he hz hJ hS hentry hstop hfirst hsecond
  have hJd : J ≤ δ := by linarith
  have hSd : S ≤ δ := by linarith
  have hesq : ε ≤ δ ^ 2 := by linarith
  have hzsq : z ≤ δ ^ 2 := by linarith
  have hdsq : δ ^ 2 ≤ δ := by nlinarith only [hd1, hd.le]
  have hed : ε ≤ δ := hesq.trans hdsq
  have hzd : z ≤ δ := hzsq.trans hdsq
  have hsqrt : Real.sqrt ε ≤ δ := (Real.sqrt_le_iff).mpr ⟨hd.le, hesq⟩
  have hSsq : S ^ 2 ≤ δ * S := by nlinarith only [hSd, hS]
  have hSsq' : S ^ 2 ≤ δ :=
    (sq_le_sq₀ hS hd.le).mpr hSd |>.trans hdsq
  have hJsq : J ^ 2 ≤ δ * J := by nlinarith only [hJd, hJ]
  have hCsq : C * S ^ 2 ≤ C * δ * S := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hSsq hC.le
  have hS' : S ≤ 2 * c⁻¹ * J + 2 * C * (ε + z) := by
    have hh := mul_le_mul_of_nonneg_right hdC hS
    nlinarith only [hsecond, hCsq, hh]
  have hterm₁ : C * J * (ε + S ^ 2) ≤ 2 * C * δ * J := by
    have hh := mul_le_mul_of_nonneg_left (add_le_add hed hSsq')
      (mul_nonneg hC.le hJ)
    nlinarith only [hh]
  have hterm₂ : C * F * J * (Real.sqrt ε + S) ≤ 2 * C * δ * J := by
    calc
      _ ≤ C * 1 * J * (δ + δ) := by gcongr
      _ = _ := by ring
  have hterm₃ : C * F * J ^ 2 ≤ C * δ * J := by
    calc
      _ ≤ C * 1 * (δ * J) := by gcongr
      _ = _ := by ring
  have hterm₄ : C * z * J ≤ C * δ * J := by gcongr
  have hfirst' : J ≤ D + C * (ε + z) + C * δ * S + 6 * C * δ * J := by
    nlinarith only [hfirst, hCsq, hterm₁, hterm₂, hterm₃, hterm₄]
  have hsub := mul_le_mul_of_nonneg_left hS' (mul_nonneg hC.le hd.le)
  have hcoef := mul_le_mul_of_nonneg_right hdcoef hJ
  have hdata := mul_le_mul_of_nonneg_right hdC
    (mul_nonneg (show 0 ≤ 2 * C by positivity) (add_nonneg he hz))
  have hJ' : J ≤ 2 * D + 4 * C * (ε + z) := by
    nlinarith only [hfirst', hsub, hcoef, hdata]
  have hJK : J ≤ K * (D + ε + z) := by
    dsimp only [K]
    have hCD := mul_nonneg (show 0 ≤ 4 * C by positivity) hD
    linarith only [hJ', hCD, he, hz]
  have hSJ := mul_le_mul_of_nonneg_left hJK (show 0 ≤ 2 * c⁻¹ by positivity)
  have hCD := mul_nonneg (show 0 ≤ 2 * C by positivity) hD
  dsimp only [A]
  nlinarith only [hJK, hS', hSJ, hCD]

end EmcsfAcExtension.Global.Interaction

namespace EmcsfAcExtension.Global.Closure

open Set MeasureTheory Filter Topology
open scoped ENNReal

/-- [internal]
The finite sum of full-stage budgets bounds the field energy at every
boundary point, including all connectors. The coefficient is one, uniform
in the finite path. The empty path is handled by its entry estimate. -/
theorem boundary_budget_le_sum {ui u₀ u₁ v₀ ρ : ℝ} {S : Fields} {vb : ℝ → ℝ}
    {N : ℕ} (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) (hN : 0 < N)
    (E : Fin N → ℝ) (hE : BoundaryBudgets S ui u₀ u₁ v₀ ρ vb N B E)
    {u : ℝ} (hu : u ∈ Icc u₀ u₁) :
    S.m u (vb u) / S.r u (vb u) +
      ‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖ ^ 2 ≤ ∑ n, E n := by
  obtain ⟨n, hn⟩ := stage_interval_cover hN B.cuts
    (show u ∈ Icc (B.cuts 0) (B.cuts (Fin.last N)) by
      simpa only [B.first, B.last] using hu)
  exact ((hE n).2.1 u hn).trans
    (Finset.single_le_sum (fun n _ => (hE n).1) (Finset.mem_univ n))

/-- [internal]
The first stopped inequality on the actual finite source envelope. The
profiles and their common-label representative bound are derived from the
weak stops. The coefficient depends only on the fixed box and `Csum`,
before the development, stopping budget, late entry and every finite path.
The field budgets and their two finite sums are supplied by the stage
construction, including a partial last stage. Source: charged_SF_new_version.tex:L4028–L4035.
-/
theorem stopped_source_inequality_of_budgets (δ c Λ F ε ρ Csum : ℝ)
    (hbox : ExteriorBox δ c Λ F ε ρ) (hCsum : 0 ≤ Csum) :
    ∃ C > 0, ∀ (ui e : ℝ) (S : Fields),
      OriginalData ui e S → SignedTerminalBound ui S → ∀ Jstop : ℝ,
      ∃ a ∈ Ioo ui 0, ∀ (u₀ u₁ v₀ R₀ εentry Svar : ℝ) (vb en : ℝ → ℝ)
        (N : ℕ) (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) (E : Fin N → ℝ),
        a ≤ u₀ → 0 ≤ εentry → 0 ≤ Svar →
        ExteriorStops S (exteriorDomain ui u₀ u₁ vb) δ c Λ F ε →
        S.r u₀ 0 = R₀ → (∀ u ∈ Icc u₀ u₁, R₀ / 2 ≤ S.r u 0) →
        (interactionNorm e S (exteriorDomain ui u₀ u₁ vb) u₀ v₀).toReal ≤ Jstop →
        (∀ u ∈ Icc u₀ u₁, S.m u (vb u) / S.r u (vb u) ≤ en u ∧ en u ≤ F ^ 2) →
        BoundaryBudgets S ui u₀ u₁ v₀ ρ vb N B E →
        (∑ n, E n) ≤ Csum * (εentry + Svar ^ 2) →
        (∑ n, Real.sqrt (E n)) ≤ Csum * (Real.sqrt εentry + Svar) →
        let J := (interactionNorm e S (exteriorDomain ui u₀ u₁ vb) u₀ v₀).toReal
        let ζ₂ := Local.sigma e (Interaction.scalarBackground ui R₀ c F Jstop S) (2 * R₀)
        J ≤ (initialInteraction S u₀ v₀).toReal + C * (εentry + Svar ^ 2) +
          C * J * (εentry + Svar ^ 2) + C * F * J * (Real.sqrt εentry + Svar) +
          C * F * J ^ 2 + C * ζ₂ * (1 + J) := by
  obtain ⟨Cq, hCq, hprofiles⟩ := Interaction.stopped_profiles
  obtain ⟨Cs, hCs, hsource⟩ :=
    Interaction.n_estimate_of_profiles δ c Λ F ε ρ Cq hbox hCq.le
  let C := Cs * (1 + Csum)
  have hC : 0 < C := mul_pos hCs (by positivity)
  have hCsC : Cs ≤ C := by dsimp [C]; nlinarith only [mul_nonneg hCs.le hCsum]
  have hprod : Cs * Csum ≤ C := by dsimp [C]; linarith only [hCs]
  refine ⟨C, hC, ?_⟩
  intro ui e S h hs Jstop
  obtain ⟨a, ha, hprof⟩ := hprofiles ui e S h hs Jstop
  refine ⟨a, ha, ?_⟩
  intro u₀ u₁ v₀ R₀ εentry Svar vb en N B E hau he hSvar hstop hR₀ hR hJ hmass hE hsum hhalf
  let K := exteriorDomain ui u₀ u₁ vb
  let g := fun v => (incomingEnvelope e S K u₀ v).toReal
  let J := (interactionNorm e S K u₀ v₀).toReal
  let z := Local.sigma e (Interaction.scalarBackground ui R₀ c F Jstop S) (2 * R₀)
  have hab : u₀ ≤ u₁ := by
    simpa only [B.first, B.last] using B.ordered (Fin.zero_le (Fin.last N))
  have d := stopped_profile_data h B hbox hstop hR₀ hR hJ
  obtain ⟨hfin, hg, hg0, hmajor, hint, heq⟩ := incoming_envelope h B
  have hp := hprof u₀ u₁ v₀ R₀ δ c Λ F ε vb g en hau d hmass
  have hsour := hsource ui e u₀ u₁ v₀ R₀ _ S vb g N B E h hab
    (B.mem u₁ ⟨hab, le_rfl⟩).2.1 d.radius_pos
    (d.one_le_background h ⟨le_rfl, hab⟩) hstop d.annulus hE
    (fun p hp' => (hp p.1 ⟨hp'.2.1, hp'.2.2.1⟩ p.2
      ⟨hp'.2.2.2, hp'.1.2.2.2⟩).2) hg (Eventually.of_forall hg0)
    (hmajor.mono (fun _ hv u hu huv => (hv u hu huv).1))
  dsimp only at hsour
  rw [hint] at hsour
  have hJ0 : 0 ≤ J := ENNReal.toReal_nonneg
  have hz : 0 ≤ z := by dsimp [z, Local.sigma]; positivity
  have hF : 0 ≤ F := hbox.2.2.2.2.1
  have hsum0 : 0 ≤ ∑ n, E n := Finset.sum_nonneg (fun n _ => (hE n).1)
  have hraw :
      (sourceInteraction e S K v₀).toReal ≤
        Cs * (∑ n, E n) + Cs * J * (∑ n, E n) +
        Cs * F * J * (∑ n, Real.sqrt (E n)) + Cs * F * J ^ 2 + Cs * z * (1 + J) := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsour
    have hn : 0 ≤ Cs * (∑ n, E n) + Cs * J * (∑ n, E n) +
        Cs * F * J * (∑ n, Real.sqrt (E n)) + Cs * F * J ^ 2 + Cs * z * (1 + J) := by
      positivity
    rw [ENNReal.toReal_ofReal hn] at hh
    exact hh
  have hterm₁ : Cs * (∑ n, E n) ≤ C * (εentry + Svar ^ 2) := by
    calc
      _ ≤ Cs * (Csum * (εentry + Svar ^ 2)) := mul_le_mul_of_nonneg_left hsum hCs.le
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hprod (add_nonneg he (sq_nonneg Svar))]
  have hterm₂ := mul_le_mul_of_nonneg_right hterm₁ hJ0
  have hterm₃ : Cs * F * J * (∑ n, Real.sqrt (E n)) ≤
      C * F * J * (Real.sqrt εentry + Svar) := by
    calc
      _ ≤ Cs * F * J * (Csum * (Real.sqrt εentry + Svar)) := by gcongr
      _ = (Cs * Csum) * F * J * (Real.sqrt εentry + Svar) := by ring
      _ ≤ _ := by gcongr
  have hterm₄ := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCsC hF) (sq_nonneg J)
  have hterm₅ := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCsC hz) (show 0 ≤ 1 + J by positivity)
  have hadd : J = (initialInteraction S u₀ v₀).toReal + (sourceInteraction e S K v₀).toReal := by
    have hn : initialInteraction S u₀ v₀ + sourceInteraction e S K v₀ ≠ ⊤ := by
      rw [← heq]
      exact hfin.ne
    change (interactionNorm e S K u₀ v₀).toReal = _
    rw [heq]
    exact ENNReal.toReal_add (ENNReal.add_ne_top.mp hn).1 (ENNReal.add_ne_top.mp hn).2
  change J ≤ _
  change J ≤ (initialInteraction S u₀ v₀).toReal + C * (εentry + Svar ^ 2) +
    C * J * (εentry + Svar ^ 2) + C * F * J * (Real.sqrt εentry + Svar) +
    C * F * J ^ 2 + C * z * (1 + J)
  linarith only [hraw, hadd, hterm₁, hterm₂, hterm₃, hterm₄, hterm₅]

/-- [internal]
Absorb both actual finite stopped estimates after the field budgets have
been produced. Neither source nor forcing inequality is an assumption.
The stopping threshold, entry ceiling and final constant depend only on
the fixed box and finite-sum coefficient, before the development, late
entry, finite boundary, radii and durations. Source: charged_SF_new_version.tex:L4041–L4054.
-/
theorem closed_interaction_of_budgets (δ c Λ F ε ρ Csum : ℝ)
    (hbox : ExteriorBox δ c Λ F ε ρ) (hCsum : 0 ≤ Csum) :
    ∃ εstop η A : ℝ, 0 < εstop ∧ 0 < η ∧ 0 < A ∧
      ∀ (ui e : ℝ) (S : Fields), OriginalData ui e S → SignedTerminalBound ui S →
      ∃ a ∈ Ioo ui 0, ∀ (u₀ u₁ v₀ R₀ εentry : ℝ) (vb en : ℝ → ℝ)
        (N : ℕ) (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) (E T : Fin N → ℝ),
        a ≤ u₀ → 0 ≤ εentry →
        ExteriorStops S (exteriorDomain ui u₀ u₁ vb) δ c Λ F ε →
        S.r u₀ 0 = R₀ → (∀ u ∈ Icc u₀ u₁, R₀ / 2 ≤ S.r u 0) →
        (∀ u ∈ Icc u₀ u₁, ∀ w ∈ Icc u 0, δ ≤ 1 - S.mu u w) →
        (∀ u ∈ Icc u₀ u₁, S.m u (vb u) / S.r u (vb u) ≤ en u ∧ en u ≤ F ^ 2) →
        BoundaryBudgets S ui u₀ u₁ v₀ ρ vb N B E → (∀ n, E n ≤ F ^ 2) →
        (∀ n, 0 < T n) →
        ∀ γ : ∀ n, ClockCylinder S (origDomain ui) (B.radii n) 0 (T n),
        (∀ n, (γ n).U 0 = B.cuts n.castSucc ∧ (γ n).U (T n) = B.cool n) →
        (∀ n, ∀ τ ∈ Icc 0 (T n), vb ((γ n).U τ) = (γ n).V τ) →
        let J := (interactionNorm e S (exteriorDomain ui u₀ u₁ vb) u₀ v₀).toReal
        let Svar := ∑ n, (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal
        let ζ₂ := Local.sigma e (Interaction.scalarBackground ui R₀ c F εstop S) (2 * R₀)
        (∑ n, E n) ≤ Csum * (εentry + Svar ^ 2) →
        (∑ n, Real.sqrt (E n)) ≤ Csum * (Real.sqrt εentry + Svar) →
        εentry + ζ₂ ≤ η → J + Svar ≤ εstop →
        J + Svar ≤ A * ((initialInteraction S u₀ v₀).toReal + εentry + ζ₂) := by
  have hc := hbox.2.2.1
  have hF := hbox.2.2.2.2.1
  have hF1 := hbox.2.2.2.2.2.1
  obtain ⟨Cs, hCs, hs⟩ := stopped_source_inequality_of_budgets δ c Λ F ε ρ Csum hbox hCsum
  obtain ⟨Cf, hCf, hf⟩ := stopped_forcing_inequality_of_budgets δ F hbox.1 hbox.2.1 hF hF1
  let C := Cs + Cf * (Csum + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  have hsC : Cs ≤ C := le_add_of_nonneg_right (mul_nonneg hCf.le (by positivity))
  have hfC : Cf ≤ C := by dsimp [C]; nlinarith only [hCs, mul_nonneg hCf.le hCsum]
  have hfprod : Cf * Csum ≤ C := by dsimp [C]; linarith only [hCs, hCf]
  obtain ⟨εstop, η, A, hεstop, hη, hA, habsorb⟩ :=
    Interaction.stopped_absorption c C F hc hC ⟨hF, hF1.le⟩
  refine ⟨εstop, η, A, hεstop, hη, hA, ?_⟩
  intro ui e S h hsigned
  obtain ⟨a, ha, hsource⟩ := hs ui e S h hsigned εstop
  refine ⟨a, ha, ?_⟩
  intro u₀ u₁ v₀ R₀ εentry vb en N B E T hau he hstop hR₀ hR hcore hmass hE hEF hT γ hends hgraph
  dsimp only
  let J := (interactionNorm e S (exteriorDomain ui u₀ u₁ vb) u₀ v₀).toReal
  let V := ∑ n, (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal
  let z := Local.sigma e (Interaction.scalarBackground ui R₀ c F εstop S) (2 * R₀)
  intro hsum hhalf hentry hsmall
  have hJ0 : 0 ≤ J := ENNReal.toReal_nonneg
  have hV0 : 0 ≤ V := Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  have hz : 0 ≤ z := by dsimp [z, Local.sigma]; positivity
  have hJ : J ≤ εstop := by linarith only [hsmall, hV0]
  have hsource := hsource u₀ u₁ v₀ R₀ εentry V vb en N B E hau he hV0
    hstop hR₀ hR hJ hmass hE hsum hhalf
  have hforcing := hf ui e u₀ u₁ v₀ ρ R₀ c Λ ε εstop S vb N B E T
    h hbox hεstop.le hstop hR₀ hR hJ hcore hE hEF hT γ hends hgraph
  apply habsorb (initialInteraction S u₀ v₀).toReal εentry z J V
    ENNReal.toReal_nonneg he hz hJ0 hV0 hentry hsmall
  · apply hsource.trans
    change _ ≤ (initialInteraction S u₀ v₀).toReal + C * (εentry + V ^ 2) +
      C * J * (εentry + V ^ 2) + C * F * J * (Real.sqrt εentry + V) +
      C * F * J ^ 2 + C * z * (1 + J)
    gcongr
  · have hterm : Cf * (∑ n, E n) ≤ C * (εentry + V ^ 2) := by
      calc
        _ ≤ Cf * (Csum * (εentry + V ^ 2)) := mul_le_mul_of_nonneg_left hsum hCf.le
        _ = (Cf * Csum) * (εentry + V ^ 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hfprod (by positivity)
    have hzterm := mul_le_mul_of_nonneg_right hfC hz
    change V ≤ c⁻¹ * J + Cf * (∑ n, E n) + Cf * z at hforcing
    linarith only [hforcing, hterm, hzterm]

/-- [internal]
Produce the actual finite field budgets, including an unfinished last
cylinder or connector, from the weak stops and the already propagated
initial cylinder energies. Observation and cooling are unconditional.
The comparison triangles and charged scale are discharged from retained
radius, independent late geometry and the canonical exterior profile.
The constants depend only on `δ,εweak,ρ`, before recurrence parameters,
fields, stopping budgets, entry, radii and durations.
Source: charged_SF_new_version.tex:L3911–L3932, L4016–L4026, L4086–L4102. -/
theorem stopped_boundary_budgets_of_initial_energies (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    ∃ Ts δs ηs : ℝ, 0 < Ts ∧ 0 < δs ∧ 0 < ηs ∧
      ∀ (εweak ρ : ℝ), 0 ≤ εweak → 0 < ρ → ∃ Cbudget > 0,
      ∀ (χ C εentry c Λ F ui e u₀ u₁ v₀ Jstop R₀ : ℝ)
        (S : Fields) (vb : ℝ → ℝ) (σ : ℕ → ℝ) (N : ℕ)
        (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) (T : Fin N → ℝ),
      0 ≤ χ → 0 ≤ C → 0 ≤ εentry → 0 ≤ Jstop → F + εweak ≤ δs →
      OriginalData ui e S → ExteriorBox δ c Λ F εweak ρ →
      ExteriorStops S (exteriorDomain ui u₀ u₁ vb) δ c Λ F εweak →
      S.r u₀ 0 = R₀ → (∀ u ∈ Icc u₀ u₁, R₀ / 2 ≤ S.r u 0) →
      (interactionNorm e S (exteriorDomain ui u₀ u₁ vb) u₀ v₀).toReal ≤ Jstop →
      (∀ p ∈ origDomain ui, u₀ ≤ p.1 → 0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) →
      (∀ n, B.radii n < R₀ / 2) → (∀ n, 0 ≤ T n) →
      ∀ γ : ∀ n, ClockCylinder S (origDomain ui) (B.radii n) 0 (T n),
      (∀ n, (γ n).U 0 = B.cuts n.castSucc ∧ (γ n).U (T n) = B.cool n) →
      (∀ n, ∀ τ ∈ Icc 0 (T n), vb ((γ n).U τ) = (γ n).V τ) →
      (∀ n : Fin N, σ n = (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal) →
      (∀ n, cylinderEnergy S (B.radii n) ((γ n).U 0) ((γ n).V 0) / B.radii n ≤
        energyEnvelope χ C εentry σ n) →
      let z := Local.sigma e (Interaction.scalarBackground ui R₀ c F Jstop S) (2 * R₀)
      z ≤ 1 → 9 * z ≤ ηs ^ 2 →
      BoundaryBudgets S ui u₀ u₁ v₀ ρ vb N B (fun n => stageBudget Cbudget χ C εentry σ n) := by
  obtain ⟨Ts, δs, ηs, hTs, hδs, hηs, hbudgets⟩ :=
    finite_stage_budgets_of_estimates δ hδ (Cooling.observation_input δ hδ)
  refine ⟨Ts, δs, ηs, hTs, hδs, hηs, ?_⟩
  intro εweak ρ hεweak hρ
  obtain ⟨Cb, hCb, hbudget⟩ := hbudgets εweak ρ hεweak hρ
  refine ⟨Cb, hCb, ?_⟩
  intro χ C εentry c Λ F ui e u₀ u₁ v₀ Jstop R₀ S vb σ N B T
    hχ hC he hJstop hweak h hbox hstop hR₀ hR hJ hgap hradii hT γ hends hgraph hσ henergy
  dsimp only
  intro hz1 hzη
  have hab : u₀ ≤ u₁ := by
    simpa only [B.first, B.last] using B.ordered (Fin.zero_le (Fin.last N))
  have d := stopped_profile_data h B hbox hstop hR₀ hR hJ
  obtain ⟨_, hg, hg0, _, hint, _⟩ := incoming_envelope h B
  let g := fun v => (incomingEnvelope e S (exteriorDomain ui u₀ u₁ vb) u₀ v).toReal
  let M := Interaction.scalarBackground ui R₀ c F Jstop S
  have hM := d.one_le_background h ⟨le_rfl, hab⟩
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hRpos : 0 < R₀ := d.radius_pos
  have hscale : 3 * (|e| * M * R₀) ≤ ηs := by
    apply (sq_le_sq₀ (by positivity) hηs.le).mp
    rw [ct_zeta] at hzη
    calc
      (3 * (|e| * M * R₀)) ^ 2 = 9 * (e ^ 2 * M ^ 2 * R₀ ^ 2) := by
        simp only [mul_pow, sq_abs]
        ring
      _ ≤ ηs ^ 2 := hzη
  have hcurve (n : Fin N) (τ : ℝ) (hτ : τ ∈ Icc 0 (T n)) :
      (γ n).U τ ∈ Icc u₀ u₁ ∧ ((γ n).U τ, (γ n).V τ) ∈ exteriorDomain ui u₀ u₁ vb := by
    have hm := ((γ n).strictMonoOn_U h.solution).monotoneOn
    have hl := hm (left_mem_Icc.mpr (hT n)) hτ hτ.1
    have hr := hm hτ (right_mem_Icc.mpr (hT n)) hτ.2
    rw [(hends n).1] at hl
    rw [(hends n).2] at hr
    have hu : (γ n).U τ ∈ Icc u₀ u₁ :=
      ⟨(B.first.ge.trans (B.ordered (Fin.zero_le _))).trans hl,
        hr.trans ((B.split n).2.trans ((B.ordered (Fin.le_last _)).trans B.last.le))⟩
    exact ⟨hu, (γ n).mem τ hτ, hu.1, hu.2, (hgraph n τ hτ).le⟩
  have hterm (n : Fin N) (τ : ℝ) (hτ : τ ∈ Icc 0 (T n)) :
      B.radii n < S.r ((γ n).U τ) 0 := (hradii n).trans_le (hR _ (hcurve n τ hτ).1)
  have hwindows (n : Fin N) (τ : ℝ) (hτ : τ ∈ Icc (Ts * B.radii n) (T n - Ts * B.radii n)) :=
    observation_window_regions h (γ n) (B.radius_pos n) hTs.le
      (by rw [(hends n).1]; exact B.first.ge.trans (B.ordered (Fin.zero_le _)))
      (hterm n) hgap τ hτ
  have hcool (n : Fin N) : B.cool n ∈ Icc u₀ u₁ :=
    ⟨(B.first.ge.trans (B.ordered (Fin.zero_le _))).trans (B.split n).1,
      (B.split n).2.trans ((B.ordered (Fin.le_last _)).trans B.last.le)⟩
  apply hbudget (g := fun _ => g) χ C εentry c Λ F ui e u₀ u₁ v₀
    (Interaction.terminalScalarSup ui R₀ S) Jstop R₀ S vb σ N B T
    hχ hC he hbox.2.2.1 hbox.2.2.2.2.1 hbox.2.2.2.2.2.1 hJstop h hT γ hends hgraph
    (fun n => Cylinder.ac_curveParallel_a h.solution (γ n) (B.radius_pos n) (hT n)) hσ henergy
  · intro n τ hτ
    have hp := hcurve n τ hτ
    have hs := hstop _ hp.2
    have hmu : S.mu ((γ n).U τ) ((γ n).V τ) ≤ εweak := by
      apply le_trans _ hs.2.2.2.2.2.1
      apply (le_div_iff₀ (h.solution.one_sub_mu_pos _ hp.2.1)).mpr
      nlinarith only [sq_nonneg (S.mu ((γ n).U τ) ((γ n).V τ))]
    exact (add_le_add hmu hs.2.2.2.2.1).trans (by linarith only [hweak])
  · intro n τ hτ
    have hw := hwindows n τ hτ
    have hwidth := mul_nonneg hTs.le (B.radius_pos n).le
    have hτ' : τ ∈ Icc 0 (T n) :=
      ⟨hwidth.trans hτ.1, hτ.2.trans (sub_le_self _ hwidth)⟩
    have hp := hcurve n τ hτ'
    refine ⟨hw.1, hw.2, ?_⟩
    apply le_trans _ hscale
    exact (observation_physical_scale_of_profile (B.radius_pos n).le
      ((hradii n).le.trans (half_le_self d.radius_pos.le)) hM hbox.2.2.2.2.2.1.le
      (ct_m0 h d _ hp.2) (hstop _ hp.2).2.2.2.2.1).2
  · exact hstop
  · intro u hu w hw
    exact (hgap (u, w) (d.core_segment hu ⟨rfl, hw.1, hw.2⟩) hu.1).2
  · intro u hu
    exact Interaction.terminal_scalar_le_sup h d.radius_pos
      ⟨(B.mem u hu).1, (B.mem u hu).2.1⟩ (d.annulus u hu)
  · intro n
    exact (hradii n).le.trans (half_le_self d.radius_pos.le)
  · intro n
    exact hg.mono_set (Icc_subset_Icc
      (InteractionEstimate.finite_boundary_label_bounds B _ (hcool n)).1 le_rfl)
  · intro n
    exact Eventually.of_forall hg0
  · intro n u hu
    have hu' : u ∈ Icc u₀ u₁ :=
      ⟨(hcool n).1.trans hu.1, hu.2.trans ((B.ordered (Fin.le_last _)).trans B.last.le)⟩
    filter_upwards [(d.majorant u hu').filter_mono (ae_mono (Measure.restrict_mono
      (Icc_subset_Icc (InteractionEstimate.finite_boundary_label_bounds B _ (hcool n)).1
        le_rfl) le_rfl)),
      ae_restrict_mem measurableSet_Icc] with w hw hwm
    apply hw
    rw [B.connector n u hu]
    exact hwm.1
  · intro n
    have hv := InteractionEstimate.finite_boundary_label_bounds B _ (hcool n)
    have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le (hv.1.trans hv.2)).mpr hg
    have hh := intervalIntegral.integral_mono_interval hv.1 hv.2 le_rfl
      (Eventually.of_forall hg0) hi
    exact hh.trans d.budget
  · simpa only [ct_zeta, Interaction.scalarBackground] using hz1

/-- [internal]
Choose a smaller running stop and then a common entry-error tolerance so
that the closed interaction, field, optical and preliminary budget margins
hold simultaneously. Every coefficient is fixed before both witnesses and
before all data, physical scales, stages and cutoffs. This is the numerical
part of the entry choice; it asserts no availability of a stage.
Source: charged_SF_new_version.tex:L4045–L4083; approved internal project record initialization. -/
theorem exists_strict_stopping_margins (εabs ηabs A ηfield Copt Csum F : ℝ)
    (hεabs : 0 < εabs) (hηabs : 0 < ηabs) (_hA : 0 < A)
    (hηfield : 0 < ηfield) (_hCopt : 0 < Copt) (_hCsum : 0 ≤ Csum) (hF : 0 < F) :
    ∃ εrun q : ℝ, 0 < εrun ∧ 0 < q ∧ εrun ≤ εabs ∧ q ≤ ηabs ∧ q ≤ ηfield ∧
      A * q < εrun ∧ A * q ≤ ηfield ∧
      Csum * (q + εrun ^ 2) ≤ F ^ 2 ∧ Csum * (q + εrun ^ 2) ≤ ηfield ∧
      Copt * (Csum * (q + εrun ^ 2) + (A * q) ^ 2 + q) < Real.log 2 := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have cs : ContinuousAt (fun s : ℝ => Csum * s ^ 2) 0 := by fun_prop
  have co : ContinuousAt (fun s : ℝ => Copt * (Csum * s ^ 2)) 0 := by fun_prop
  have hs : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s ∧ s < εabs ∧
      Csum * s ^ 2 < F ^ 2 ∧ Csum * s ^ 2 < ηfield ∧
      Copt * (Csum * s ^ 2) < Real.log 2 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hεabs),
      (cs.tendsto.mono_left nhdsWithin_le_nhds).eventually
        (Iio_mem_nhds (by simpa using sq_pos_of_pos hF)),
      (cs.tendsto.mono_left nhdsWithin_le_nhds).eventually
        (Iio_mem_nhds (by simpa using hηfield)),
      (co.tendsto.mono_left nhdsWithin_le_nhds).eventually
        (Iio_mem_nhds (by simpa using hlog))] with s hs hsa hsF hsf hso
    exact ⟨hs, hsa, hsF, hsf, hso⟩
  obtain ⟨s, hs, hsa, hsF, hsf, hso⟩ := hs.exists
  let B := fun t : ℝ => Csum * (t + s ^ 2)
  let O := fun t : ℝ => Copt * (B t + (A * t) ^ 2 + t)
  have cB : ContinuousAt B 0 := by dsimp [B]; fun_prop
  have cO : ContinuousAt O 0 := by dsimp [O, B]; fun_prop
  have cA : ContinuousAt (fun t : ℝ => A * t) 0 := by fun_prop
  have hq : ∀ᶠ q in 𝓝[>] (0 : ℝ), 0 < q ∧ q < ηabs ∧ q < ηfield ∧
      A * q < s ∧ A * q < ηfield ∧ B q < F ^ 2 ∧ B q < ηfield ∧ O q < Real.log 2 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hηabs), nhdsWithin_le_nhds (Iio_mem_nhds hηfield),
      (cA.tendsto.mono_left nhdsWithin_le_nhds).eventually (Iio_mem_nhds (by simpa using hs)),
      (cA.tendsto.mono_left nhdsWithin_le_nhds).eventually
        (Iio_mem_nhds (by simpa using hηfield)),
      (cB.tendsto.mono_left nhdsWithin_le_nhds).eventually
        (Iio_mem_nhds (by simpa [B] using hsF)),
      (cB.tendsto.mono_left nhdsWithin_le_nhds).eventually
        (Iio_mem_nhds (by simpa [B] using hsf)),
      (cO.tendsto.mono_left nhdsWithin_le_nhds).eventually
        (Iio_mem_nhds (by simpa [O, B] using hso))] with q hq hqa hqf hqs hqA hqB hqBf hqO
    exact ⟨hq, hqa, hqf, hqs, hqA, hqB, hqBf, hqO⟩
  obtain ⟨q, hq, hqa, hqf, hqs, hqA, hqB, hqBf, hqO⟩ := hq.exists
  exact ⟨s, q, hs, hq, hsa.le, hqa.le, hqf.le, hqs, hqA.le, hqB.le, hqBf.le, hqO⟩

/-- [internal]
Assemble compatible finite paths and their common budget sequence on one
boundary graph. All cuts are preserved exactly and the full weighted
budgets, including connectors, are transferred by equality on each prefix.
The finite paths are data of this helper; their production at every stage
remains the separate construction obligation. Constants: none.
Source: charged_SF_new_version.tex:L4106–L4115. -/
theorem common_finite_boundaries_of_coherent_prefixes {S : Fields} {ui u₀ v₀ ρ : ℝ}
    (U : ℕ → ℝ) (V : ℕ → ℝ → ℝ)
    (B : ∀ N, FiniteBoundary S ui u₀ (U N) v₀ ρ (V N) N) (E : ℕ → ℝ)
    (hcompat : ∀ M N, M ≤ N → EqOn (V N) (V M) (Icc u₀ (U M)))
    (hE : ∀ N, BoundaryBudgets S ui u₀ (U N) v₀ ρ (V N) N (B N) (fun i => E i)) :
    ∃ vb : ℝ → ℝ, ∃ B' : ∀ N, FiniteBoundary S ui u₀ (U N) v₀ ρ vb N,
      (∀ N, EqOn vb (V N) (Icc u₀ (U N))) ∧
      (∀ N i, (B' N).cuts i = (B N).cuts i) ∧
      ∀ N, BoundaryBudgets S ui u₀ (U N) v₀ ρ vb N (B' N) (fun i => E i) := by
  obtain ⟨vb, hgraph⟩ := common_boundary_of_coherent_prefixes u₀ v₀ U V hcompat
  let B' := fun N => transportBoundary (B N) vb (hgraph N)
  refine ⟨vb, B', hgraph, (fun _ _ => rfl), ?_⟩
  intro N n
  have hfirst (i : Fin (N + 1)) : u₀ ≤ (B N).cuts i :=
    (B N).first.ge.trans ((B N).ordered (Fin.zero_le i))
  have hlast (i : Fin (N + 1)) : (B N).cuts i ≤ U N :=
    ((B N).ordered (Fin.le_last i)).trans (B N).last.le
  have heq (u : ℝ) (hu : u ∈ Icc ((B N).cuts n.castSucc) ((B N).cuts n.succ)) :
      vb u = V N u := hgraph N ⟨(hfirst _).trans hu.1, hu.2.trans (hlast _)⟩
  refine ⟨(hE N n).1, ?_, ?_⟩
  · intro u hu
    change S.m u (vb u) / S.r u (vb u) +
      ‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖ ^ 2 ≤ E n
    rw [heq u hu]
    exact (hE N n).2.1 u hu
  · change (∫ u in (B N).cuts n.castSucc..(B N).cuts n.succ,
        (‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖ ^ 2 +
         ‖S.xi u (vb u) / (S.nu u (vb u) : ℂ)‖ ^ 2 + S.mu u (vb u) ^ 2) *
          (-S.nu u (vb u)) / S.r u (vb u)) ≤ E n
    convert (hE N n).2.2 using 1
    apply intervalIntegral.integral_congr
    intro u hu
    have horder := (B N).ordered (Fin.castSucc_le_succ n)
    rw [uIcc_of_le horder] at hu
    dsimp only
    rw [heq u hu]

end EmcsfAcExtension.Global.Closure
