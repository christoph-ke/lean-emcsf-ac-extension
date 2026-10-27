module

public import EmcsfAcExtension.Global.Closure.Windows
public import EmcsfAcExtension.Global.Closure.Absorption
public import EmcsfAcExtension.Global.Closure.Stages
import EmcsfAcExtension.Global.Interaction.ConnectorBudget
import EmcsfAcExtension.Global.Interaction.PairKernel
import EmcsfAcExtension.Global.Interaction.PairTonelli
import EmcsfAcExtension.Global.Interaction.WrappersSource
import EmcsfAcExtension.Global.Cooling.Full
import EmcsfAcExtension.Global.Cooling.ObservationDischarge
import EmcsfAcExtension.Global.Observation.Energy
import Mathlib.Tactic

/-! # Energy transfer on the actual incoming connector

The connector's fixed factor is chosen before entry and before all fields.
Its source majorant, scalar profile and charged scale come from the same
weakly stopped finite prefix used by the budget and strict-stop consumers.
Source: `charged_SF_new_version.tex:L3908–L3922`.
-/

public section

open Set Filter Topology MeasureTheory

namespace EmcsfAcExtension.Global.Closure

/-- [internal]
Cooling and the actual constant-label connector propagate the starting
observation energy on every completed cylinder, including every partial
connector endpoint. The only analytic inputs are the same weak stops,
late gap, entry interaction bound and charged margins as in
`stopped_boundary_budgets_of_initial_energies`. Covariant AC, observation
windows, the scalar profile and source majorant are all discharged here.
The thresholds depend only on `δ`; `H,C₁` depend only on `δ,εweak,ρ,χ`.
All are chosen before the solution, coupling, entry row and every stage.
Source: `charged_SF_new_version.tex:L3908–L3917`, `charged_SF_new_version.tex:L4086–L4102`. -/
theorem stopped_connector_recurrence (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    ∃ Ts δs ηs : ℝ, 0 < Ts ∧ 0 < δs ∧ 0 < ηs ∧
      ∀ (εweak ρ χ : ℝ), 0 ≤ εweak → 0 < ρ → 0 < χ →
      ∃ H C₁ : ℝ, 0 < H ∧ 0 < C₁ ∧
      ∀ (ui e u₀ u₁ v₀ R₀ c Λ F Jstop εn : ℝ) (S : Fields)
        (vb : ℝ → ℝ) (N : ℕ) (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) (n : Fin N),
      OriginalData ui e S → ExteriorBox δ c Λ F εweak ρ → 0 ≤ Jstop → 0 < εn →
      F + εweak ≤ δs →
      ExteriorStops S (exteriorDomain ui u₀ u₁ vb) δ c Λ F εweak →
      S.r u₀ 0 = R₀ → (∀ u ∈ Icc u₀ u₁, R₀ / 2 ≤ S.r u 0) →
      (interactionNorm e S (exteriorDomain ui u₀ u₁ vb) u₀ v₀).toReal ≤ Jstop →
      (∀ p ∈ origDomain ui, u₀ ≤ p.1 → 0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) →
      B.radii n < R₀ / 2 →
      ∀ γ : ClockCylinder S (origDomain ui) (B.radii n) 0 (H * B.radii n / εn),
      (γ.U 0 = B.cuts n.castSucc ∧ γ.U (H * B.radii n / εn) = B.cool n) →
      (∀ τ ∈ Icc 0 (H * B.radii n / εn), vb (γ.U τ) = γ.V τ) →
      cylinderEnergy S (B.radii n) (γ.U 0) (γ.V 0) / B.radii n ≤ εn →
      let z := Local.sigma e (Interaction.scalarBackground ui R₀ c F Jstop S) (2 * R₀)
      z ≤ 1 → 9 * z ≤ ηs ^ 2 →
      ∀ x ∈ Icc (B.cool n) (B.cuts n.succ),
        cylinderEnergy S (S.r x (vb x)) x (vb x) / S.r x (vb x) ≤
          χ * εn + C₁ * (curveCovVar e S S.a γ.U γ.V 0 (H * B.radii n / εn)).toReal ^ 2 := by
  obtain ⟨Ts, δs, ηs, hTs, hδs, hηs, hsteps⟩ :=
    cc_recurrence_of_estimates δ hδ (Cooling.observation_input δ hδ)
  refine ⟨Ts, δs, ηs, hTs, hδs, hηs, ?_⟩
  intro εweak ρ χ hεweak hρ hχ
  obtain ⟨K, d, H, Cd, C₁, _hK, _hd, hH, _hCd, hC₁, _hcontract, hstep⟩ :=
    hsteps εweak ρ χ hεweak hρ hχ
  refine ⟨H, C₁, hH, hC₁, ?_⟩
  intro ui e u₀ u₁ v₀ R₀ c Λ F Jstop εn S vb N B n h hbox hJstop he hweak
    hstop hR₀ hretained hJ hgap hRn γ hends hgraph henergy
  dsimp only
  intro hz1 hzη
  have data := stopped_profile_data h B hbox hstop hR₀ hretained hJ
  have hT : 0 < H * B.radii n / εn := div_pos (mul_pos hH (B.radius_pos n)) he
  have hfirst (i : Fin (N + 1)) : u₀ ≤ B.cuts i :=
    B.first.ge.trans (B.ordered (Fin.zero_le i))
  have hlast (i : Fin (N + 1)) : B.cuts i ≤ u₁ :=
    (B.ordered (Fin.le_last i)).trans B.last.le
  have hcool : B.cool n ∈ Icc u₀ u₁ :=
    ⟨(hfirst _).trans (B.split n).1, (B.split n).2.trans (hlast _)⟩
  have hsub : Icc (B.cool n) (B.cuts n.succ) ⊆ Icc u₀ u₁ :=
    Icc_subset_Icc hcool.1 (hlast _)
  have hcurve (τ : ℝ) (hτ : τ ∈ Icc 0 (H * B.radii n / εn)) :
      γ.U τ ∈ Icc u₀ u₁ ∧ (γ.U τ, γ.V τ) ∈ exteriorDomain ui u₀ u₁ vb := by
    have hm := (γ.strictMonoOn_U h.solution).monotoneOn
    have hl := hm (left_mem_Icc.mpr hT.le) hτ hτ.1
    have hr := hm hτ (right_mem_Icc.mpr hT.le) hτ.2
    rw [hends.1] at hl
    rw [hends.2] at hr
    have hu : γ.U τ ∈ Icc u₀ u₁ := ⟨(hfirst _).trans hl, hr.trans hcool.2⟩
    exact ⟨hu, γ.mem τ hτ, hu.1, hu.2, (hgraph τ hτ).le⟩
  have hterm (τ : ℝ) (hτ : τ ∈ Icc 0 (H * B.radii n / εn)) :
      B.radii n < S.r (γ.U τ) 0 := hRn.trans_le (hretained _ (hcurve τ hτ).1)
  let M := Interaction.scalarBackground ui R₀ c F Jstop S
  have hM : 1 ≤ M := data.one_le_background h ⟨le_rfl, hcool.1.trans hcool.2⟩
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hRpos : 0 < R₀ := data.radius_pos
  have hscale : 3 * (|e| * M * R₀) ≤ ηs := by
    apply (sq_le_sq₀ (by positivity) hηs.le).mp
    rw [ct_zeta] at hzη
    calc
      (3 * (|e| * M * R₀)) ^ 2 = 9 * (e ^ 2 * M ^ 2 * R₀ ^ 2) := by
        simp only [mul_pow, sq_abs]
        ring
      _ ≤ ηs ^ 2 := hzη
  have hweak' (τ : ℝ) (hτ : τ ∈ Icc 0 (H * B.radii n / εn)) :
      S.mu (γ.U τ) (γ.V τ) +
        ‖S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)‖ ≤ δs := by
    have hp := hcurve τ hτ
    have hs := hstop _ hp.2
    have hmu : S.mu (γ.U τ) (γ.V τ) ≤ εweak := by
      apply le_trans _ hs.2.2.2.2.2.1
      apply (le_div_iff₀ (h.solution.one_sub_mu_pos _ hp.2.1)).mpr
      nlinarith only [sq_nonneg (S.mu (γ.U τ) (γ.V τ))]
    exact (add_le_add hmu hs.2.2.2.2.1).trans (by linarith only [hweak])
  have hwindows (τ : ℝ) (hτ : τ ∈ Icc (Ts * B.radii n) (H * B.radii n / εn - Ts * B.radii n)) :
      triangle (γ.U (τ - Ts * B.radii n)) (γ.V (τ + Ts * B.radii n)) ⊆ origDomain ui ∧
      (∀ p ∈ triangle (γ.U (τ - Ts * B.radii n)) (γ.V (τ + Ts * B.radii n)),
        0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) ∧
      |e| * B.radii n * (1 + ‖S.a (γ.U τ) (γ.V τ)‖) ≤ ηs := by
    have hw := observation_window_regions h γ (B.radius_pos n) hTs.le
      (by rw [hends.1]; exact hfirst _) hterm hgap τ hτ
    have hwidth := mul_nonneg hTs.le (B.radius_pos n).le
    have hτ' : τ ∈ Icc 0 (H * B.radii n / εn) :=
      ⟨hwidth.trans hτ.1, hτ.2.trans (sub_le_self _ hwidth)⟩
    have hp := hcurve τ hτ'
    refine ⟨hw.1, hw.2, ?_⟩
    exact (observation_physical_scale_of_profile (B.radius_pos n).le
      (hRn.le.trans (half_le_self data.radius_pos.le)) hM hbox.2.2.2.2.2.1.le
      (ct_m0 h data _ hp.2) (hstop _ hp.2).2.2.2.2.1).2.trans hscale
  obtain ⟨_, hg, hg0, _, _, _⟩ := incoming_envelope h B
  let g := fun v => (incomingEnvelope e S (exteriorDomain ui u₀ u₁ vb) u₀ v).toReal
  have hv := InteractionEstimate.finite_boundary_label_bounds B _ hcool
  have hg' : IntegrableOn g (Icc (vb (B.cool n)) 0) :=
    hg.mono_set (Icc_subset_Icc hv.1 le_rfl)
  have hmajor (u : ℝ) (hu : u ∈ Icc (B.cool n) (B.cuts n.succ)) :
      ∀ᵐ w ∂volume.restrict (Icc (vb (B.cool n)) 0), ‖weightedJ S u w‖ ≤ g w := by
    filter_upwards [(data.majorant u (hsub hu)).filter_mono (ae_mono (Measure.restrict_mono
      (Icc_subset_Icc hv.1 le_rfl) le_rfl)), ae_restrict_mem measurableSet_Icc] with w hw hwm
    apply hw
    rw [B.connector n u hu]
    exact hwm.1
  have hJg : (∫ w in vb (B.cool n)..0, g w) ≤ Jstop := by
    have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le (hv.1.trans hv.2)).mpr hg
    exact (intervalIntegral.integral_mono_interval hv.1 hv.2 le_rfl
      (Eventually.of_forall hg0) hi).trans data.budget
  intro x hx
  have hlocal : ExteriorStops S
      (exteriorDomain ui (B.cool n) x (fun _ => vb (B.cool n))) δ c Λ F εweak := by
    intro p hp
    have hu : p.1 ∈ Icc (B.cool n) (B.cuts n.succ) := ⟨hp.2.1, hp.2.2.1.trans hx.2⟩
    apply hstop p ⟨hp.1, (hsub hu).1, (hsub hu).2, ?_⟩
    rw [B.connector n p.1 hu]
    exact hp.2.2.2
  have hs := hstep c Λ F ui e (B.radii n) εn x
    (Interaction.terminalScalarSup ui R₀ S) Jstop R₀ S g hbox.2.2.1
    hbox.2.2.2.2.1 hbox.2.2.2.2.2.1 (B.radius_pos n) he hJstop
    (hRn.le.trans (half_le_self data.radius_pos.le)) h γ
    (Cylinder.ac_curveParallel_a h.solution γ (B.radius_pos n) hT.le)
    hweak' hwindows henergy
  dsimp only at hs
  rw [← hgraph _ (right_mem_Icc.mpr hT.le), hends.2] at hs
  have hbv : x < vb (B.cool n) := by
    simpa only [B.connector n x hx] using B.off_axis x (hsub hx)
  have hr := hs hx.1 hbv
    (fun u hu => by simpa only [B.connector n u ⟨hu.1, hu.2.trans hx.2⟩] using
      (B.radius_range n u ⟨(B.split n).1.trans hu.1, hu.2.trans hx.2⟩).1)
    hlocal
    (fun u hu w hw => (hgap (u, w)
      (data.core_segment (hsub ⟨hu.1, hu.2.trans hx.2⟩) ⟨rfl, hw⟩)
      (hsub ⟨hu.1, hu.2.trans hx.2⟩).1).2)
    (fun u hu => Interaction.terminal_scalar_le_sup h data.radius_pos
      ⟨(B.mem u (hsub ⟨hu.1, hu.2.trans hx.2⟩)).1,
        (B.mem u (hsub ⟨hu.1, hu.2.trans hx.2⟩)).2.1⟩
      (data.annulus u (hsub ⟨hu.1, hu.2.trans hx.2⟩)))
    hg' (Eventually.of_forall hg0)
    (fun u hu => hmajor u ⟨hu.1, hu.2.trans hx.2⟩) hJg
    (by simpa only [ct_zeta, Interaction.scalarBackground] using hz1)
  simpa only [B.connector n x hx] using hr

end EmcsfAcExtension.Global.Closure
