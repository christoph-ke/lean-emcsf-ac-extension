module

public import EmcsfAcExtension.Global.Assembly.Inputs
public import EmcsfAcExtension.Global.Defs.Interaction
import EmcsfAcExtension.Global.Closure.FinalEntry
import EmcsfAcExtension.Global.Closure.FinalAdvance
import EmcsfAcExtension.Global.Closure.FinalAssembly
import EmcsfAcExtension.Global.Gap.LateMain
import Mathlib.Tactic

/-! # Closure families retaining the literal initial density

Retain the proper entry family from the unconditional construction of
`closure_obligations`. The same finite estimates and coherent-prefix
assembly now keep the literal initial interaction in the closed bound.
Source: `charged_SF_new_version.tex:L3873–L3876`, `charged_SF_new_version.tex:L4047–L4115`.
-/

public section

open Set Filter Topology

namespace EmcsfAcExtension.Global.Closure

/-- [internal]
Produce common closure families with their literal initial-density bound.
The constants depend on the fixed development and its geometric, stopping
and connector choices; they precede the energy tolerance, shrinking entry
row, stage number and all durations. The proper family `ell,V` is the one
used by the construction, and its literal initial density tends to zero.
No construction or analytic estimate is assumed. -/
theorem closure_families_with_initial_density
    (ui e : ℝ) (S : Fields) (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) :
    ∃ c F A : ℝ, 0 < c ∧ F ^ 2 < 1 ∧ 0 < A ∧
    ∃ Camp εmax : ℝ, ∃ ell V M : ℝ → ℝ,
      1 ≤ Camp ∧ 0 < εmax ∧
      Tendsto (fun u => (initialInteraction S u (V u)).toReal) (𝓝[<] 0) (𝓝 0) ∧
      (∀ u, M u = Camp * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) ∧
      (∀ᶠ u in 𝓝[<] (0 : ℝ), u < V u ∧ V u < 0 ∧
        S.r u (V u) = ell (S.r u 0) ∧
        0 < ell (S.r u 0) ∧ ell (S.r u 0) < S.r u 0) ∧
      Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0) ∧
      (∀ ε₀ ∈ Ioc 0 εmax, ∀ᶠ u₀ in 𝓝[<] (0 : ℝ),
        ∃ ρ b₀ K : ℝ, ∃ U : ℕ → ℝ, ∃ vb : ℝ → ℝ,
        ∃ B : ∀ N, FiniteBoundary S ui u₀ (U N) (V u₀) ρ vb N,
        ∃ E J : ℕ → ℝ,
          (0 ≤ ρ ∧ ρ < 1) ∧ Monotone U ∧ (∀ N i, (B N).cuts i = U i) ∧
          (∀ n, S.r u₀ 0 / 2 ≤ S.r (U n) 0) ∧
          (∀ n, S.r (U n) (vb (U n)) = stageRadius ρ b₀ n) ∧
          (∀ N, BoundaryBudgets S ui u₀ (U N) (V u₀) ρ vb N (B N) (fun i => E i)) ∧
          (∀ N, ∑ n ∈ Finset.range N, E n ≤ K) ∧
          (∀ n, ‖S.phi (U n) (vb (U n))‖ ≤ M u₀) ∧
          (∀ n, J n ≤ A * ((initialInteraction S u₀ (V u₀)).toReal + ε₀ +
            e ^ 2 * M u₀ ^ 2 * S.r u₀ 0 ^ 2)) ∧
          (∀ n, (1 - F ^ 2) *
            (eVariationOn (S.a (U n)) (Icc (vb (U n)) 0)).toReal ≤ c⁻¹ * J n +
              F ^ 2 * ‖S.theta (U n) (vb (U n)) /
                (S.lam (U n) (vb (U n)) : ℂ)‖)) := by
  have hδ : 0 < gapConstant / 2 ∧ gapConstant / 2 < 1 := by
    have hx : Real.exp (-32 : ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    unfold gapConstant
    constructor
    · positivity
    · linarith only [hx]
  obtain ⟨δs, ηs, hδs, hηs, hchoices⟩ := actual_cutoff_callback_of_small_entry
    (gapConstant / 2) hδ
  obtain ⟨ell, V, a₀, ha₀, c, Λ, F, εweak, hc, hΛ, hcΛ, hF, hεweak, hupper,
    hroot, hRa, hproper, hratiolimit, hadaptive, hboxes, hweak, hD, hentry⟩ :=
    proper_entry_stop_initialization ui e (δs / 4) (δs / 4) S h hs
      (by positivity) (by positivity)
  let ρ : ℝ := 1 / 4
  let χ : ℝ := 1 / 2
  have hρ : 0 < ρ ∧ ρ < 1 := by norm_num [ρ]
  have hχ : 0 < χ ∧ χ < 1 := by norm_num [χ]
  have hρχ : ρ < χ := by norm_num [ρ, χ]
  have hbox := hboxes ρ hρ
  have hweaknum : F + εweak ≤ δs := weak_box_margin_of_initialization hbox hδs
    (fun μ x hμ hμ1 hratio hx => (hweak μ x hμ hμ1 hratio hx).1)
  obtain ⟨H, C₁, Cbudget, Csum, hH, hC₁, hCbudget, hCsum, hstops⟩ :=
    hchoices εweak ρ χ hεweak hρ.1 hχ
  obtain ⟨εabs, εrun, q, A, hεabs, hεrun, hq, hA, hrun, hdata⟩ :=
    hstops c Λ F hbox hF hweaknum
  obtain ⟨alate, halate, hcallback⟩ := hdata ui e S h hs
  obtain ⟨agap, hagap, hgap⟩ := Gap.late_from_terminal ui e S h hs
  obtain ⟨C, hC, hbackground⟩ := canonical_background_logarithmic ui e c F εabs S h hs
    hc hF.le hbox.2.2.2.2.2.1 hεabs.le
  let D := fun u => ∫ v in V u..0, ‖weightedJ S u v‖
  let M := fun u => C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))
  let εmax := min 1 (q / 3)
  have hεmax : 0 < εmax := by dsimp [εmax]; positivity
  have hF2 : F ^ 2 < 1 := by
    have hm := hbox.2.2.2.2.2.2.2.1
    have hh : (1 / 2 : ℝ) ≤ max εweak (1 / 2) := le_max_right _ _
    linarith only [hm, hh]
  have hroot' : ∀ᶠ u in 𝓝[<] (0 : ℝ), u < V u ∧ V u < 0 ∧
      S.r u (V u) = ell (S.r u 0) ∧
      0 < ell (S.r u 0) ∧ ell (S.r u 0) < S.r u 0 := by
    filter_upwards [Ioo_mem_nhdsLT ha₀.2] with u hu
    exact hroot u ⟨hu.1.le, hu.2⟩
  have hDliteral : Tendsto (fun u => (initialInteraction S u (V u)).toReal)
      (𝓝[<] 0) (𝓝 0) := by
    apply hD.congr'
    filter_upwards [Ioo_mem_nhdsLT ha₀.2] with u hu
    have hv := hroot u ⟨hu.1.le, hu.2⟩
    have hrow : outSeg u (V u) 0 ⊆ origDomain ui := by
      rintro ⟨x, v⟩ ⟨rfl, hvl, hvr⟩
      exact ⟨ha₀.1.le.trans hu.1.le, hu.2, hv.1.le.trans hvl, hvr⟩
    rw [initialInteraction_eq h.solution hv.1 hv.2.1.le hrow,
      ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg hv.2.1.le
        (fun _ _ => norm_nonneg _))]
  refine ⟨c, F, A, hc, hF2, hA, C, εmax, ell, V, M, hC, hεmax,
    hDliteral, (fun _ => rfl), hroot', hratiolimit, ?_⟩
  intro ε₀ hε₀
  have he : 0 < ε₀ := hε₀.1
  have he1 : ε₀ ≤ 1 := hε₀.2.trans (min_le_left _ _)
  have heq : ε₀ ≤ q / 3 := hε₀.2.trans (min_le_right _ _)
  have hq3 : 0 < q / 3 := by positivity
  filter_upwards [hentry εrun ε₀ H ρ χ C (q / 3) hεrun he he1 hH.le hρ.1 hρχ hq3,
    Ioo_mem_nhdsLT halate.2, Ioo_mem_nhdsLT hagap.2,
    hD.eventually (Iio_mem_nhds hq3)] with a ha halate_a hagap_a hDa
  obtain ⟨ha₀a, hbsmall, hentryV, hentrylam, henergy, hclocksmall, hcharged⟩ := ha
  let R₀ := S.r a 0
  let v₀ := V a
  let b₀ := ell R₀
  let Kclock := H * b₀ / (ε₀ * (1 - ρ / χ)) + b₀
  let ζ := Local.sigma e (Interaction.scalarBackground ui R₀ c F εabs S) (2 * R₀)
  have hui : ui ≤ a := ha₀.1.le.trans ha₀a.1.le
  have hv := hroot a ⟨ha₀a.1.le, ha₀a.2⟩
  have hp : (a, v₀) ∈ origDomain ui := ⟨hui, ha₀a.2, hv.1.le, hv.2.1.le⟩
  have hRpos : 0 < R₀ := h.solution.r_pos (a, 0) ⟨hui, ha₀a.2, ha₀a.2.le, le_rfl⟩ ha₀a.2
  have hb₀ : 0 < b₀ := hv.2.2.2.1
  have henergy' : cylinderEnergy S (S.r a v₀) a v₀ / S.r a v₀ ≤ ε₀ := by
    change cylinderEnergy S (S.r a (V a)) a (V a) / S.r a (V a) ≤ ε₀
    rw [hv.2.2.1]
    exact henergy
  have hrow : outSeg a v₀ 0 ⊆ origDomain ui := by
    rintro ⟨u, v⟩ ⟨rfl, hv₀, hvzero⟩
    exact ⟨hui, ha₀a.2, hv.1.le.trans hv₀, hvzero⟩
  have hDreal : (initialInteraction S a v₀).toReal = D a := by
    rw [initialInteraction_eq h.solution hv.1 hv.2.1.le hrow,
      ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg hv.2.1.le
        (fun _ _ => norm_nonneg _))]
  have hBM : Interaction.scalarBackground ui R₀ c F εabs S ≤ M a :=
    (hbackground a ⟨hui, ha₀a.2⟩).2
  have hBnonneg : 0 ≤ Interaction.scalarBackground ui R₀ c F εabs S :=
    scalar_background_nonneg_at_entry h ⟨hui, ha₀a.2⟩ hRpos hc hF.le hF2 hεabs.le
  have hζ : ζ ≤ e ^ 2 * M a ^ 2 * R₀ ^ 2 := charged_error_le_of_background hBnonneg hBM
  have hsmall : (initialInteraction S a v₀).toReal + ε₀ + ζ ≤ q := by
    rw [hDreal]
    linarith only [hDa, heq, hζ, hcharged]
  have hconstant := constant_entry_of_proper_initialization hentryV
  have hgap' (p : ℝ × ℝ) (hpo : p ∈ origDomain ui) (hap : a ≤ p.1) :
      0 ≤ S.mu p.1 p.2 ∧ gapConstant / 2 ≤ 1 - S.mu p.1 p.2 :=
    ⟨(h.mu p hpo).1, (hgap p hpo (hagap_a.1.le.trans hap)).1⟩
  have hpath_data (b : ℝ) (vb : ℝ → ℝ) (σ : ℕ → ℝ) (N : ℕ)
      (B : FiniteBoundary S ui a b v₀ ρ vb N) (T : Fin N → ℝ)
      (hT : ∀ n, 0 < T n)
      (hradii : ∀ n : Fin N, B.radii n = stageRadius ρ b₀ n)
      (hshort : ∀ n : Fin N, T n ≤ H * B.radii n / energyEnvelope χ C₁ ε₀ σ n)
      (hprior : ∀ n : Fin N, n.val + 1 < N →
        T n = H * B.radii n / energyEnvelope χ C₁ ε₀ σ n)
      (γ : ∀ n, ClockCylinder S (origDomain ui) (B.radii n) 0 (T n))
      (hends : ∀ n, (γ n).U 0 = B.cuts n.castSucc ∧ (γ n).U (T n) = B.cool n)
      (hgraph : ∀ n, ∀ s ∈ Icc 0 (T n), vb ((γ n).U s) = (γ n).V s)
      (hσ : ∀ n : Fin N, σ n = (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal) :
      StrictFiniteCutoffStops S ui a R₀ vb
        (fun _ => (interactionNorm e S (exteriorDomain ui a b vb) a v₀).toReal)
        (fun _ => ∑ n, (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal)
        (gapConstant / 2) c Λ F εweak εrun b ∧
      (0 < N →
        (interactionNorm e S (exteriorDomain ui a b vb) a v₀).toReal +
          (∑ n, (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal) ≤
            A * ((initialInteraction S a v₀).toReal + ε₀ + ζ) ∧
        BoundaryBudgets S ui a b v₀ ρ vb N B (fun n => stageBudget Cbudget χ C₁ ε₀ σ n) ∧
        (∑ n : Fin N, stageBudget Cbudget χ C₁ ε₀ σ n) ≤ Csum * (ε₀ +
          (∑ n, (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal) ^ 2) ∧
        (∑ n : Fin N, Real.sqrt (stageBudget Cbudget χ C₁ ε₀ σ n)) ≤ Csum *
          (Real.sqrt ε₀ + ∑ n, (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal)) := by
    have hclock : cylinderClock S vb a b ≤ Kclock :=
      total_boundary_clock_of_duration_le h.solution B hH ⟨hρ.1, hρχ⟩ hχ hC₁.le he hb₀ σ
        hradii T hT (fun n => by simpa only [stageDuration, ← hradii n] using hshort n)
        γ hends hgraph
    have hRn (n : Fin N) : B.radii n < R₀ / 2 := by
      rw [hradii n]
      exact (mul_le_of_le_one_left hb₀.le (pow_le_one₀ hρ.1.le hρ.2.le)).trans_lt hbsmall
    have hentryB := strict_entry_of_initial h B T γ hconstant
    obtain ⟨hcb, hest⟩ := hcallback a b v₀ R₀ ε₀ Kclock vb σ N B T
      halate_a.1.le he rfl hgap' hRn hT hprior γ hends hgraph hσ henergy' hentrylam
      hclock hclocksmall hsmall hentryB
    have hfixed (p : ℝ × ℝ) (hpo : p ∈ exteriorDomain ui a b vb) :
        0 ≤ S.mu p.1 p.2 ∧ gapConstant / 2 ≤ 1 - S.mu p.1 p.2 ∧
        S.lam p.1 p.2 ≤ Λ ∧ S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 ≤ S.mu p.1 p.2 / 2 :=
      ⟨(h.mu p hpo.1).1, (hgap p hpo.1 (hagap_a.1.le.trans hpo.2.1)).1,
        hupper p hpo.1, (hgap p hpo.1 (hagap_a.1.le.trans hpo.2.1)).2⟩
    have hfull := strict_full_path_of_callback h B T (fun n => (hT n).le)
      γ hends hgraph hfixed hconstant hcb
    refine ⟨hfull, ?_⟩
    intro hN
    apply hest hN
    have hweakB : FiniteCutoffStops S ui a R₀ vb
        (fun _ => (interactionNorm e S (exteriorDomain ui a b vb) a v₀).toReal)
        (fun _ => ∑ n, (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal)
        (gapConstant / 2) c Λ F εweak εrun b :=
      ⟨hfull.1, (fun u hu => (hfull.2.2.1 u hu).le), hfull.2.2.2.le⟩
    simpa only [FiniteCutoffStops,
      clipped_variation_final h B T (fun n => (hT n).le) γ hends hgraph] using hweakB
  obtain ⟨P₀⟩ : Nonempty (FinalPrefix S ui e a v₀ ρ b₀ H χ C₁ ε₀ R₀
      (gapConstant / 2) c Λ F εweak εrun 0) :=
    initial_final_prefix hp hv.1 hv.2.2.1 hconstant
  have hpaths := fun b vb σ N B T hT hradii hshort hprior γ hends hgraph hσ =>
    (hpath_data b vb σ N B T hT hradii hshort hprior γ hends hgraph hσ).1
  have hstep (N : ℕ)
      (P : FinalPrefix S ui e a v₀ ρ b₀ H χ C₁ ε₀ R₀ (gapConstant / 2) c Λ F εweak εrun N) :=
    final_prefix_extension_of_stopped_paths h (ha₀.1.trans ha₀a.1) hρ hb₀ hbsmall
      hH hχ.1 hC₁.le he hpaths N P
  obtain ⟨P, hP₀, hU, hgraphs, hcuts, hvars⟩ := coherent_final_prefixes_of_extension P₀
    (fun N P => by
      obtain ⟨Q, hinc, hgraph, hcuts, hstages, hvar, hcurves⟩ := hstep N P
      exact ⟨Q, hinc, hgraph, hcuts, hvar⟩)
  have hest (N : ℕ) (hN : 0 < N) :=
    ((hpath_data (P N).endpoint (P N).graph (P N).variation N (P N).boundary
      (P N).duration (P N).duration_pos (P N).radii_eq
      (fun n => ((P N).duration_eq n).le) (fun n _ => (P N).duration_eq n)
      (P N).cylinders (P N).ends (P N).on_graph (P N).variation_eq).2 hN)
  have herr : (initialInteraction S a v₀).toReal + ε₀ + ζ ≤
      (initialInteraction S a v₀).toReal + ε₀ + e ^ 2 * M a ^ 2 * R₀ ^ 2 :=
    add_le_add le_rfl hζ
  obtain ⟨K, U, vb, B, E, J, hresult⟩ := closure_entry_of_coherent_prefixes h hbox
    ⟨hρ.1.le, hρ.2⟩ he.le hA.le hCsum.le ⟨hεrun.le, hrun⟩ rfl hBM herr
    P hgraphs hcuts hvars (fun N hN =>
      ⟨(hest N hN).1, (hest N hN).2.1, (hest N hN).2.2.1⟩)
  exact ⟨ρ, b₀, K, U, vb, B, E, J, hresult⟩


end EmcsfAcExtension.Global.Closure
