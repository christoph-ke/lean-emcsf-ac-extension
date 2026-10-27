module

public import EmcsfAcExtension.Global.Defs.Renormalized
public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Defs.Domains
import EmcsfAcExtension.Global.Exterior.ScalarEnergy
import EmcsfAcExtension.Global.Terminal.OpticalUpper
import EmcsfAcExtension.Global.Api.Definitions
import EmcsfAcExtension.Infra.AC.Variation

/-! # The outgoing exterior interaction norm

The cubic estimate and the initial norm use the original gauge and only an
L¹ derivative of the AC normalized scalar. All integrals use the outgoing
label; the factor `λ` is precisely the radial Jacobian. Source:
`charged_SF_new_version.tex:L1427–1457`, approved internal project record, (J1).
-/

public section

open Set MeasureTheory Filter Topology Complex

namespace EmcsfAcExtension.Global.Entry

variable {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}

/-- [def-node sec:charged-step7#exterior-interaction-variable]
The exterior interaction variable is exactly frozen `jOut`; no second
interaction field is introduced (`charged_SF_new_version.tex:L1427–1435`). -/
theorem exterior_interaction_variable (S : Fields) (u v : ℝ)
    (hl : S.lam u v ≠ 0) :
    jOut S u v = (1 - S.mu u v) * S.lam u v *
      (alphaPrime S u v - (1 / S.r u v : ℝ) *
        ‖S.theta u v / S.lam u v‖ ^ 2 * (S.theta u v / S.lam u v)) :=
  Global.jOut_eq S u v hl

/-- [internal] Cancel the positive gap in the weighted interaction
variable, retaining both factors of the outgoing expansion in its cubic
term. This is a literal identity, including at exceptional derivative labels. -/
theorem weightedJ_eq (S : Fields) (u v : ℝ) (hg : 1 - S.mu u v ≠ 0) :
    weightedJ S u v = (S.lam u v : ℂ) *
      (deriv (S.a u) v - S.lam u v / S.r u v *
        ‖S.theta u v / S.lam u v‖ ^ 2 * (S.theta u v / S.lam u v)) := by
  unfold weightedJ jOut
  push_cast
  have hgc : (1 : ℂ) - (S.mu u v : ℂ) ≠ 0 := by exact_mod_cast hg
  rw [← mul_assoc, div_mul_cancel₀ _ hgc]

private theorem continuousOn_field (hS : IsSolution e S D) {u a b : ℝ}
    (hs : outSeg u a b ⊆ D) :
    ContinuousOn (fun v => S.theta u v / (S.lam u v : ℂ)) (Icc a b) :=
  (Calculus.continuousOn_out_section hS.cont_theta hs).div
    (Complex.continuous_ofReal.comp_continuousOn
      (Calculus.continuousOn_out_section hS.cont_lam hs))
    (fun v hv => Complex.ofReal_ne_zero.mpr (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)).ne')

/-- [internal] The cubic radial integral is bounded by the scalar energy.
The coefficient `1` is universal, uniformly in the solution, coupling,
row, positive lower radius `l`, and field upper bound `F`. No pointwise
bound on the AC derivative enters. -/
theorem exterior_cubic_interaction_bound_of_energy (hS : IsSolution e S D)
    {u a l F E : ℝ} (ha : a ≤ 0) (hl : 0 < l)
    (hs : outSeg u a 0 ⊆ D)
    (hr : ∀ v ∈ Icc a 0, l ≤ S.r u v)
    (hF : ∀ v ∈ Icc a 0, ‖S.theta u v / (S.lam u v : ℂ)‖ ≤ F)
    (hE : (∫ v in a..0, ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v) ≤ E) :
    (∫ v in a..0, ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 3 /
      S.r u v * S.lam u v) ≤ F * E / l := by
  have cy := (continuousOn_field hS hs).norm
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have hrp : ∀ v ∈ Icc a 0, 0 < S.r u v := fun v hv => hl.trans_le (hr v hv)
  have hcub := ((cy.pow 3).div cr (fun v hv => (hrp v hv).ne')).mul cl
  have hi := hcub.intervalIntegrable_of_Icc (μ := volume) ha
  have he := ((cy.pow 2).mul cl).intervalIntegrable_of_Icc (μ := volume) ha
  have hF0 : 0 ≤ F := (norm_nonneg _).trans (hF a ⟨le_rfl, ha⟩)
  calc
    _ ≤ ∫ v in a..0, (F / l) *
        (‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v) := by
      apply intervalIntegral.integral_mono_on ha hi (he.const_mul (F / l))
      intro v hv
      have hv' := hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)
      have hd : ‖S.theta u v / (S.lam u v : ℂ)‖ / S.r u v ≤ F / l :=
        div_le_div₀ hF0 (hF v hv) hl (hr v hv)
      have hh := mul_le_mul_of_nonneg_right hd
        (mul_nonneg (sq_nonneg ‖S.theta u v / (S.lam u v : ℂ)‖) hv'.le)
      dsimp only [Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
      convert hh using 1
      ring
    _ = (F / l) * ∫ v in a..0,
        ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ (F / l) * E := mul_le_mul_of_nonneg_left hE (div_nonneg hF0 hl.le)
    _ = _ := by ring

/-- [internal] Rowwise initial interaction estimate, including L¹
integrability of the exact frozen expression. The numerical coefficients
are universal; `L` is any expansion upper bound and `F` any normalized
field upper bound on this row. The source derivative is used only in L¹. -/
theorem small_initial_interaction_norm_of_energy (hS : IsSolution e S D)
    {u a l F E L : ℝ} (ha : a ≤ 0) (hl : 0 < l)
    (hs : outSeg u a 0 ⊆ D)
    (hr : ∀ v ∈ Icc a 0, l ≤ S.r u v)
    (hF : ∀ v ∈ Icc a 0, ‖S.theta u v / (S.lam u v : ℂ)‖ ≤ F)
    (hL : ∀ v ∈ Icc a 0, S.lam u v ≤ L)
    (hE : (∫ v in a..0, ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v) ≤ E) :
    IntervalIntegrable (weightedJ S u) volume a 0 ∧
      (∫ v in a..0, ‖weightedJ S u v‖) ≤
        L * (eVariationOn (S.a u) (Icc a 0)).toReal + L * F * E / l := by
  let y := fun v => S.theta u v / (S.lam u v : ℂ)
  let c := fun v => ((S.lam u v / S.r u v * ‖y v‖ ^ 2 : ℝ) : ℂ) * y v
  have cy : ContinuousOn y (Icc a 0) := continuousOn_field hS hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have hrp : ∀ v ∈ Icc a 0, 0 < S.r u v := fun v hv => hl.trans_le (hr v hv)
  have cc : ContinuousOn c (Icc a 0) :=
    (Complex.continuous_ofReal.comp_continuousOn
      ((cl.div cr (fun v hv => (hrp v hv).ne')).mul (cy.norm.pow 2))).mul cy
  have hac := (hS.ac_out u a 0 ha hs).2.2.2.2
  have hd := hac.intervalIntegrable_deriv_complex
  have hc := cc.intervalIntegrable_of_Icc (μ := volume) ha
  have hi := (hd.sub hc).continuousOn_mul
    (by simpa only [uIcc_of_le ha] using
      Complex.continuous_ofReal.comp_continuousOn cl)
  have heq (v : ℝ) (hv : v ∈ Icc a 0) :
      weightedJ S u v = (S.lam u v : ℂ) * (deriv (S.a u) v - c v) := by
    rw [weightedJ_eq S u v (hS.one_sub_mu_pos (u, v) (hs ⟨rfl, hv⟩)).ne']
    simp only [c, y, ofReal_mul, ofReal_div, ofReal_pow]
  have hiW : IntervalIntegrable (weightedJ S u) volume a 0 :=
    hi.congr (by
      intro v hv
      exact (heq v (by simpa only [uIcc_of_le ha] using uIoc_subset_uIcc hv)).symm)
  have hL0 : 0 ≤ L := (hS.lam_pos (u, a) (hs ⟨rfl, le_rfl, ha⟩)).le.trans
    (hL a ⟨le_rfl, ha⟩)
  have hcn (v : ℝ) (hv : v ∈ Icc a 0) :
      ‖c v‖ = ‖y v‖ ^ 3 / S.r u v * S.lam u v := by
    dsimp only [c]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg
        (div_nonneg (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)).le (hrp v hv).le)
        (sq_nonneg _))]
    ring
  have hb (v : ℝ) (hv : v ∈ Icc a 0) :
      ‖weightedJ S u v‖ ≤ L * ‖deriv (S.a u) v‖ + L * ‖c v‖ := by
    rw [heq v hv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩))]
    calc
      _ ≤ S.lam u v * (‖deriv (S.a u) v‖ + ‖c v‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _)
          (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)).le
      _ ≤ L * (‖deriv (S.a u) v‖ + ‖c v‖) :=
        mul_le_mul_of_nonneg_right (hL v hv) (add_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = _ := mul_add _ _ _
  refine ⟨hiW, ?_⟩
  calc
    _ ≤ ∫ v in a..0, L * ‖deriv (S.a u) v‖ + L * ‖c v‖ :=
      intervalIntegral.integral_mono_on ha hiW.norm
        ((hd.norm.const_mul L).add (hc.norm.const_mul L)) hb
    _ = L * (eVariationOn (S.a u) (Icc a 0)).toReal +
        L * ∫ v in a..0, ‖y v‖ ^ 3 / S.r u v * S.lam u v := by
      rw [intervalIntegral.integral_add (hd.norm.const_mul L) (hc.norm.const_mul L),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        hac.toReal_eVariationOn_eq_integral_norm_deriv ha]
      congr 2
      exact intervalIntegral.integral_congr (fun v hv => hcn v (uIcc_of_le ha ▸ hv))
    _ ≤ L * (eVariationOn (S.a u) (Icc a 0)).toReal + L * (F * E / l) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (exterior_cubic_interaction_bound_of_energy hS ha hl hs hr hF hE) hL0)
    _ = _ := by ring

/-- [internal]
The complete late-row estimate and its vanishing limit, with the
original outgoing variation and field decay supplied by internal project record.
`L` is any fixed uniform upper bound for `λ`. The coefficient `4` is
universal, uniformly in the development, coupling, profile and row.
Every density hypothesis is in the original gauge; no common complex
scalar limit is used (`charged_SF_new_version.tex:L1437–1457`). -/
theorem small_initial_interaction_norm_of_energy_and_density {ui uc L : ℝ}
    (h : OriginalData ui e S) (huc : uc < 0) (V ell F : ℝ → ℝ)
    (hrow : ∀ u ∈ Ico uc 0, (u, V u) ∈ origDomain ui)
    (hradius : ∀ u ∈ Ico uc 0, 0 < ell (terminalRadius S u) ∧
      ∀ v ∈ Icc (V u) 0, ell (terminalRadius S u) ≤ S.r u v)
    (hexpansion : ∀ u ∈ Ico uc 0, ∀ v ∈ Icc (V u) 0, S.lam u v ≤ L)
    (henergy : ∀ u ∈ Ico uc 0,
      (∫ v in V u..0, ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v) ≤
        4 * terminalMass S u)
    (hfield : ∀ u ∈ Ico uc 0, ∀ v ∈ Icc (V u) 0,
      ‖S.theta u v / (S.lam u v : ℂ)‖ ≤ F u)
    (hvariation : Tendsto (fun u => (eVariationOn (S.a u) (Icc (V u) 0)).toReal)
      (𝓝[<] 0) (𝓝 0))
    (hfieldDecay : Tendsto F (𝓝[<] 0) (𝓝 0))
    (hmassDecay : Tendsto (fun u => terminalMass S u / ell (terminalRadius S u))
      (𝓝[<] 0) (𝓝 0)) :
    (∀ u ∈ Ico uc 0, IntervalIntegrable (weightedJ S u) volume (V u) 0 ∧
      (∫ v in V u..0, ‖weightedJ S u v‖) ≤
        L * (eVariationOn (S.a u) (Icc (V u) 0)).toReal +
          4 * L * F u * (terminalMass S u / ell (terminalRadius S u))) ∧
      Tendsto (fun u => ∫ v in V u..0, ‖weightedJ S u v‖) (𝓝[<] 0) (𝓝 0) := by
  have hb (u : ℝ) (hu : u ∈ Ico uc 0) :
      IntervalIntegrable (weightedJ S u) volume (V u) 0 ∧
      (∫ v in V u..0, ‖weightedJ S u v‖) ≤
        L * (eVariationOn (S.a u) (Icc (V u) 0)).toReal +
          4 * L * F u * (terminalMass S u / ell (terminalRadius S u)) := by
    have hp := hrow u hu
    have hs : outSeg u (V u) 0 ⊆ origDomain ui :=
      (outSeg_subset_origDomain_iff hp.2.2.2).2 ⟨hp.1, hp.2.1, hp.2.2.1, le_rfl⟩
    obtain ⟨hi, he⟩ := small_initial_interaction_norm_of_energy h.solution hp.2.2.2
      (hradius u hu).1 hs (hradius u hu).2 (hfield u hu) (hexpansion u hu) (henergy u hu)
    exact ⟨hi, by convert he using 1; ring⟩
  refine ⟨hb, ?_⟩
  have hupper := (hvariation.const_mul L).add
    ((hfieldDecay.mul hmassDecay).const_mul (4 * L))
  simp only [mul_zero, zero_add] at hupper
  apply squeeze_zero' _ _ hupper
  · filter_upwards [Ioo_mem_nhdsLT huc] with u hu
    exact intervalIntegral.integral_nonneg (hrow u ⟨hu.1.le, hu.2⟩).2.2.2
      (fun _ _ => norm_nonneg _)
  · filter_upwards [Ioo_mem_nhdsLT huc] with u hu
    convert (hb u ⟨hu.1.le, hu.2⟩).2 using 1
    ring

private theorem row_radius_lower_bound {ui ub u a : ℝ}
    (h : OriginalData ui e S) {ell : ℝ → ℝ}
    (hp : (u, a) ∈ adaptiveExterior S ui ub ell) :
    ∀ v ∈ Icc a 0, ell (terminalRadius S u) ≤ S.r u v := by
  intro v hv
  exact hp.2.2.trans (Exterior.outgoing_radius_mono h hp.1.2.2.1 hv.1
    ((outSeg_subset_origDomain_iff hv.1).2
      ⟨hp.1.1, hp.1.2.1, hp.1.2.2.1, hv.2⟩))

private theorem scalar_energy_late {ui : ℝ}
    (h : OriginalData ui e S) (_ht : SignedTerminalBound ui S)
    (M ell : ℝ → ℝ) {R₀ : ℝ} (hR : 0 < R₀)
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0)) :
    ∃ ub ∈ Ioo ui 0, ∀ u a, (u, a) ∈ adaptiveExterior S ui ub ell →
      (∫ v in a..0, ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v) ≤
        4 * terminalMass S u := by
  have hRlim := Terminal.terminal_radius_collapse h.ui_neg h.solution h.mu
  obtain ⟨ub, hub, he⟩ := charged_exterior_scalar_energy_of_terminal
    h M ell hR hRlim hmass hell hsmall
  exact ⟨ub, hub, fun u a hp => (he u a hp).1⟩

/-- [node sec:charged-step7#exterior-cubic-interaction-bound]
The original signed terminal hypothesis and adaptive profile supply the
scalar energy bound; only the outgoing field upper bound is left free.
The coefficient `4` is universal, uniformly in every later row, inner
endpoint and upper bound `F` (`charged_SF_new_version.tex:L1449–1455`). -/
theorem exterior_cubic_interaction_bound {ui : ℝ}
    (h : OriginalData ui e S) (ht : SignedTerminalBound ui S)
    (M ell : ℝ → ℝ) {R₀ : ℝ} (hR : 0 < R₀)
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0)) :
    ∃ ub ∈ Ioo ui 0, ∀ u a l F,
      (u, a) ∈ adaptiveExterior S ui ub ell →
      0 < l → l ≤ ell (terminalRadius S u) →
      (∀ v ∈ Icc a 0, ‖S.theta u v / (S.lam u v : ℂ)‖ ≤ F) →
      (∫ v in a..0, ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 3 /
        S.r u v * S.lam u v) ≤ 4 * F * terminalMass S u / l := by
  obtain ⟨ub, hub, henergy⟩ := scalar_energy_late h ht M ell hR hmass hell hsmall
  refine ⟨ub, hub, ?_⟩
  intro u a l F hp hl hle hF
  have hs : outSeg u a 0 ⊆ origDomain ui :=
    (outSeg_subset_origDomain_iff hp.1.2.2.2).2
      ⟨hp.1.1, hp.1.2.1, hp.1.2.2.1, le_rfl⟩
  convert exterior_cubic_interaction_bound_of_energy h.solution hp.1.2.2.2 hl hs
    (fun v hv => hle.trans (row_radius_lower_bound h hp v hv)) hF
    (henergy u a hp) using 1
  ring

/-- [internal]
Discharge the scalar-energy premise from the signed terminal hypothesis.
The explicit internal project record inputs are outgoing normalized-scalar variation
decay and a uniformly vanishing normalized-field upper bound, all in the
original gauge. The adaptive mass ratio also tends to zero. The estimate
uses any fixed expansion upper bound `L` and the universal coefficient `4`.
No comparison-gauge scalar limit is used. -/
theorem small_initial_interaction_norm_of_density {ui uc L : ℝ}
    (h : OriginalData ui e S) (ht : SignedTerminalBound ui S)
    (huc : uc ∈ Ioo ui 0) (V M ell F : ℝ → ℝ) {R₀ : ℝ} (hR : 0 < R₀)
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0))
    (hrow : ∀ u ∈ Ico uc 0, (u, V u) ∈ adaptiveExterior S ui uc ell)
    (hrange : ∀ u ∈ Ico uc 0, terminalRadius S u ∈ Ioc 0 R₀)
    (hexpansion : ∀ u ∈ Ico uc 0, ∀ v ∈ Icc (V u) 0, S.lam u v ≤ L)
    (hfield : ∀ u ∈ Ico uc 0, ∀ v ∈ Icc (V u) 0,
      ‖S.theta u v / (S.lam u v : ℂ)‖ ≤ F u)
    (hvariation : Tendsto (fun u => (eVariationOn (S.a u) (Icc (V u) 0)).toReal)
      (𝓝[<] 0) (𝓝 0))
    (hfieldDecay : Tendsto F (𝓝[<] 0) (𝓝 0)) :
    (∃ ub ∈ Ioo ui 0, ∀ u ∈ Ico ub 0,
      IntervalIntegrable (weightedJ S u) volume (V u) 0 ∧
      (∫ v in V u..0, ‖weightedJ S u v‖) ≤
        L * (eVariationOn (S.a u) (Icc (V u) 0)).toReal +
          4 * L * F u * (terminalMass S u / ell (terminalRadius S u))) ∧
      Tendsto (fun u => ∫ v in V u..0, ‖weightedJ S u v‖) (𝓝[<] 0) (𝓝 0) := by
  obtain ⟨ue, hue, henergy⟩ := scalar_energy_late h ht M ell hR hmass hell hsmall
  have hRlim := Terminal.terminal_radius_collapse h.ui_neg h.solution h.mu
  have hRt : Tendsto (terminalRadius S) (𝓝[<] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hRlim, ?_⟩
    filter_upwards [Ioo_mem_nhdsLT h.ui_neg] with u hu
    exact h.solution.r_pos (u, 0) ⟨hu.1.le, hu.2, hu.2.le, le_rfl⟩ hu.2
  have hmassDecay : Tendsto (fun u => terminalMass S u / ell (terminalRadius S u))
      (𝓝[<] 0) (𝓝 0) := by
    apply (hsmall.comp hRt).congr'
    filter_upwards [Ioo_mem_nhdsLT h.ui_neg] with u hu
    dsimp only [Function.comp_def, terminalMass, terminalRadius]
    rw [hmass u ⟨hu.1.le, hu.2⟩]
  let ub := max uc ue
  have hub : ub ∈ Ioo ui 0 := ⟨lt_max_of_lt_left huc.1, max_lt huc.2 hue.2⟩
  have hlate {u : ℝ} (hu : u ∈ Ico ub 0) : u ∈ Ico uc 0 :=
    ⟨(le_max_left uc ue).trans hu.1, hu.2⟩
  have he := small_initial_interaction_norm_of_energy_and_density h hub.2 V ell F
    (fun u hu => (hrow u (hlate hu)).1)
    (fun u hu => ⟨hell _ (hrange u (hlate hu)),
      row_radius_lower_bound h (hrow u (hlate hu))⟩)
    (fun u hu => hexpansion u (hlate hu))
    (fun u hu => (henergy u (V u)
      ⟨(hrow u (hlate hu)).1, (le_max_right uc ue).trans hu.1,
        (hrow u (hlate hu)).2.2⟩))
    (fun u hu => hfield u (hlate hu)) hvariation hfieldDecay hmassDecay
  exact ⟨⟨ub, hub, he.1⟩, he.2⟩

end EmcsfAcExtension.Global.Entry
