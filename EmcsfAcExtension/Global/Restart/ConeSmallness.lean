module

public import EmcsfAcExtension.Global.Restart.AxisLimit
public import EmcsfAcExtension.Global.Restart.ConeVariation
public import EmcsfAcExtension.Global.Restart.ConeAC
import EmcsfAcExtension.Global.Closure.Entry
import EmcsfAcExtension.Global.Terminal.OpticalUpper

/-! # The complete small cone supplied to local restart

The unfinished shrinking construction remains an explicit family of finite
boundary records with its budgets, radial estimate, amplitude and radius
stop. The output is exactly the cone premise consumed by
`Closure.regular_center_continuation_of_cone`.
Source: charged_SF_new_version.tex:L4115–4168 and approved internal project record.
-/

public section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global.Restart

/-- [internal] Combine the finite boundary records and their uniform closure
estimates into a proper complete cone. The variation coefficient depends
only on `c,F,A`, fixed before the physical data and entry errors. This helper
does not assert existence of the shrinking construction. -/
theorem selected_cone_of_closure (c F A : ℝ) (hc : 0 < c) (hF : F ^ 2 < 1)
    (ui e : ℝ) (S : Fields) (h : OriginalData ui e S)
    {u₀ v₀ ρ b₀ K M D₀ ε₀ ζ₂ : ℝ} (hu₀ : u₀ ∈ Ioo ui 0)
    (hρ : 0 ≤ ρ ∧ ρ < 1) (U : ℕ → ℝ) (vb : ℝ → ℝ)
    (B : ∀ N, FiniteBoundary S ui u₀ (U N) v₀ ρ vb N)
    (hU : Monotone U) (hcuts : ∀ N i, (B N).cuts i = U i)
    (hR : ∀ n, S.r u₀ 0 / 2 ≤ S.r (U n) 0)
    (hrad : ∀ n, S.r (U n) (vb (U n)) = stageRadius ρ b₀ n)
    (E J : ℕ → ℝ)
    (hbudget : ∀ N, BoundaryBudgets S ui u₀ (U N) v₀ ρ vb N (B N)
      (fun i => E i))
    (hEsum : ∀ N, ∑ n ∈ Finset.range N, E n ≤ K)
    (hamp : ∀ n, ‖S.phi (U n) (vb (U n))‖ ≤ M)
    (hclosed : ∀ n, J n ≤ A * (D₀ + ε₀ + ζ₂))
    (hrow : ∀ n, (1 - F ^ 2) *
      (eVariationOn (S.a (U n)) (Icc (vb (U n)) 0)).toReal ≤ c⁻¹ * J n +
        F ^ 2 * ‖S.theta (U n) (vb (U n)) / (S.lam (U n) (vb (U n)) : ℂ)‖) :
    ∃ us ∈ Ioo ui 0, u₀ ≤ us ∧
      AbsolutelyContinuousOnInterval (S.a us) us 0 ∧
      eVariationOn (S.a us) (Icc us 0) ≤
        ENNReal.ofReal ((c⁻¹ * A / (1 - F ^ 2)) * (D₀ + ε₀ + ζ₂)) ∧
      ‖S.phi us us‖ ≤ M ∧ S.r us 0 ≤ S.r u₀ 0 := by
  have hU0 : U 0 = u₀ := (hcuts 0 0).symm.trans (B 0).first
  have hentry (n : ℕ) : u₀ ≤ U n := by
    rw [← hU0]
    exact hU (Nat.zero_le n)
  have hmem (n : ℕ) : (U n, vb (U n)) ∈ origDomain ui :=
    (B n).mem _ ⟨hentry n, le_rfl⟩
  have hmono : Monotone (fun n => vb (U n)) := by
    intro n m hnm
    exact (B m).mono ⟨hentry n, hU hnm⟩ ⟨hentry m, le_rfl⟩ (hU hnm)
  have hRpos := h.solution.r_pos (u₀, 0)
    ⟨hu₀.1.le, hu₀.2, hu₀.2.le, le_rfl⟩ hu₀.2
  obtain ⟨us, hus, hTu, hTv⟩ := proper_axis_limit_of_closure ui e S h hu₀ hρ
    (half_pos hRpos) U vb B hU hU0.ge hR hrad
  have hentry_limit : u₀ ≤ us := ge_of_tendsto hTu (Eventually.of_forall hentry)
  have hvle (n : ℕ) : vb (U n) ≤ us :=
    ge_of_tendsto hTv (eventually_atTop.mpr ⟨n, fun m hm => hmono hm⟩)
  have hdecay := (boundary_scalar_decay_of_closure ui e S h U vb B E (fun _ => 0)
    (fun _ => le_rfl) hbudget hEsum (K := K) (L := 0) (by simp)).2.2 U (by
      intro n
      rw [hcuts, hcuts]
      exact ⟨le_rfl, hU (Nat.le_succ n)⟩)
  obtain ⟨hac, hvertex⟩ := complete_cone_ac_of_closure ui e S h hus U
    (fun n => vb (U n)) hTu hTv hmem hamp
  refine ⟨us, hus, hentry_limit, hac, ?_, hvertex, ?_⟩
  · exact complete_cone_variation_of_closure c F A hc hF ui e S h hus U
      (fun n => vb (U n)) J hTu
      (fun n => ⟨(hmem n).1, (hmem n).2.1, (hmem n).2.2.1, hvle n⟩)
      (by simpa only [norm_zero] using hdecay.norm) hclosed hrow
  · exact (Terminal.terminal_radius_strictAntiOn h.solution).antitoneOn
      ⟨hu₀.1.le, hu₀.2⟩ ⟨hus.1.le, hus.2⟩ hentry_limit

/-- [internal] The first-power charged logarithmic scale also tends to
zero. `C` depends on the fixed development, and is chosen before every
entry row; coupling is arbitrary (charged_SF_new_version.tex:L3888–3898). -/
theorem charged_logarithmic_scale_tendsto_zero (ui e C : ℝ) (S : Fields)
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) (hC : 0 ≤ C) :
    Tendsto (fun u => |e| * S.r u 0 *
      (C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))))
      (𝓝[<] 0) (𝓝 0) := by
  have ht := (cc_zeta ui e S h hs C).sqrt
  simp only [Real.sqrt_zero] at ht
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsLT h.ui_neg] with u hu
  have hr := h.solution.r_pos (u, 0) ⟨hu.1.le, hu.2, hu.2.le, le_rfl⟩ hu.2
  have hM : 0 ≤ C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0))) := by positivity
  have heq : e ^ 2 * (C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) ^ 2 *
      S.r u 0 ^ 2 =
      (|e| * S.r u 0 * (C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0))))) ^ 2 := by
    simp only [mul_pow, sq_abs]
    ring
  rw [heq, Real.sqrt_sq (by positivity)]

/-- [internal] The exact `hcone` required by regular-center continuation,
conditional only on the unfinished closure conclusions displayed below.
`c,F,A` precede physical data; the amplitude coefficient `C` and admissible
energy ceiling may depend on the fixed development. For each fixed energy
tolerance, the same closure records must exist for all sufficiently late
entry rows. No smallness of the coupling or original datum is assumed.
Source: charged_SF_new_version.tex:L4115–4168; approved internal project record. -/
theorem complete_cone_smallness_of_closure (c F A : ℝ)
    (hc : 0 < c) (hF : F ^ 2 < 1) (hA : 0 < A)
    (ui e : ℝ) (S : Fields) (h : OriginalData ui e S) (hs : SignedTerminalBound ui S)
    (C εmax : ℝ) (hC : 1 ≤ C) (hεmax : 0 < εmax)
    (D M : ℝ → ℝ) (hD : Tendsto D (𝓝[<] 0) (𝓝 0))
    (hM : ∀ u, M u = C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0))))
    (hclosure : ∀ ε₀ ∈ Ioc 0 εmax, ∀ᶠ u₀ in 𝓝[<] (0 : ℝ),
      ∃ v₀ ρ b₀ K : ℝ, ∃ U : ℕ → ℝ, ∃ vb : ℝ → ℝ,
      ∃ B : ∀ N, FiniteBoundary S ui u₀ (U N) v₀ ρ vb N,
      ∃ E J : ℕ → ℝ,
        (0 ≤ ρ ∧ ρ < 1) ∧ Monotone U ∧ (∀ N i, (B N).cuts i = U i) ∧
        (∀ n, S.r u₀ 0 / 2 ≤ S.r (U n) 0) ∧
        (∀ n, S.r (U n) (vb (U n)) = stageRadius ρ b₀ n) ∧
        (∀ N, BoundaryBudgets S ui u₀ (U N) v₀ ρ vb N (B N) (fun i => E i)) ∧
        (∀ N, ∑ n ∈ Finset.range N, E n ≤ K) ∧
        (∀ n, ‖S.phi (U n) (vb (U n))‖ ≤ M u₀) ∧
        (∀ n, J n ≤ A * (D u₀ + ε₀ + e ^ 2 * M u₀ ^ 2 * S.r u₀ 0 ^ 2)) ∧
        (∀ n, (1 - F ^ 2) *
          (eVariationOn (S.a (U n)) (Icc (vb (U n)) 0)).toReal ≤ c⁻¹ * J n +
            F ^ 2 * ‖S.theta (U n) (vb (U n)) /
              (S.lam (U n) (vb (U n)) : ℂ)‖)) :
    ∀ η : ℝ, 0 < η → ∃ us ∈ Ioo ui 0,
      AbsolutelyContinuousOnInterval (S.a us) us 0 ∧
      eVariationOn (S.a us) (Icc us 0) ≤ ENNReal.ofReal η ∧
      |e| * (2 * S.r us 0) *
        (1 + ‖S.phi us us‖ + 10 * (eVariationOn (S.a us) (Icc us 0)).toReal) ≤ η := by
  let Bcone := c⁻¹ * A / (1 - F ^ 2)
  have hB : 0 < Bcone := div_pos (mul_pos (inv_pos.mpr hc) hA) (sub_pos.mpr hF)
  have hZ : Tendsto (fun u => e ^ 2 * M u ^ 2 * S.r u 0 ^ 2)
      (𝓝[<] 0) (𝓝 0) := by
    simpa only [hM] using cc_zeta ui e S h hs C
  have hscale : Tendsto (fun u => |e| * S.r u 0 * M u) (𝓝[<] 0) (𝓝 0) := by
    simpa only [hM] using charged_logarithmic_scale_tendsto_zero ui e C S h hs
      (zero_le_one.trans hC)
  intro η hη
  let δ := min η 1
  have hδ : 0 < δ := lt_min hη zero_lt_one
  let ε₀ := min εmax (δ / (2 * Bcone))
  have hε : ε₀ ∈ Ioc 0 εmax :=
    ⟨lt_min hεmax (div_pos hδ (by positivity)), min_le_left _ _⟩
  have hsmall : ∀ᶠ u in 𝓝[<] (0 : ℝ), Bcone *
      (D u + e ^ 2 * M u ^ 2 * S.r u 0 ^ 2) ≤ δ / 2 :=
    ((hD.add hZ).const_mul Bcone).eventually
      (ge_mem_nhds (by simpa only [add_zero, mul_zero] using half_pos hδ))
  have hscale_small : ∀ᶠ u in 𝓝[<] (0 : ℝ), |e| * S.r u 0 * M u ≤ η / 24 :=
    hscale.eventually (ge_mem_nhds (by positivity))
  have hlabel : ∀ᶠ u : ℝ in 𝓝[<] 0, u ∈ Ioo ui 0 := Ioo_mem_nhdsLT h.ui_neg
  obtain ⟨u₀, hu₀, hsmall₀, hscale₀, hcl⟩ :=
    (hlabel.and (hsmall.and (hscale_small.and (hclosure ε₀ hε)))).exists
  obtain ⟨v₀, ρ, b₀, K, U, vb, B, E, J, hρ, hU, hcuts,
    hR, hrad, hbudget, hEsum, hamp, hclosed, hrow⟩ := hcl
  obtain ⟨us, hus, _, hac, hvar, hvertex, hr⟩ :=
    selected_cone_of_closure c F A hc hF ui e S h hu₀ hρ U vb B hU hcuts
      hR hrad E J hbudget hEsum hamp hclosed hrow
  have hεbound : Bcone * ε₀ ≤ δ / 2 := by
    have hh := mul_le_mul_of_nonneg_left (min_le_right εmax (δ / (2 * Bcone))) hB.le
    dsimp only [ε₀]
    convert hh using 1
    field_simp [hB.ne']
  have herror : Bcone * (D u₀ + ε₀ + e ^ 2 * M u₀ ^ 2 * S.r u₀ 0 ^ 2) ≤ δ := by
    linarith only [hsmall₀, hεbound]
  have hvδ : eVariationOn (S.a us) (Icc us 0) ≤ ENNReal.ofReal δ :=
    hvar.trans (ENNReal.ofReal_le_ofReal herror)
  have hvreal : (eVariationOn (S.a us) (Icc us 0)).toReal ≤ 1 := by
    have hh := (ENNReal.toReal_le_toReal
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvδ) ENNReal.ofReal_ne_top).2 hvδ
    rw [ENNReal.toReal_ofReal hδ.le] at hh
    exact hh.trans (min_le_right _ _)
  have hMone : 1 ≤ M u₀ := by
    rw [hM]
    have hfac : (1 : ℝ) ≤ 1 + Real.sqrt (Real.log (S.r ui 0 / S.r u₀ 0)) :=
      le_add_of_nonneg_right (Real.sqrt_nonneg _)
    calc
      1 ≤ C := hC
      _ = C * 1 := (mul_one C).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hfac (zero_le_one.trans hC)
  have hdatum : 1 + ‖S.phi us us‖ +
      10 * (eVariationOn (S.a us) (Icc us 0)).toReal ≤ 12 * M u₀ := by
    linarith only [hvertex, hvreal, hMone]
  have hrpos := h.solution.r_pos (us, 0) ⟨hus.1.le, hus.2, hus.2.le, le_rfl⟩ hus.2
  refine ⟨us, hus, hac, hvδ.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _)), ?_⟩
  calc
    _ ≤ |e| * (2 * S.r us 0) * (12 * M u₀) :=
      mul_le_mul_of_nonneg_left hdatum (by positivity)
    _ ≤ 24 * (|e| * S.r u₀ 0 * M u₀) := by
      have hh := mul_le_mul_of_nonneg_right hr
        (mul_nonneg (abs_nonneg e) (zero_le_one.trans hMone))
      nlinarith only [hh]
    _ ≤ η := by linarith only [hscale₀]

end EmcsfAcExtension.Global.Restart
