module

public import EmcsfAcExtension.Global.Exterior.DerivativeSourceAggregateBound
public import EmcsfAcExtension.Global.Exterior.OpticsCoefficients
public import EmcsfAcExtension.Global.Exterior.DerivativeSourceForcing

/-! # Terminal consumer of the aggregate exterior source estimate

Every gap, scalar, charge, mass-ratio and optical profile is discharged
by the proved terminal exterior estimates. The terminal inputs are the
approved internal project record handoff. The constant `4096` is numerical and uniform
in the solution, coupling, row and inner endpoint; only the cutoff and
logarithmic envelope depend on the fixed terminal data.
Source: `charged_SF_new_version.tex:L1298–L1335`, internal project record (S0)–(S4).
-/

public section

open Set Filter Topology MeasureTheory

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
The exact source bound, with all geometric profiles derived from the
terminal estimates. `SF` bounds the continuous field `theta/lambda`,
with no supremum of an outgoing derivative. The universal constant is
`4096`; the cutoff is fixed before every later row and label. -/
theorem charged_exterior_source_bound_of_terminal {ui e C : ℝ} {S : Fields}
    (h : OriginalData ui e S) (M ell : ℝ → ℝ)
    {R₀ : ℝ} (hR : 0 < R₀) (hC : 0 < C)
    (hcollapse : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0))
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0))
    (hphi : ∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
      C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) :
    ∃ u₀ ∈ Ioo ui 0, ∀ u a, (u, a) ∈ adaptiveExterior S ui u₀ ell →
      ∀ SF : ℝ, (∀ v ∈ Icc a 0, ‖S.theta u v / (S.lam u v : ℂ)‖ ≤ SF) →
      let L := (C + 2) * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))
      (∫ v in a..0, ‖rawDensitySource e S u v‖) ≤
        4096 * (-S.nu u 0) *
          (terminalMass S u / S.r u a ^ 2 *
            (SF + Real.sqrt (terminalMass S u / S.r u a)) +
          |e| * L * (terminalMass S u / S.r u a) *
            Real.sqrt (terminalMass S u / S.r u a) +
          |e| * (terminalMass S u / S.r u a) +
          |e| * L * Real.sqrt (terminalMass S u / S.r u a) +
          e ^ 2 * L ^ 2 * Real.sqrt (terminalMass S u * terminalRadius S u)) := by
  obtain ⟨us, hus, hsource⟩ := source_inputs_of_terminal h M ell hR hC
    hcollapse hmass hell hellsmall hsmall hphi
  obtain ⟨ux, hux, hmassratio⟩ := exterior_small_gap_of_terminal h M ell hR
    (by norm_num : (0 : ℝ) < 1 / 4) hcollapse hmass hell hsmall
  obtain ⟨un, hun, hratio⟩ := uniform_nu_ratio_of_terminal h M ell hR hC
    hcollapse hmass hell hellsmall hsmall hphi (1 / 2) (by norm_num)
  let u₀ := max us (max ux un)
  have hu₀ : u₀ ∈ Ioo ui 0 :=
    ⟨lt_max_of_lt_left hus.1, max_lt hus.2 (max_lt hux.2 hun.2)⟩
  refine ⟨u₀, hu₀, ?_⟩
  intro u a hp SF hF
  have hps : (u, a) ∈ adaptiveExterior S ui us ell :=
    ⟨hp.1, (le_max_left us (max ux un)).trans hp.2.1, hp.2.2⟩
  obtain ⟨hua, ha, hs, hg, hscalar, hcharge⟩ := hsource u a hps
  have hp0 : (u, 0) ∈ origDomain ui := hs ⟨rfl, ha, le_rfl⟩
  have hn0 := neg_pos.mpr (h.solution.nu_neg (u, 0) hp0)
  have hν (v : ℝ) (hv : v ∈ Icc a 0) : -S.nu u v ≤ 2 * (-S.nu u 0) := by
    have hrl := outgoing_radius_mono h hua.le hv.1
      (fun _ hx => hs (outSeg_subset_outSeg le_rfl hv.2 hx))
    have hpv : (u, v) ∈ adaptiveExterior S ui un ell :=
      ⟨hs ⟨rfl, hv⟩, (le_max_right ux un).trans
        ((le_max_right us (max ux un)).trans hp.2.1), hp.2.2.trans hrl⟩
    have hh := (abs_lt.mp (hratio (u, v) hpv)).2
    have hdiv : (-S.nu u v) / (-S.nu u 0) ≤ 2 := by
      rw [neg_div_neg_eq]
      linarith only [hh]
    exact (div_le_iff₀ hn0).mp hdiv
  have hpx : (u, a) ∈ adaptiveExterior S ui ux ell :=
    ⟨hp.1, (le_max_left ux un).trans
      ((le_max_right us (max ux un)).trans hp.2.1), hp.2.2⟩
  have hx := hmassratio (u, a) hpx
  have hM : 0 ≤ terminalMass S u := mass_nonneg h hp0
  have hX : terminalMass S u / S.r u a ≤ 1 := by
    have hh := div_le_div_of_nonneg_left hM hx.1 hp.2.2
    have hb := hx.2.2
    rw [mul_div_assoc] at hb
    linarith only [hh, hb]
  exact charged_exterior_source_bound_of_profiles h hua ha hs hg hscalar hcharge hν hX hF

/-- [internal]
The source majorant after the proved field-versus-variation estimate, on
the actual adaptive frontier. The numerical constant `20480=5*4096` is
universal. This is the source input to the outgoing variation argument;
no bounded variation estimate or forcing integral is assumed. -/
theorem source_variation_majorant_of_terminal {ui e C : ℝ} {S : Fields}
    (h : OriginalData ui e S) (M ell : ℝ → ℝ)
    {R₀ : ℝ} (hR : 0 < R₀) (hC : 0 < C)
    (hcollapse : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0))
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0))
    (hphi : ∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
      C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) :
    ∃ u₀ ∈ Ioo ui 0, ∀ u a, (u, a) ∈ adaptiveExterior S ui u₀ ell →
      S.r u a = ell (S.r u 0) →
      let L := fun R => (C + 2) * (1 + Real.sqrt (Real.log (S.r ui 0 / R)))
      (∫ v in a..0, ‖rawDensitySource e S u v‖) ≤
        20480 * (-S.nu u 0) *
          (M (S.r u 0) / ell (S.r u 0) ^ 2 *
            (eVariationOn (S.a u) (Icc a 0)).toReal +
          exteriorForcing e M ell L (S.r u 0)) := by
  obtain ⟨us, hus, hsource⟩ := charged_exterior_source_bound_of_terminal h M ell hR hC
    hcollapse hmass hell hellsmall hsmall hphi
  obtain ⟨uv, huv, hvar⟩ := charged_exterior_FV_of_terminal h M ell hR
    hcollapse hmass hell hellsmall hsmall
  refine ⟨max us uv, ⟨lt_max_of_lt_left hus.1, max_lt hus.2 huv.2⟩, ?_⟩
  intro u a hp hroot
  have hps : (u, a) ∈ adaptiveExterior S ui us ell :=
    ⟨hp.1, (le_max_left us uv).trans hp.2.1, hp.2.2⟩
  have hpv : (u, a) ∈ adaptiveExterior S ui uv ell :=
    ⟨hp.1, (le_max_right us uv).trans hp.2.1, hp.2.2⟩
  have hb := hsource u a hps
    ((eVariationOn (S.a u) (Icc a 0)).toReal +
      4 * Real.sqrt (terminalMass S u / ell (S.r u 0)))
    (hvar u a hpv hroot)
  have hm := hmass u ⟨hp.1.1, hp.1.2.1⟩
  dsimp only [terminalMass, terminalRadius] at hb
  rw [hroot, ← hm] at hb
  refine hb.trans ?_
  have hn : 0 ≤ -S.nu u 0 := (neg_pos.mpr (h.solution.nu_neg (u, 0)
    ⟨hp.1.1, hp.1.2.1, hp.1.2.1.le, le_rfl⟩)).le
  have hM : 0 ≤ M (S.r u 0) := by
    rw [hm]
    exact mass_nonneg h ⟨hp.1.1, hp.1.2.1, hp.1.2.1.le, le_rfl⟩
  have hL : 0 ≤ (C + 2) * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0))) := by positivity
  have hX : 0 ≤ M (S.r u 0) / ell (S.r u 0) := by
    have hr : 0 ≤ ell (S.r u 0) := by
      rw [← hroot]
      exact by
        rcases hp.1.2.2.1.eq_or_lt with heq | hlt
        · change u = a at heq
          subst a
          rw [(h.solution.axis u hp.1).1]
        · exact (h.solution.r_pos (u, a) hp.1 hlt).le
    exact div_nonneg hM hr
  have hA : 0 ≤ M (S.r u 0) / ell (S.r u 0) ^ 2 := by positivity
  have hv : 0 ≤ (eVariationOn (S.a u) (Icc a 0)).toReal := ENNReal.toReal_nonneg
  have h₁ := mul_nonneg hn (mul_nonneg hA hv)
  have h₂ : 0 ≤ (-S.nu u 0) * (|e| * ((C + 2) *
      (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) *
      (M (S.r u 0) / ell (S.r u 0)) * Real.sqrt (M (S.r u 0) / ell (S.r u 0))) := by positivity
  have h₃ : 0 ≤ (-S.nu u 0) * (|e| * (M (S.r u 0) / ell (S.r u 0))) := by positivity
  have h₄ : 0 ≤ (-S.nu u 0) * (|e| * ((C + 2) *
      (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) *
      Real.sqrt (M (S.r u 0) / ell (S.r u 0))) := by positivity
  have h₅ : 0 ≤ (-S.nu u 0) * (e ^ 2 * ((C + 2) *
      (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) ^ 2 *
      Real.sqrt (M (S.r u 0) * S.r u 0)) := by positivity
  simp only [exteriorForcing]
  nlinarith only [h₁, h₂, h₃, h₄, h₅]

end EmcsfAcExtension.Global.Exterior
