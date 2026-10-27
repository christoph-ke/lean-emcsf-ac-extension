module

public import EmcsfAcExtension.Global.Defs.Interaction
public import EmcsfAcExtension.Global.Defs.Original
import EmcsfAcExtension.Global.Renormalized.WeakTransfer
import EmcsfAcExtension.Global.Calculus.Sections
import EmcsfAcExtension.Infra.AC.Variation

/-! # Pre-absorption finiteness on proper cutoffs

The only rough factor in the entry density is the derivative of an AC
outgoing scalar. The actual weighted source is continuous off the axis.
Zero extension of that source from a compact cutoff and Tonelli give
finiteness of its label-first history norm. No absorption estimate is used.
Source: `charged_SF_new_version.tex:L3839–L3971`, approved internal project record finite-envelope.
-/

public section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global.Interaction

/-- [internal] The entry weighted derivative is integrable on a proper
outgoing segment, directly from its frozen AC normalized scalar. There
are no profile, smallness, or envelope assumptions. -/
theorem weightedJ_intervalIntegrable {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) : IntervalIntegrable (weightedJ S u) volume a b := by
  let y := fun v => S.theta u v / (S.lam u v : ℂ)
  let k := fun v => (S.lam u v / S.r u v * ‖y v‖ ^ 2 : ℝ) * y v
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have ct := Calculus.continuousOn_out_section hS.cont_theta hs
  have cy : ContinuousOn y (Icc a b) :=
    ct.div (Complex.continuous_ofReal.comp_continuousOn cl)
      (fun v hv => Complex.ofReal_ne_zero.mpr (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)).ne')
  have ck : ContinuousOn k (Icc a b) :=
    (Complex.continuous_ofReal.comp_continuousOn
      ((cl.div cr (fun v hv => (hS.r_pos (u, v) (hs ⟨rfl, hv⟩)
        (hua.trans_le hv.1)).ne')).mul (cy.norm.pow 2))).mul cy
  have ha := (hS.ac_out u a b hab hs).2.2.2.2
  have hi := (ha.intervalIntegrable_deriv_complex.sub (ck.intervalIntegrable_of_Icc hab))
    |>.continuousOn_mul (by simpa only [uIcc_of_le hab] using
      Complex.continuous_ofReal.comp_continuousOn cl)
  apply hi.congr
  intro v hv
  have hv : v ∈ Icc a b := by
    simpa only [uIcc_of_le hab] using uIoc_subset_uIcc hv
  have hg : (1 - (S.mu u v : ℂ)) ≠ 0 := by
    exact_mod_cast (hS.one_sub_mu_pos (u, v) (hs ⟨rfl, hv⟩)).ne'
  dsimp [weightedJ, jOut, k, y]
  push_cast
  field_simp [hg]

/-- [node sec:charged-terminal-interaction#finite-cutoff-envelope-finiteness]
The entry derivative is L¹ and the generated source and its additive
history envelope are finite on every compact proper cutoff,
charged_SF_new_version.tex:L3839–L3971. The cutoff may have any measurable history
shape; no absorption inequality, derivative envelope, or numerical bound
is assumed. There are no constants. -/
theorem finite_cutoff_envelope_finiteness {ui e u₀ v₀ : ℝ} {S : Fields}
    (h : OriginalData ui e S) (huv : u₀ < v₀) (hv : v₀ ≤ 0)
    (hentry : outSeg u₀ v₀ 0 ⊆ origDomain ui)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hproper : K ⊆ origDomain ui ∩ {p | p.1 < p.2}) :
    IntegrableOn (deriv (S.a u₀)) (Icc v₀ 0) ∧
      IntegrableOn (weightedJ S u₀) (Icc v₀ 0) ∧
      initialInteraction S u₀ v₀ < ⊤ ∧
      IntegrableOn (Function.uncurry (weightedJSource e S)) K (volume.prod volume) ∧
      sourceInteraction e S K v₀ < ⊤ ∧
      interactionNorm e S K u₀ v₀ = initialInteraction S u₀ v₀ + sourceInteraction e S K v₀ ∧
      interactionNorm e S K u₀ v₀ < ⊤ := by
  have ha := (h.solution.ac_out u₀ v₀ 0 hv hentry).2.2.2.2
  have hder := (intervalIntegrable_iff_integrableOn_Icc_of_le hv).mp
    ha.intervalIntegrable_deriv_complex
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hv).mp
    (weightedJ_intervalIntegrable h.solution huv hv hentry)
  have hini : initialInteraction S u₀ v₀ < ⊤ :=
    hasFiniteIntegral_iff_enorm.mp hi.hasFiniteIntegral
  have hc := Renormalized.continuousOn_weightedJSource h.solution hproper
  have hsource : IntegrableOn (Function.uncurry (weightedJSource e S)) K
      (volume.prod volume) := hc.integrableOn_compact hK
  let f : ℝ × ℝ → ℂ := K.indicator (Function.uncurry (weightedJSource e S))
  have hif : Integrable f (volume.prod volume) :=
    (integrable_indicator_iff hK.measurableSet).mpr hsource
  have hfin : (∫⁻ v, ∫⁻ u, ‖f (u, v)‖ₑ) < ⊤ := by
    rw [← lintegral_prod_symm _ hif.enorm.aemeasurable]
    exact hasFiniteIntegral_iff_enorm.mp hif.hasFiniteIntegral
  have hsection (v : ℝ) :
      (∫⁻ u in {u | (u, v) ∈ K}, ‖weightedJSource e S u v‖ₑ) =
        ∫⁻ u, ‖f (u, v)‖ₑ := by
    have hm : MeasurableSet {u | (u, v) ∈ K} :=
      hK.measurableSet.preimage (measurable_id.prodMk measurable_const)
    rw [← lintegral_indicator hm]
    apply lintegral_congr
    intro u
    simp only [f, enorm_indicator_eq_indicator_enorm]
    rfl
  have hsrc : sourceInteraction e S K v₀ < ⊤ := by
    unfold sourceInteraction
    simp_rw [hsection]
    exact (setLIntegral_le_lintegral _ _).trans_lt hfin
  have hsum : interactionNorm e S K u₀ v₀ =
      initialInteraction S u₀ v₀ + sourceInteraction e S K v₀ :=
    lintegral_add_left' hi.enorm.aemeasurable _
  refine ⟨hder, hi, hini, hsource, hsrc, hsum, ?_⟩
  rw [hsum]
  exact ENNReal.add_lt_top.mpr ⟨hini, hsrc⟩

end EmcsfAcExtension.Global.Interaction
