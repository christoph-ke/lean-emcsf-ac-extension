module

public import EmcsfAcExtension.Global.Exterior.Entry
public import EmcsfAcExtension.Global.Exterior.AssemblyGeometry
import EmcsfAcExtension.Global.Terminal.OpticalUpper

/-! # The small entry interaction norm from the signed terminal setting

Both outgoing density inputs are discharged from the constructed exterior.
The actual normalized field supremum supplies its vanishing envelope.
Source: `charged_SF_new_version.tex:L1427–1456`, L3878–3886.
-/

public section

open Set Filter Topology MeasureTheory

namespace EmcsfAcExtension.Global.Exterior

/-- [internal] On a proper frontier the genuine outgoing field supremum
bounds every field value, is nonnegative, and inherits uniform decay.
The comparison coefficient is the universal constant `1`. -/
theorem field_sup_decay_of_root {ui e c : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hc : c ∈ Ioo ui 0) (V : ℝ → ℝ)
    (hroot : ∀ u ∈ Ico c 0, u < V u ∧ V u < 0)
    (hfield : ∀ ε > 0, ∀ᶠ u in 𝓝[<] (0 : ℝ), ∀ v ∈ Icc (V u) 0,
      ‖S.theta u v / (S.lam u v : ℂ)‖ < ε) :
    (∀ u ∈ Ico c 0, 0 ≤ outgoingFieldSup S V u ∧
      ∀ v ∈ Icc (V u) 0,
        ‖S.theta u v / (S.lam u v : ℂ)‖ ≤ outgoingFieldSup S V u) ∧
      Tendsto (outgoingFieldSup S V) (𝓝[<] 0) (𝓝 0) := by
  have hbounds (u : ℝ) (hu : u ∈ Ico c 0) :
      0 ≤ outgoingFieldSup S V u ∧
      ∀ v ∈ Icc (V u) 0,
        ‖S.theta u v / (S.lam u v : ℂ)‖ ≤ outgoingFieldSup S V u := by
    have hr := hroot u hu
    have hmem (v : ℝ) (hv : v ∈ Icc (V u) 0) : (u, v) ∈ origDomain ui :=
      ⟨hc.1.le.trans hu.1, hu.2, hr.1.le.trans hv.1, hv.2⟩
    have ct := h.solution.cont_theta.comp
      (continuous_const.prodMk continuous_id).continuousOn hmem
    have cl := h.solution.cont_lam.comp
      (continuous_const.prodMk continuous_id).continuousOn hmem
    have cf := (ct.div (Complex.continuous_ofReal.comp_continuousOn cl)
      (fun v hv => Complex.ofReal_ne_zero.mpr (h.solution.lam_pos (u, v) (hmem v hv)).ne')).norm
    have hb := isCompact_Icc.bddAbove_image cf
    have hlo (v : ℝ) (hv : v ∈ Icc (V u) 0) :
        ‖S.theta u v / (S.lam u v : ℂ)‖ ≤ outgoingFieldSup S V u :=
      le_csSup hb ⟨v, hv, rfl⟩
    exact ⟨(norm_nonneg _).trans (hlo 0 ⟨hr.2.le, le_rfl⟩), hlo⟩
  refine ⟨hbounds, Metric.tendsto_nhds.mpr ?_⟩
  intro ε hε
  filter_upwards [Ioo_mem_nhdsLT hc.2, hfield (ε / 2) (half_pos hε)] with u hu hf
  have hul : u ∈ Ico c 0 := ⟨hu.1.le, hu.2⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hbounds u hul).1]
  have hle : outgoingFieldSup S V u ≤ ε / 2 := by
    unfold outgoingFieldSup
    apply csSup_le
    · exact ⟨_, ⟨0, ⟨(hroot u hul).2.le, le_rfl⟩, rfl⟩⟩
    · rintro _ ⟨v, hv, rfl⟩
      exact (hf v hv).le
  exact hle.trans_lt (half_lt_self hε)

end EmcsfAcExtension.Global.Exterior

namespace EmcsfAcExtension.Global.Entry

/-- [node sec:charged-step7#small-initial-interaction-norm]
The actual entry interaction is L¹ on all sufficiently late exterior rows
and its norm tends to zero. All density and expansion estimates are
derived from original data, the signed terminal bound and the constructed
profile. The coefficient `4` is universal. Every uniform expansion upper
bound is allowed, before its late entry cutoff and all subsequent rows. -/
theorem small_initial_interaction_norm {ui e c k : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S)
    (hc : c ∈ Ioo ui 0) (M ell V : ℝ → ℝ)
    (hk : 0 < k ∧ k < 1 / 8)
    (hLip : LipschitzOnWith (Real.toNNReal k) ell (Ioc 0 (S.r ui 0)))
    (hMc : ContinuousOn M (Ioc 0 (S.r ui 0)))
    (hM : ∀ R ∈ Ioc 0 (S.r ui 0), 0 ≤ M R)
    (hI : (∫⁻ R in Ioc 0 (S.r ui 0), ENNReal.ofReal (M R / ell R ^ 2)) < ⊤)
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 (S.r ui 0), 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0))
    (hroot : ∀ u ∈ Ico c 0, u < V u ∧ V u < 0 ∧ S.r u (V u) = ell (S.r u 0)) :
    (∀ L : ℝ,
      (∀ u ∈ Ico c 0, ∀ v ∈ Icc (V u) 0, S.lam u v ≤ L) →
      ∃ ub ∈ Ioo ui 0, ∀ u ∈ Ico ub 0,
      IntervalIntegrable (weightedJ S u) volume (V u) 0 ∧
      (∫ v in V u..0, ‖weightedJ S u v‖) ≤
        L * (eVariationOn (S.a u) (Icc (V u) 0)).toReal +
          4 * L * Exterior.outgoingFieldSup S V u *
            (terminalMass S u / ell (terminalRadius S u))) ∧
      Tendsto (fun u => ∫ v in V u..0, ‖weightedJ S u v‖) (𝓝[<] 0) (𝓝 0) := by
  obtain ⟨hvar, hfield⟩ := Exterior.density_decay_of_root h hs hc M ell V hk hLip hMc
    hM hI hmass hell hellsmall hsmall hroot
  obtain ⟨hF, hFt⟩ := Exterior.field_sup_decay_of_root h hc V
    (fun u hu => ⟨(hroot u hu).1, (hroot u hu).2.1⟩) hfield
  have hrow (u : ℝ) (hu : u ∈ Ico c 0) : (u, V u) ∈ adaptiveExterior S ui c ell :=
    ⟨⟨hc.1.le.trans hu.1, hu.2, (hroot u hu).1.le, (hroot u hu).2.1.le⟩,
      hu.1, (hroot u hu).2.2.ge⟩
  have hest (L : ℝ)
      (hupper : ∀ u ∈ Ico c 0, ∀ v ∈ Icc (V u) 0, S.lam u v ≤ L) :=
    small_initial_interaction_norm_of_density h hs hc V M ell
      (Exterior.outgoingFieldSup S V) (Exterior.terminal_radius_mem h ⟨le_rfl, h.ui_neg⟩).1
      hmass hell hsmall hrow
      (fun u hu => Exterior.terminal_radius_mem h ⟨hc.1.le.trans hu.1, hu.2⟩)
      hupper (fun u hu => (hF u hu).2) hvar hFt
  refine ⟨fun L hupper => (hest L hupper).1, ?_⟩
  obtain ⟨L, _, _, hupper⟩ := Terminal.lambda_gap_upper h.ui_neg h.solution h.mu
  exact (hest L (fun u hu v hv => hupper (u, v)
    ⟨hc.1.le.trans hu.1, hu.2, (hroot u hu).1.le.trans hv.1, hv.2⟩)).2

end EmcsfAcExtension.Global.Entry
