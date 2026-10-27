module

public import EmcsfAcExtension.Global.Exterior.SignedBoundary
public import EmcsfAcExtension.Global.Exterior.SignedVariation
import EmcsfAcExtension.Global.Exterior.OpticsFrontier
import EmcsfAcExtension.Global.Terminal.Mass

/-! # Compatibility of the constructed adaptive frontiers

Separate terminal consumers choose representatives of the same unique
outgoing radius level. Their late geometric and density conclusions can
therefore be combined. Source: `charged_SF_new_version.tex:L1215–1223`, L1417–1424.
-/

public section

open Set Filter Topology MeasureTheory

namespace EmcsfAcExtension.Global.Exterior

/-- [internal] Every terminal radius lies in the original radial range. -/
theorem terminal_radius_mem {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) {u : ℝ} (hu : u ∈ Ico ui 0) :
    S.r u 0 ∈ Ioc 0 (S.r ui 0) := by
  exact ⟨h.solution.r_pos (u, 0) ⟨hu.1, hu.2, hu.2.le, le_rfl⟩ hu.2,
    (Terminal.terminal_radius_strictAntiOn h.solution).antitoneOn
      ⟨le_rfl, h.ui_neg⟩ hu hu.1⟩

/-- [internal] The positive adaptive radius has a unique proper outgoing
label. There are no constants or terminal estimates in this uniqueness. -/
theorem frontier_label_eq {ui e u a b : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hu : u ∈ Ico ui 0)
    (ha : u < a ∧ a ≤ 0) (hb : u < b ∧ b ≤ 0)
    (hr : S.r u a = S.r u b) : a = b := by
  exact (outgoing_radius_strictMono h hu).injOn
    ⟨ha.1.le, ha.2⟩ ⟨hb.1.le, hb.2⟩ hr

/-- [internal] Any increasing graph of the constructed radius is continuous
on its complete proper half-open interval. Compact optical bounds are
chosen separately for each proper segment, before its two labels. -/
theorem frontier_continuous_of_root {ui e c k : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hc : c ∈ Ioo ui 0) (ell V : ℝ → ℝ)
    (hk : 0 ≤ k)
    (hLip : LipschitzOnWith (Real.toNNReal k) ell (Ioc 0 (S.r ui 0)))
    (hroot : ∀ u ∈ Ico c 0, u < V u ∧ V u < 0 ∧ S.r u (V u) = ell (S.r u 0))
    (hm : MonotoneOn V (Ico c 0)) : ContinuousOn V (Ico c 0) := by
  apply continuousOn_boundary_Ico_of_proper_segments
  intro b hcb hb
  obtain ⟨a, ha, B, hB, hbound⟩ := proper_row_optical_bounds h hc.1.le hcb hb
  exact (frontier_lipschitz_of_row_bounds h ell V hc le_rfl hb hk ha hB hLip
    (fun u hu => terminal_radius_mem h ⟨hc.1.le.trans hu.1, hu.2.trans_lt hb⟩)
    hroot hm hbound).continuousOn

/-- [internal] Outgoing density decay transfers to any representative of
the same adaptive frontier. Its cutoff precedes all outgoing labels. -/
theorem density_decay_of_root {ui e c k : ℝ} {S : Fields}
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
    Tendsto (fun u => (eVariationOn (S.a u) (Icc (V u) 0)).toReal) (𝓝[<] 0) (𝓝 0) ∧
    (∀ ε > 0, ∀ᶠ u in 𝓝[<] (0 : ℝ), ∀ v ∈ Icc (V u) 0,
      ‖S.theta u v / (S.lam u v : ℂ)‖ < ε) := by
  have hR := (terminal_radius_mem h ⟨le_rfl, h.ui_neg⟩).1
  obtain ⟨d, hd, W, E, hW, _, _, hvar, hfield, _⟩ :=
    variation_and_boundary_exit_tails h hs M ell hR hk hLip hMc hM hI
      hmass hell hellsmall hsmall
  have he : ∀ᶠ u in 𝓝[<] (0 : ℝ), V u = W u := by
    filter_upwards [Ioo_mem_nhdsLT (max_lt hc.2 hd.2)] with u hu
    have huc : u ∈ Ico c 0 := ⟨(le_max_left c d).trans hu.1.le, hu.2⟩
    have hud : u ∈ Ico d 0 := ⟨(le_max_right c d).trans hu.1.le, hu.2⟩
    have hr := hroot u huc
    have hw := hW u hud
    exact frontier_label_eq h ⟨hc.1.le.trans huc.1, hu.2⟩
      ⟨hr.1, hr.2.1.le⟩ ⟨hw.1, hw.2.1.le⟩ (hr.2.2.trans hw.2.2.symm)
  refine ⟨hvar.congr' (he.mono fun u hu => by simp only [hu]), ?_⟩
  intro ε hε
  filter_upwards [he, hfield ε hε] with u hu hf
  simpa only [hu] using hf

/-- [internal] Restricting a finite-variation frontier to a later entry row
preserves finite intrinsic variation in the new parallel frame. The bound
is the original complete variation, before every proper upper endpoint. -/
theorem frontier_bv_later_of_bv {ui e a c : ℝ} {S : Fields} {V : ℝ → ℝ}
    (h : OriginalData ui e S) (hac : a ≤ c) (_hc : c < 0)
    (hV : ContinuousOn V (Ico a 0))
    (hmem : ∀ u ∈ Ico a 0, (u, V u) ∈ origDomain ui)
    (hbv : BoundedVariationOn (curveParallel e S S.a id V a) (Ico a 0)) :
    BoundedVariationOn (curveParallel e S S.a id V c) (Ico c 0) := by
  apply boundedVariationOn_curveParallel_Ico_of_uniform_bound hbv
  intro b hb
  have hsub : Icc a b ⊆ Ico a 0 := fun u hu => ⟨hu.1, hu.2.trans_lt hb.2⟩
  have hA : IntervalIntegrable (fun u => S.A u (V u) * deriv id u) volume a b := by
    simpa only [deriv_id, mul_one, Function.comp_def, Function.uncurry, id_eq] using
      (h.solution.cont_A.comp (continuousOn_id.prodMk (hV.mono hsub))
        (fun u hu => hmem u (hsub hu))).intervalIntegrable_of_Icc (hac.trans hb.1)
  rw [← eVariationOn_curveParallel_eq_curveCovVar
    (e := e) (S := S) (f := S.a) (U := id) (V := V) hac hb.1 hA]
  exact eVariationOn.mono _ (fun u hu => ⟨hac.trans hu.1, hu.2.trans_lt hb.2⟩)

/-- [internal] The signed-terminal speed theorem applies to every actual
representative of the same frontier after one common cutoff. The local
constants may depend on the proper interval, before its pairs of labels. -/
theorem frontier_speed_of_root {ui e c k : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S)
    (hc : c ∈ Ioo ui 0) (M ell V : ℝ → ℝ)
    (hk : 0 < k ∧ k < 1 / 8)
    (hLip : LipschitzOnWith (Real.toNNReal k) ell (Ioc 0 (S.r ui 0)))
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 (S.r ui 0), 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0))
    (hroot : ∀ u ∈ Ico c 0, u < V u ∧ V u < 0 ∧ S.r u (V u) = ell (S.r u 0)) :
    ∃ d ∈ Ioo ui 0, c ≤ d ∧
      ∀ a b, d ≤ a → a ≤ b → b < 0 →
        ∃ L > 0, ∃ m > 0,
          LipschitzOnWith (Real.toNNReal L) V (Icc a b) ∧
          (∀ u ∈ Icc a b, ∀ w ∈ Icc a b, m * dist u w ≤ dist (V u) (V w)) ∧
          (∀ᵐ u ∂volume.restrict (Icc a b),
            S.lam u (V u) * deriv V u =
                -S.nu u (V u) - deriv ell (S.r u 0) * (-S.nu u 0) ∧
              (1 / 2 - k) * (-S.nu u 0) ≤ S.lam u (V u) * deriv V u ∧
              0 < S.lam u (V u) * deriv V u) := by
  have hR := (terminal_radius_mem h ⟨le_rfl, h.ui_neg⟩).1
  obtain ⟨s, hs', W, hW, _, _, hspeed⟩ := charged_frontier_speed h hs M ell hR hk hLip
    hmass hell hellsmall hsmall
  let d := max c s
  have hd : d ∈ Ioo ui 0 := ⟨lt_max_of_lt_left hc.1, max_lt hc.2 hs'.2⟩
  have he (u : ℝ) (hu : u ∈ Ico d 0) : V u = W u := by
    have huc : u ∈ Ico c 0 := ⟨(le_max_left c s).trans hu.1, hu.2⟩
    have hus : u ∈ Ico s 0 := ⟨(le_max_right c s).trans hu.1, hu.2⟩
    have hr := hroot u huc
    have hw := hW u hus
    exact frontier_label_eq h ⟨hd.1.le.trans hu.1, hu.2⟩
      ⟨hr.1, hr.2.1.le⟩ ⟨hw.1, hw.2.1.le⟩ (hr.2.2.trans hw.2.2.symm)
  refine ⟨d, hd, le_max_left c s, ?_⟩
  intro a b ha hab hb
  have hsub : Icc a b ⊆ Ico d 0 := fun u hu => ⟨ha.trans hu.1, hu.2.trans_lt hb⟩
  obtain ⟨L, hL, m, hm, hWL, hWm, hWs⟩ :=
    hspeed a b ((le_max_right c s).trans ha) hab hb
  refine ⟨L, hL, m, hm, ?_, ?_, ?_⟩
  · rw [lipschitzOnWith_iff_dist_le_mul]
    intro u hu w hw
    rw [he u (hsub hu), he w (hsub hw)]
    exact hWL.dist_le_mul u hu w hw
  · intro u hu w hw
    rw [he u (hsub hu), he w (hsub hw)]
    exact hWm u hu w hw
  · have heq : EqOn V W (Ioo a b) := fun u hu => he u (hsub (Ioo_subset_Icc_self hu))
    rw [← restrict_Ioo_eq_restrict_Icc] at hWs ⊢
    filter_upwards [hWs, ae_restrict_mem measurableSet_Ioo] with u hu hum
    rw [heq.deriv isOpen_Ioo hum, heq hum]
    exact hu

end EmcsfAcExtension.Global.Exterior
