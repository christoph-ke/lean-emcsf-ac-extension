module

public import EmcsfAcExtension.Global.Exterior.OpticsPast
import EmcsfAcExtension.Global.Exterior.Charge

/-! # The adaptive frontier as a locally Lipschitz graph

The frontier is the unique outgoing label of its prescribed positive
radius. Incoming-past invariance orders these labels. Compact bounds for
the original continuous expansions then give a Lipschitz graph on every
proper interval (`charged_SF_new_version.tex:L1215–L1223`).
-/

public section

open Set Filter Topology MeasureTheory

namespace EmcsfAcExtension.Global.Exterior

variable {ui e : ℝ} {S : Fields}

/-- [internal]
Positive outgoing expansion makes the radius strictly increasing on
every complete proper outgoing row, including its existing axis endpoint. -/
theorem outgoing_radius_strictMono (h : OriginalData ui e S) {u : ℝ} (hu : u ∈ Ico ui 0) :
    StrictMonoOn (S.r u) (Icc u 0) := by
  intro a ha b hb hab
  have hs : outSeg u a b ⊆ origDomain ui :=
    (outSeg_subset_origDomain_iff hab.le).2 ⟨hu.1, hu.2, ha.1, hb.2⟩
  have hr := (Calculus.out_integralForm h.solution ha.1 hab.le hs).1
  have hp : 0 < ∫ v in a..b, S.lam u v := intervalIntegral.integral_pos hab
    (Calculus.continuousOn_out_section h.solution.cont_lam hs)
    (fun v hv => (h.solution.lam_pos (u, v) (hs ⟨rfl, hv.1.le, hv.2⟩)).le)
    ⟨a, ⟨le_rfl, hab.le⟩, h.solution.lam_pos (u, a) (hs ⟨rfl, le_rfl, hab.le⟩)⟩
  rw [← hr.2] at hp
  exact sub_pos.mp hp

/-- [internal]
Each late positive adaptive radius strictly below the terminal radius
has a frontier label strictly between the axis label and zero. A real
representative is used only on the displayed late interval. -/
theorem frontier_label_exists (h : OriginalData ui e S) (ell : ℝ → ℝ) {u₀ : ℝ}
    (hu₀ : u₀ ∈ Ioo ui 0)
    (hlevel : ∀ u ∈ Ico u₀ 0, 0 < ell (S.r u 0) ∧ ell (S.r u 0) < S.r u 0) :
    ∃ V : ℝ → ℝ, ∀ u ∈ Ico u₀ 0,
      u < V u ∧ V u < 0 ∧ S.r u (V u) = ell (S.r u 0) := by
  have hex (u : ℝ) (hu : u ∈ Ico u₀ 0) :
      ∃ v : ℝ, u < v ∧ v < 0 ∧ S.r u v = ell (S.r u 0) := by
    have hs : outSeg u u 0 ⊆ origDomain ui :=
      (outSeg_subset_origDomain_iff hu.2.le).2 ⟨hu₀.1.le.trans hu.1, hu.2, le_rfl, le_rfl⟩
    have haxis := (h.solution.axis u (hs ⟨rfl, le_rfl, hu.2.le⟩)).1
    obtain ⟨v, hv, hrv⟩ := exists_outgoing_radius_between h hu.2.le hs
      (by rw [haxis]; exact (hlevel u hu).1.le) (hlevel u hu).2.le
    have huv : u < v := by
      rcases hv.1.eq_or_lt with heq | hlt
      · rw [← heq, haxis] at hrv
        exact False.elim ((ne_of_gt (hlevel u hu).1) hrv.symm)
      · exact hlt
    have hv0 : v < 0 := by
      rcases hv.2.eq_or_lt with heq | hlt
      · rw [heq] at hrv
        exact False.elim ((ne_of_lt (hlevel u hu).2) hrv.symm)
      · exact hlt
    exact ⟨v, huv, hv0, hrv⟩
  choose W hW using hex
  let V : ℝ → ℝ := fun u => if hu : u ∈ Ico u₀ 0 then W u hu else 0
  refine ⟨V, ?_⟩
  intro u hu
  simpa only [V, dite_eq_left hu] using hW u hu

/-- [internal]
Incoming-past invariance orders all frontier labels. The graph is
characterized by its actual radius, not by a selected radial inverse. -/
theorem frontier_label_monotone_of_past (h : OriginalData ui e S)
    (ell V : ℝ → ℝ) {u₀ : ℝ} (hu₀ : u₀ ∈ Ioo ui 0)
    (hroot : ∀ u ∈ Ico u₀ 0, u < V u ∧ V u < 0 ∧ S.r u (V u) = ell (S.r u 0))
    (hpast : ∀ p ∈ adaptiveExterior S ui u₀ ell,
      ∀ s ∈ Icc u₀ p.1, (s, p.2) ∈ adaptiveExterior S ui u₀ ell) :
    MonotoneOn V (Ico u₀ 0) := by
  intro u hu w hw huw
  have hru := hroot u hu
  have hrw := hroot w hw
  have hp : (w, V w) ∈ adaptiveExterior S ui u₀ ell :=
    ⟨⟨hu₀.1.le.trans hw.1, hw.2, hrw.1.le, hrw.2.1.le⟩, hw.1, hrw.2.2.ge⟩
  have hkeep := hpast (w, V w) hp u ⟨hu.1, huw⟩
  apply le_of_not_gt
  intro hv
  have hstrict := outgoing_radius_strictMono h
    (show u ∈ Ico ui 0 from ⟨hu₀.1.le.trans hu.1, hu.2⟩)
    ⟨huw.trans hrw.1.le, hrw.2.1.le⟩ ⟨hru.1.le, hru.2.1.le⟩ hv
  rw [hru.2.2] at hstrict
  exact (not_lt_of_ge hkeep.2.2) hstrict

/-- [internal]
Uniform positive lower and upper expansion bounds on any proper compact
set of outgoing rows. The witnesses depend on the fixed solution and
row interval, before quantifying over all points in those rows. -/
theorem proper_row_optical_bounds (h : OriginalData ui e S) {a b : ℝ}
    (hia : ui ≤ a) (hab : a ≤ b) (hb : b < 0) :
    ∃ c > 0, ∃ B > 0, ∀ u ∈ Icc a b, ∀ v ∈ Icc u 0,
      c ≤ S.lam u v ∧ S.lam u v ≤ B ∧ c ≤ -S.nu u v ∧ -S.nu u v ≤ B := by
  let K : Set (ℝ × ℝ) := (Icc a b ×ˢ Icc a 0) ∩ {p | p.1 ≤ p.2}
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset
    ((isClosed_Icc.prod isClosed_Icc).inter (isClosed_le continuous_fst continuous_snd))
    inter_subset_left
  have hKs : K ⊆ origDomain ui := by
    intro p hp
    exact ⟨hia.trans hp.1.1.1, hp.1.1.2.trans_lt hb, hp.2, hp.1.2.2⟩
  have hKne : K.Nonempty := ⟨(a, a), ⟨⟨⟨le_rfl, hab⟩,
    ⟨le_rfl, hab.trans hb.le⟩⟩, by change a ≤ a; exact le_rfl⟩⟩
  have cl := h.solution.cont_lam.mono hKs
  have cn := h.solution.cont_nu.mono hKs
  have cf : ContinuousOn (fun p => min (S.lam p.1 p.2) (-S.nu p.1 p.2)) K := cl.inf cn.neg
  have cg : ContinuousOn (fun p => max (S.lam p.1 p.2) (-S.nu p.1 p.2)) K := cl.sup cn.neg
  obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hKne cf
  obtain ⟨B, hB⟩ := hK.bddAbove_image cg
  have hc : 0 < min (S.lam p.1 p.2) (-S.nu p.1 p.2) :=
    lt_min (h.solution.lam_pos p (hKs hp)) (neg_pos.mpr (h.solution.nu_neg p (hKs hp)))
  refine ⟨_, hc, max B 1, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right B 1), ?_⟩
  intro u hu v hv
  have hpuv : (u, v) ∈ K := ⟨⟨hu, ⟨hu.1.trans hv.1, hv.2⟩⟩, hv.1⟩
  have hlo := hmin hpuv
  have hhi := (hB (mem_image_of_mem _ hpuv)).trans (le_max_left B 1)
  exact ⟨hlo.trans (min_le_left _ _), (le_max_left _ _).trans hhi,
    hlo.trans (min_le_right _ _), (le_max_right _ _).trans hhi⟩

/-- [internal]
An ordered frontier increment is bounded using proper-row expansion
bounds. The coefficient `(1+k)B/c` is uniform in both labels once the
solution, row interval, slope and compact expansion bounds are fixed. -/
theorem frontier_increment_le_of_row_bounds (h : OriginalData ui e S) (ell V : ℝ → ℝ)
    {u₀ a b R₀ k c B : ℝ} (hu₀ : u₀ ∈ Ioo ui 0) (hia : u₀ ≤ a) (hb : b < 0)
    (hk : 0 ≤ k) (hc : 0 < c)
    (hLip : LipschitzOnWith (Real.toNNReal k) ell (Ioc 0 R₀))
    (hRange : ∀ u ∈ Icc a b, S.r u 0 ∈ Ioc 0 R₀)
    (hroot : ∀ u ∈ Ico u₀ 0, u < V u ∧ V u < 0 ∧ S.r u (V u) = ell (S.r u 0))
    (hmono : MonotoneOn V (Ico u₀ 0))
    (hbound : ∀ u ∈ Icc a b, ∀ v ∈ Icc u 0,
      c ≤ S.lam u v ∧ S.lam u v ≤ B ∧ c ≤ -S.nu u v ∧ -S.nu u v ≤ B) :
    ∀ u ∈ Icc a b, ∀ w ∈ Icc a b, u ≤ w →
      V w - V u ≤ ((1 + k) * B / c) * (w - u) := by
  intro u hu w hw huw
  have hu' : u ∈ Ico u₀ 0 := ⟨hia.trans hu.1, hu.2.trans_lt hb⟩
  have hw' : w ∈ Ico u₀ 0 := ⟨hia.trans hw.1, hw.2.trans_lt hb⟩
  have hru := hroot u hu'
  have hrw := hroot w hw'
  have hvw := hmono hu' hw' huw
  have hout : outSeg u (V u) (V w) ⊆ origDomain ui :=
    (outSeg_subset_origDomain_iff hvw).2
      ⟨hu₀.1.le.trans hu'.1, hu'.2, hru.1.le, hrw.2.1.le⟩
  have hro := (h.solution.eq_out u (V u) (V w) hru.1 hvw hout).1
  have hOut := intervalIntegral.integral_mono_on hvw
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => c) volume (V u) (V w)) hro.1
    (fun v hv => (hbound u hu v ⟨hru.1.le.trans hv.1, hv.2.trans hrw.2.1.le⟩).1)
  rw [intervalIntegral.integral_const, smul_eq_mul, ← hro.2, hru.2.2] at hOut
  have hin : inSeg u w (V w) ⊆ origDomain ui :=
    (inSeg_subset_origDomain_iff huw).2
      ⟨hu₀.1.le.trans hu'.1, hw'.2, hrw.1.le, hrw.2.1.le⟩
  have hri := (h.solution.eq_in u w (V w) huw hrw.1 hin).1
  have hIn := intervalIntegral.integral_mono_on huw hri.1.neg
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => B) volume u w)
    (fun x hx => (hbound x ⟨hu.1.trans hx.1, hx.2.trans hw.2⟩ (V w)
      ⟨hx.2.trans hrw.1.le, hrw.2.1.le⟩).2.2.2)
  simp only [Pi.neg_apply] at hIn
  rw [intervalIntegral.integral_neg, ← hri.2, intervalIntegral.integral_const,
    smul_eq_mul] at hIn
  change -(S.r w (V w) - S.r u (V w)) ≤ (w - u) * B at hIn
  rw [hrw.2.2] at hIn
  have hin0 : inSeg u w 0 ⊆ origDomain ui :=
    (inSeg_subset_origDomain_iff huw).2 ⟨hu₀.1.le.trans hu'.1, hw'.2, hw'.2.le, le_rfl⟩
  have hrt := (h.solution.eq_in u w 0 huw hw'.2 hin0).1
  have hRt := intervalIntegral.integral_mono_on huw hrt.1.neg
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => B) volume u w)
    (fun x hx => (hbound x ⟨hu.1.trans hx.1, hx.2.trans hw.2⟩ 0
      ⟨hx.2.trans hw'.2.le, le_rfl⟩).2.2.2)
  simp only [Pi.neg_apply] at hRt
  rw [intervalIntegral.integral_neg, ← hrt.2, intervalIntegral.integral_const, smul_eq_mul] at hRt
  have hRnonneg := intervalIntegral.integral_nonneg (μ := volume) huw
    (fun x hx => neg_nonneg.mpr
      (h.solution.nu_neg (x, 0) (hin0 ⟨hx.1, hx.2, rfl⟩)).le)
  rw [intervalIntegral.integral_neg, ← hrt.2] at hRnonneg
  have hRdiff : 0 ≤ S.r u 0 - S.r w 0 := by linarith only [hRnonneg]
  have hL := (lipschitzOnWith_iff_dist_le_mul.mp hLip)
    (S.r u 0) (hRange u hu) (S.r w 0) (hRange w hw)
  rw [Real.coe_toNNReal _ hk, Real.dist_eq, Real.dist_eq, abs_of_nonneg hRdiff] at hL
  have hEll : ell (S.r w 0) - ell (S.r u 0) ≤ k * (S.r u 0 - S.r w 0) := by
    have hn := neg_le_abs (ell (S.r u 0) - ell (S.r w 0))
    linarith only [hn, hL]
  have hScaled := mul_le_mul_of_nonneg_left hRt hk
  have hResult : c * (V w - V u) ≤ (1 + k) * B * (w - u) := by
    nlinarith only [hOut, hIn, hEll, hScaled]
  calc
    V w - V u ≤ ((1 + k) * B * (w - u)) / c :=
      (le_div_iff₀ hc).mpr (by nlinarith only [hResult])
    _ = _ := by ring

/-- [internal]
A frontier graph is Lipschitz on each proper row interval. The explicit
constant depends on the prescribed slope and proper compact expansion
bounds, uniformly in both labels of that interval. -/
theorem frontier_lipschitz_of_row_bounds (h : OriginalData ui e S) (ell V : ℝ → ℝ)
    {u₀ a b R₀ k c B : ℝ} (hu₀ : u₀ ∈ Ioo ui 0) (hia : u₀ ≤ a) (hb : b < 0)
    (hk : 0 ≤ k) (hc : 0 < c) (hB : 0 < B)
    (hLip : LipschitzOnWith (Real.toNNReal k) ell (Ioc 0 R₀))
    (hRange : ∀ u ∈ Icc a b, S.r u 0 ∈ Ioc 0 R₀)
    (hroot : ∀ u ∈ Ico u₀ 0, u < V u ∧ V u < 0 ∧ S.r u (V u) = ell (S.r u 0))
    (hmono : MonotoneOn V (Ico u₀ 0))
    (hbound : ∀ u ∈ Icc a b, ∀ v ∈ Icc u 0,
      c ≤ S.lam u v ∧ S.lam u v ≤ B ∧ c ≤ -S.nu u v ∧ -S.nu u v ≤ B) :
    LipschitzOnWith (Real.toNNReal ((1 + k) * B / c)) V (Icc a b) := by
  have hinc := frontier_increment_le_of_row_bounds h ell V hu₀ hia hb hk hc
    hLip hRange hroot hmono hbound
  have hL : 0 ≤ (1 + k) * B / c := by positivity
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro u hu w hw
  rw [Real.coe_toNNReal _ hL]
  rcases le_total u w with huw | hwu
  · have hvw := hmono ⟨hia.trans hu.1, hu.2.trans_lt hb⟩
      ⟨hia.trans hw.1, hw.2.trans_lt hb⟩ huw
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hvw), Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr huw)]
    simpa only [neg_sub] using hinc u hu w hw huw
  · have hwu' := hmono ⟨hia.trans hw.1, hw.2.trans_lt hb⟩
      ⟨hia.trans hu.1, hu.2.trans_lt hb⟩ hwu
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hwu'), Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr hwu)]
    exact hinc w hw u hu hwu

/-- [internal]
The geometric part of the terminal frontier consumer for
`eq:charged-frontier-speed`. The frontier is an actual radius-level
graph, its label tends to zero, and it is Lipschitz on every proper
closed row interval. Local constants may depend on that interval and
the original solution; the prescribed adaptive slope is fixed first. -/
theorem frontier_geometry_of_terminal {C k : ℝ}
    (h : OriginalData ui e S) (M ell : ℝ → ℝ) {R₀ : ℝ} (hR : 0 < R₀) (hC : 0 < C)
    (hk : 0 < k ∧ k < 1 / 8)
    (hLip : LipschitzOnWith (Real.toNNReal k) ell (Ioc 0 R₀))
    (hcollapse : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0))
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0))
    (hphi : ∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
      C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) :
    ∃ u₀ ∈ Ioo ui 0, ∃ V : ℝ → ℝ,
      (∀ u ∈ Ico u₀ 0, u < V u ∧ V u < 0 ∧ S.r u (V u) = ell (S.r u 0)) ∧
      (∀ u ∈ Ico u₀ 0, S.r u 0 ∈ Ioo 0 R₀) ∧
      MonotoneOn V (Ico u₀ 0) ∧ Tendsto V (𝓝[<] 0) (𝓝 0) ∧
      (∀ u ∈ Ico u₀ 0, 1 / 2 < S.nu u (V u) / S.nu u 0) ∧
      (∀ a b, u₀ ≤ a → a ≤ b → b < 0 →
        ∃ L > 0, LipschitzOnWith (Real.toNNReal L) V (Icc a b)) := by
  obtain ⟨up, hup, hpast⟩ := incoming_past_invariance_of_terminal h M ell hR hC hk hLip
    hcollapse hmass hell hellsmall hsmall hphi
  obtain ⟨un, hun, hnu⟩ := uniform_nu_ratio_of_terminal h M ell hR hC
    hcollapse hmass hell hellsmall hsmall hphi (1 / 2) (by norm_num)
  have hrpos : ∀ᶠ u in 𝓝[<] (0 : ℝ), 0 < S.r u 0 := by
    filter_upwards [Ioo_mem_nhdsLT h.ui_neg] with u hu
    exact h.solution.r_pos (u, 0) ⟨hu.1.le, hu.2, hu.2.le, le_rfl⟩ hu.2
  have hRt : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hcollapse, hrpos⟩
  have he : ∀ᶠ u in 𝓝[<] (0 : ℝ), u ∈ Ioo ui 0 ∧ S.r u 0 ∈ Ioo 0 R₀ ∧
      ell (S.r u 0) / S.r u 0 < 1 / 2 := by
    filter_upwards [Ioo_mem_nhdsLT h.ui_neg, hrpos,
      hcollapse.eventually (Iio_mem_nhds hR),
      (hellsmall.comp hRt).eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
      with u hu hr hrR hℓ
    exact ⟨hu, ⟨hr, hrR⟩, hℓ⟩
  obtain ⟨d, hd, hdb⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp he
  let ur := max d ui / 2
  have hur : ur ∈ Ioo ui 0 := by
    have hm0 := max_lt hd h.ui_neg
    dsimp [ur]
    constructor <;> linarith [le_max_right d ui]
  let u₀ := max up (max un ur)
  have hu₀ : u₀ ∈ Ioo ui 0 :=
    ⟨lt_max_of_lt_left hup.1, max_lt hup.2 (max_lt hun.2 hur.2)⟩
  have hlate (u : ℝ) (hu : u ∈ Ico u₀ 0) : u ∈ Ioo ui 0 ∧
      S.r u 0 ∈ Ioo 0 R₀ ∧ ell (S.r u 0) / S.r u 0 < 1 / 2 := by
    apply hdb
    refine ⟨?_, hu.2⟩
    have hb : ur ≤ u := (le_max_right un ur).trans
      ((le_max_right up (max un ur)).trans hu.1)
    dsimp [ur] at hb
    have hm0 := max_lt hd h.ui_neg
    linarith [le_max_left d ui]
  have hlevel (u : ℝ) (hu : u ∈ Ico u₀ 0) :
      0 < ell (S.r u 0) ∧ ell (S.r u 0) < S.r u 0 := by
    have hl := hlate u hu
    refine ⟨hell _ ⟨hl.2.1.1, hl.2.1.2.le⟩, ?_⟩
    have hb := (div_lt_iff₀ hl.2.1.1).mp hl.2.2
    linarith [hl.2.1.1]
  obtain ⟨V, hroot⟩ := frontier_label_exists h ell hu₀ hlevel
  have hinv (p : ℝ × ℝ) (hp : p ∈ adaptiveExterior S ui u₀ ell)
      (s : ℝ) (hs : s ∈ Icc u₀ p.1) : (s, p.2) ∈ adaptiveExterior S ui u₀ ell := by
    have hbu : up ≤ u₀ := le_max_left up (max un ur)
    have hkeep := (hpast p ⟨hp.1, hbu.trans hp.2.1, hp.2.2⟩).1 s ⟨hbu.trans hs.1, hs.2⟩
    exact ⟨hkeep.1, hs.1, hkeep.2.2⟩
  have hmono := frontier_label_monotone_of_past h ell V hu₀ hroot hinv
  have hVt : Tendsto V (𝓝[<] 0) (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [Ioo_mem_nhdsLT (max_lt hu₀.2 (neg_neg_of_pos hε))] with u hu
    have hu' : u ∈ Ico u₀ 0 := ⟨(le_max_left u₀ (-ε)).trans hu.1.le, hu.2⟩
    have hr := hroot u hu'
    rw [Real.dist_eq, sub_zero, abs_of_neg hr.2.1]
    linarith [((le_max_right u₀ (-ε)).trans_lt hu.1), hr.1]
  refine ⟨u₀, hu₀, V, hroot, (fun u hu => (hlate u hu).2.1), hmono, hVt, ?_, ?_⟩
  · intro u hu
    have hr := hroot u hu
    have hp : (u, V u) ∈ adaptiveExterior S ui un ell :=
      ⟨⟨hu₀.1.le.trans hu.1, hu.2, hr.1.le, hr.2.1.le⟩,
        (le_max_left un ur).trans ((le_max_right up (max un ur)).trans hu.1), hr.2.2.ge⟩
    have hb := (abs_lt.mp (hnu (u, V u) hp)).1
    linarith
  · intro a b hia hab hb
    obtain ⟨c, hc, B, hB, hbounds⟩ := proper_row_optical_bounds h (hu₀.1.le.trans hia) hab hb
    refine ⟨(1 + k) * B / c, div_pos (mul_pos (by linarith [hk.1]) hB) hc,
      frontier_lipschitz_of_row_bounds h ell V hu₀ hia hb
      hk.1.le hc hB hLip ?_ hroot hmono hbounds⟩
    exact fun u hu => ⟨(hlate u ⟨hia.trans hu.1, hu.2.trans_lt hb⟩).2.1.1,
      (hlate u ⟨hia.trans hu.1, hu.2.trans_lt hb⟩).2.1.2.le⟩

end EmcsfAcExtension.Global.Exterior
