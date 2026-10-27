module

public import EmcsfAcExtension.Local.Defs.C1Class
public import EmcsfAcExtension.Frozen.IsSolution
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Local.Calculus.C1ToSolution2
import EmcsfAcExtension.Infra.AC.Variation
import EmcsfAcExtension.Infra.Null.IntegralForm
import EmcsfAcExtension.Infra.Triangle
import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # Classical to broad bridge on compact continuation domains

The old-triangle/strip union is not convex. Bounded continuous domain
partials control every contained straight characteristic section, which
suffices for the frozen AC and variation clauses. Only the axis mass
limit needs to be supplied from the old part of the construction.
-/

public section

open Set MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace EmcsfAcExtension.Local

/-- On any compact unique-differentiation domain, one C¹ function has
one finite Lipschitz constant for all contained characteristic sections.
The constant depends on this function and domain, uniformly in sections. -/
theorem c1_characteristic_lipschitz_compact {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : Set (ℝ × ℝ)} {f : ℝ → ℝ → E}
    (hD : IsCompact D) (hU : UniqueDiffOn ℝ D)
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) D) :
    ∃ K : ℝ≥0,
      (∀ u c d, outSeg u c d ⊆ D → LipschitzOnWith K (f u) (Icc c d)) ∧
      (∀ c d v, inSeg c d v ⊆ D → LipschitzOnWith K (fun u => f u v) (Icc c d)) := by
  obtain ⟨Cu, hCu⟩ := hD.bddAbove_image (continuousOn_pdU hf hU).norm
  obtain ⟨Cv, hCv⟩ := hD.bddAbove_image (continuousOn_pdV hf hU).norm
  let K : ℝ≥0 := ⟨max 0 (max Cu Cv), le_max_left _ _⟩
  have hKu p (hp : p ∈ D) : ‖pdU D f p.1 p.2‖₊ ≤ K := by
    change ‖pdU D f p.1 p.2‖ ≤ max 0 (max Cu Cv)
    exact (hCu (mem_image_of_mem _ hp)).trans
      ((le_max_left Cu Cv).trans (le_max_right _ _))
  have hKv p (hp : p ∈ D) : ‖pdV D f p.1 p.2‖₊ ≤ K := by
    change ‖pdV D f p.1 p.2‖ ≤ max 0 (max Cu Cv)
    exact (hCv (mem_image_of_mem _ hp)).trans
      ((le_max_right Cu Cv).trans (le_max_right _ _))
  refine ⟨K, ?_, ?_⟩
  · intro u c d hs
    exact (convex_Icc c d).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x hx => hasDerivWithinAt_pdV hf (hs ⟨rfl, hx⟩)
        (fun y hy => hs ⟨rfl, hy⟩)) (fun x hx => hKv (u, x) (hs ⟨rfl, hx⟩))
  · intro c d v hs
    exact (convex_Icc c d).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x hx => hasDerivWithinAt_pdU hf (hs ⟨hx.1, hx.2, rfl⟩)
        (fun y hy => hs ⟨hy.1, hy.2, rfl⟩))
      (fun x hx => hKu (x, v) (hs ⟨hx.1, hx.2, rfl⟩))

/-- Compact-domain characteristic variation is controlled by a common
finite first-jet constant. No convexity of the full domain is needed. -/
theorem c1_characteristic_variation_compact {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : Set (ℝ × ℝ)} {f : ℝ → ℝ → E}
    (hD : IsCompact D) (hU : UniqueDiffOn ℝ D)
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) D) :
    ∃ K : ℝ≥0,
      (∀ u c d, outSeg u c d ⊆ D →
        eVariationOn (f u) (Icc c d) ≤ K * ENNReal.ofReal (d - c)) ∧
      (∀ c d v, inSeg c d v ⊆ D →
        eVariationOn (fun u => f u v) (Icc c d) ≤ K * ENNReal.ofReal (d - c)) := by
  obtain ⟨K, hv, hu⟩ := c1_characteristic_lipschitz_compact hD hU hf
  refine ⟨K, ?_, ?_⟩
  · intro u c d hs
    simpa only [Function.comp_id, eVariationOn_id_Icc] using
      (hv u c d hs).comp_eVariationOn_le (mapsTo_id (Icc c d))
  · intro c d v hs
    simpa only [Function.comp_id, eVariationOn_id_Icc] using
      (hu c d v hs).comp_eVariationOn_le (mapsTo_id (Icc c d))

private theorem continuationCompact_ac_v {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : Set (ℝ × ℝ)} {f : ℝ → ℝ → E}
    (hD : IsCompact D) (hU : UniqueDiffOn ℝ D)
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) D)
    {u c d : ℝ} (hcd : c ≤ d) (hs : outSeg u c d ⊆ D) :
    AbsolutelyContinuousOnInterval (f u) c d := by
  obtain ⟨K, hv, _⟩ := c1_characteristic_lipschitz_compact hD hU hf
  have hl : LipschitzOnWith K (f u) (uIcc c d) := by
    simpa only [uIcc_of_le hcd] using hv u c d hs
  exact hl.absolutelyContinuousOnInterval

private theorem continuationCompact_ac_u {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : Set (ℝ × ℝ)} {f : ℝ → ℝ → E}
    (hD : IsCompact D) (hU : UniqueDiffOn ℝ D)
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) D)
    {v c d : ℝ} (hcd : c ≤ d) (hs : inSeg c d v ⊆ D) :
    AbsolutelyContinuousOnInterval (fun u => f u v) c d := by
  obtain ⟨K, _, hu⟩ := c1_characteristic_lipschitz_compact hD hU hf
  have hl : LipschitzOnWith K (fun u => f u v) (uIcc c d) := by
    simpa only [uIcc_of_le hcd] using hu c d v hs
  exact hl.absolutelyContinuousOnInterval

private theorem continuationCompact_form_v {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {D : Set (ℝ × ℝ)} {f g : ℝ → ℝ → E} (hU : UniqueDiffOn ℝ D)
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) D)
    (heq : ∀ p ∈ D, p.1 < p.2 → pdV D f p.1 p.2 = g p.1 p.2)
    {u c d : ℝ} (huc : u < c) (hcd : c ≤ d) (hs : outSeg u c d ⊆ D) :
    IntegralForm (f u) (g u) c d := by
  apply (integralForm_pdV hf hU hcd (fun x hx => hs ⟨rfl, hx⟩)).congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIcc] with x hx
  rw [uIcc_of_le hcd] at hx
  exact heq (u, x) (hs ⟨rfl, hx⟩) (huc.trans_le hx.1)

private theorem continuationCompact_form_u {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {D : Set (ℝ × ℝ)} {f g : ℝ → ℝ → E} (hU : UniqueDiffOn ℝ D)
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) D)
    (heq : ∀ p ∈ D, p.1 < p.2 → pdU D f p.1 p.2 = g p.1 p.2)
    {v c d : ℝ} (hcd : c ≤ d) (hdv : d < v) (hs : inSeg c d v ⊆ D) :
    IntegralForm (fun u => f u v) (fun u => g u v) c d := by
  apply (integralForm_pdU hf hU hcd (fun x hx => hs ⟨hx.1, hx.2, rfl⟩)).congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIcc] with x hx
  rw [uIcc_of_le hcd] at hx
  exact heq (x, v) (hs ⟨hx.1, hx.2, rfl⟩) (hx.2.trans_lt hdv)

private theorem continuationCompact_variation_v {E : Type*} [NormedAddCommGroup E]
    {D : Set (ℝ × ℝ)} {f : ℝ → ℝ → E} {K L : ℝ≥0}
    (hD : IsCompact D) (hKL : K ≤ L)
    (hv : ∀ u c d, outSeg u c d ⊆ D →
      eVariationOn (f u) (Icc c d) ≤ K * ENNReal.ofReal (d - c))
    {u c d : ℝ} (hs : outSeg u c d ⊆ D) :
    eVariationOn (f u) (Icc c d) ≤ L * ENNReal.ofReal (Metric.diam D) := by
  by_cases hcd : c ≤ d
  · have hd := Metric.dist_le_diam_of_mem hD.isBounded
      (hs (show (u, c) ∈ outSeg u c d from ⟨rfl, le_rfl, hcd⟩))
      (hs (show (u, d) ∈ outSeg u c d from ⟨rfl, hcd, le_rfl⟩))
    have hw : d-c ≤ Metric.diam D := by
      have heq : dist ((u, c) : ℝ × ℝ) (u, d) = d-c := by
        rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, Real.dist_eq,
          abs_of_nonpos (sub_nonpos.mpr hcd)]
        ring
      rw [heq] at hd
      exact hd
    exact (hv u c d hs).trans (mul_le_mul (by exact_mod_cast hKL)
      (ENNReal.ofReal_le_ofReal hw) bot_le bot_le)
  · simp [Icc_eq_empty_of_lt (lt_of_not_ge hcd)]

private theorem continuationCompact_variation_u {E : Type*} [NormedAddCommGroup E]
    {D : Set (ℝ × ℝ)} {f : ℝ → ℝ → E} {K L : ℝ≥0}
    (hD : IsCompact D) (hKL : K ≤ L)
    (hu : ∀ c d v, inSeg c d v ⊆ D →
      eVariationOn (fun u => f u v) (Icc c d) ≤ K * ENNReal.ofReal (d - c))
    {v c d : ℝ} (hs : inSeg c d v ⊆ D) :
    eVariationOn (fun u => f u v) (Icc c d) ≤ L * ENNReal.ofReal (Metric.diam D) := by
  by_cases hcd : c ≤ d
  · have hd := Metric.dist_le_diam_of_mem hD.isBounded
      (hs (show (c, v) ∈ inSeg c d v from ⟨le_rfl, hcd, rfl⟩))
      (hs (show (d, v) ∈ inSeg c d v from ⟨hcd, le_rfl, rfl⟩))
    have hw : d-c ≤ Metric.diam D := by
      have heq : dist ((c, v) : ℝ × ℝ) (d, v) = d-c := by
        rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, Real.dist_eq,
          abs_of_nonpos (sub_nonpos.mpr hcd)]
        ring
      rw [heq] at hd
      exact hd
    exact (hu c d v hs).trans (mul_le_mul (by exact_mod_cast hKL)
      (ENNReal.ofReal_le_ofReal hw) bot_le bot_le)
  · simp [Icc_eq_empty_of_lt (lt_of_not_ge hcd)]

/-- A C¹ solution on a compact unique-differentiation domain gives a
broad solution on any subset where its axis mass limit is supplied.
The subset itself need not have ambient unique derivatives: this also
applies to a single entering cone. Variation constants depend on the
one ambient compact configuration, uniformly in contained sections. -/
theorem IsC1Solution.toIsSolution_on_of_axis_mu
    {e : ℝ} {S : Fields} {D E : Set (ℝ × ℝ)}
    (hS : IsC1Solution e S D) (hD : IsCompact D) (hU : UniqueDiffOn ℝ D)
    (hED : E ⊆ D)
    (hmu : ∀ t, (t, t) ∈ E → Tendsto (Function.uncurry S.mu)
      (𝓝[E ∩ {p | p.1 < p.2}] (t, t)) (𝓝 0)) :
    IsSolution e S E where
  subset := hED.trans hS.subset
  r_pos := fun p hp => hS.r_pos p (hED hp)
  lam_pos := fun p hp => hS.lam_pos p (hED hp)
  nu_neg := fun p hp => hS.nu_neg p (hED hp)
  one_sub_mu_pos := fun p hp => hS.one_sub_mu_pos p (hED hp)
  cont_r := hS.c1_r.continuousOn.mono hED
  cont_lam := hS.c1_lam.continuousOn.mono hED
  cont_nu := hS.c1_nu.continuousOn.mono hED
  cont_m := hS.c1_m.continuousOn.mono hED
  cont_Q := hS.c1_Q.continuousOn.mono hED
  cont_phi := hS.c1_phi.continuousOn.mono hED
  cont_A := hS.c1_A.continuousOn.mono hED
  cont_theta := hS.c1_theta.continuousOn.mono hED
  cont_xi := hS.c1_xi.continuousOn.mono hED
  eq_out := by
    intro u c d huc hcd hs
    exact ⟨
      continuationCompact_form_v hU hS.c1_r
        (fun p hp huv => (hS.eq_v p hp huv).1)
        huc hcd (hs.trans hED),
      continuationCompact_form_v hU hS.c1_nu
        (fun p hp huv => (hS.eq_v p hp huv).2.1)
        huc hcd (hs.trans hED),
      continuationCompact_form_v hU hS.c1_m
        (fun p hp huv => (hS.eq_v p hp huv).2.2.1)
        huc hcd (hs.trans hED),
      continuationCompact_form_v hU hS.c1_Q
        (fun p hp huv => (hS.eq_v p hp huv).2.2.2.1)
        huc hcd (hs.trans hED),
      continuationCompact_form_v hU hS.c1_A
        (fun p hp huv => (hS.eq_v p hp huv).2.2.2.2.1)
        huc hcd (hs.trans hED),
      continuationCompact_form_v hU hS.c1_phi
        (fun p hp huv => (hS.eq_v p hp huv).2.2.2.2.2.1)
        huc hcd (hs.trans hED),
      continuationCompact_form_v hU hS.c1_xi
        (fun p hp huv => (hS.eq_v p hp huv).2.2.2.2.2.2)
        huc hcd (hs.trans hED)⟩
  eq_in := by
    intro c d v hcd hdv hs
    exact ⟨
      continuationCompact_form_u hU hS.c1_r
        (fun p hp huv => (hS.eq_u p hp huv).1)
        hcd hdv (hs.trans hED),
      continuationCompact_form_u hU hS.c1_lam
        (fun p hp huv => (hS.eq_u p hp huv).2.1)
        hcd hdv (hs.trans hED),
      continuationCompact_form_u hU hS.c1_m
        (fun p hp huv => (hS.eq_u p hp huv).2.2.1)
        hcd hdv (hs.trans hED),
      continuationCompact_form_u hU hS.c1_Q
        (fun p hp huv => (hS.eq_u p hp huv).2.2.2.1)
        hcd hdv (hs.trans hED),
      continuationCompact_form_u hU hS.c1_phi
        (fun p hp huv => (hS.eq_u p hp huv).2.2.2.2.1)
        hcd hdv (hs.trans hED),
      continuationCompact_form_u hU hS.c1_theta
        (fun p hp huv => (hS.eq_u p hp huv).2.2.2.2.2)
        hcd hdv (hs.trans hED)⟩
  ac_out := fun _ _ _ hcd hs => ⟨continuationCompact_ac_v hD hU hS.c1_r hcd (hs.trans hED),
    continuationCompact_ac_v hD hU hS.c1_m hcd (hs.trans hED),
    continuationCompact_ac_v hD hU hS.c1_Q hcd (hs.trans hED),
    continuationCompact_ac_v hD hU hS.c1_phi hcd (hs.trans hED),
    continuationCompact_ac_v hD hU hS.c1_a hcd (hs.trans hED)⟩
  ac_in := fun _ _ _ hcd hs => ⟨continuationCompact_ac_u hD hU hS.c1_r hcd (hs.trans hED),
    continuationCompact_ac_u hD hU hS.c1_m hcd (hs.trans hED),
    continuationCompact_ac_u hD hU hS.c1_Q hcd (hs.trans hED),
    continuationCompact_ac_u hD hU hS.c1_phi hcd (hs.trans hED)⟩
  bv_loc := by
    intro K hKD _hcompact
    obtain ⟨Kl, hlv, hlu⟩ := c1_characteristic_variation_compact hD hU hS.c1_lam
    obtain ⟨Kn, hnv, hnu⟩ := c1_characteristic_variation_compact hD hU hS.c1_nu
    obtain ⟨Ka, hav, hau⟩ := c1_characteristic_variation_compact hD hU hS.c1_a
    obtain ⟨Kb, hbv, hbu⟩ := c1_characteristic_variation_compact hD hU hS.c1_b
    let L : NNReal := Kl + Kn + Ka + Kb
    have hKl : Kl ≤ L := by
      dsimp [L]
      exact ((le_add_of_nonneg_right bot_le).trans
        (le_add_of_nonneg_right bot_le)).trans (le_add_of_nonneg_right bot_le)
    have hKn : Kn ≤ L := by
      dsimp [L]
      exact ((le_add_of_nonneg_left bot_le).trans
        (le_add_of_nonneg_right bot_le)).trans (le_add_of_nonneg_right bot_le)
    have hKa : Ka ≤ L := by
      dsimp [L]
      exact (le_add_of_nonneg_left bot_le).trans
        (le_add_of_nonneg_right bot_le)
    have hKb : Kb ≤ L := by
      exact le_add_of_nonneg_left bot_le
    refine ⟨L * ENNReal.ofReal (Metric.diam D), by finiteness, ?_, ?_⟩
    · intro u c d hs
      exact ⟨continuationCompact_variation_v hD hKl hlv (hs.trans (hKD.trans hED)),
        continuationCompact_variation_v hD hKn hnv (hs.trans (hKD.trans hED)),
        continuationCompact_variation_v hD hKa hav (hs.trans (hKD.trans hED)),
        continuationCompact_variation_v hD hKb hbv (hs.trans (hKD.trans hED))⟩
    · intro c d v hs
      exact ⟨continuationCompact_variation_u hD hKl hlu (hs.trans (hKD.trans hED)),
        continuationCompact_variation_u hD hKn hnu (hs.trans (hKD.trans hED)),
        continuationCompact_variation_u hD hKa hau (hs.trans (hKD.trans hED)),
        continuationCompact_variation_u hD hKb hbu (hs.trans (hKD.trans hED))⟩
  axis_small_var := by
    intro t _ht η hη
    obtain ⟨K, hv, hu⟩ := c1_characteristic_variation_compact hD hU hS.c1_phi
    let δ : ℝ := η / (2 * ((K : ℝ) + 1))
    have hδ : 0 < δ := div_pos hη (by positivity)
    have hδeq : 2 * ((K : ℝ) + 1) * δ = η := mul_div_cancel₀ η (by positivity)
    have hbound : (K : ℝ) * (2 * δ) ≤ η := by nlinarith
    have hvar : (K : ℝ≥0∞) * ENNReal.ofReal (2 * δ) ≤ ENNReal.ofReal η := by
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul K.coe_nonneg]
      exact ENNReal.ofReal_le_ofReal hbound
    refine ⟨δ, hδ, ?_, ?_⟩
    · intro u c d hs
      have htseg : outSeg u c d ⊆ triangle (t - δ) (t + δ) := fun p hp => (hs hp).2
      by_cases hcd : c ≤ d
      · have hc := htseg (show (u, c) ∈ outSeg u c d from ⟨rfl, le_rfl, hcd⟩)
        have hd := htseg (show (u, d) ∈ outSeg u c d from ⟨rfl, hcd, le_rfl⟩)
        exact (hv u c d (fun p hp => hED (hs hp).1)).trans
          ((mul_le_mul le_rfl (ENNReal.ofReal_le_ofReal (by
            linarith [hc.1, hc.2.1, hd.2.2])) bot_le bot_le).trans hvar)
      · simp [Icc_eq_empty_of_lt (lt_of_not_ge hcd)]
    · intro c d v hs
      have htseg : inSeg c d v ⊆ triangle (t - δ) (t + δ) := fun p hp => (hs hp).2
      by_cases hcd : c ≤ d
      · have hc := htseg (show (c, v) ∈ inSeg c d v from ⟨le_rfl, hcd, rfl⟩)
        have hd := htseg (show (d, v) ∈ inSeg c d v from ⟨hcd, le_rfl, rfl⟩)
        exact (hu c d v (fun p hp => hED (hs hp).1)).trans
          ((mul_le_mul le_rfl (ENNReal.ofReal_le_ofReal (by
            linarith [hc.1, hd.2.1, hd.2.2])) bot_le bot_le).trans hvar)
      · simp [Icc_eq_empty_of_lt (lt_of_not_ge hcd)]
  axis := fun t ht => hS.axis t (hED ht)
  axis_mu := hmu



/-- Specialization of the compact-domain bridge to the entire domain.
Only the axis mass limit remains an explicit internal obligation. -/
theorem IsC1Solution.toIsSolution_of_axis_mu
    {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsC1Solution e S D) (hD : IsCompact D) (hU : UniqueDiffOn ℝ D)
    (hmu : ∀ t, (t, t) ∈ D → Tendsto (Function.uncurry S.mu)
      (𝓝[D ∩ {p | p.1 < p.2}] (t, t)) (𝓝 0)) :
    IsSolution e S D :=
  hS.toIsSolution_on_of_axis_mu hD hU subset_rfl hmu

/-- The old triangle and a strip separated from its axis together form
a broad solution as soon as their C¹ gluing has been proved. The axis
mass limit is inherited from the old triangle: the strip stays outside
a fixed open neighborhood of the diagonal. -/
theorem IsC1Solution.toIsSolution_triangle_strip
    {e S d b : ℝ} {F : Fields} (hS : 0 < S) (hd : 0 < d)
    (hdS : d < S) (hSb : S < b)
    (hF : IsC1Solution e F (triangle 0 S ∪ (Icc 0 d ×ˢ Icc S b))) :
    IsSolution e F (triangle 0 S ∪ (Icc 0 d ×ˢ Icc S b)) := by
  let D := triangle 0 S ∪ (Icc 0 d ×ˢ Icc S b)
  have hcompact : IsCompact D := (isCompact_triangle 0 S).union
    (isCompact_Icc.prod isCompact_Icc)
  have hU : UniqueDiffOn ℝ D := by
    intro p hp
    exact hp.elim
      (fun hp => (uniqueDiffOn_triangle hS p hp).mono subset_union_left)
      (fun hp => (uniqueDiffOn_rectangle hd hSb p hp).mono subset_union_right)
  apply hF.toIsSolution_of_axis_mu hcompact hU
  intro t ht
  have htA : (t, t) ∈ triangle 0 S := by
    rcases ht with ht | ht
    · exact ht
    · have ht1 := ht.1.2
      have ht2 := ht.2.1
      exact False.elim (by linarith)
  have hOld := (hF.mono subset_union_left (uniqueDiffOn_triangle hS)).toIsSolution hS
  have hneigh : {p : ℝ × ℝ | p.2-p.1 < S-d} ∈ 𝓝 (t, t) :=
    (isOpen_lt (continuous_snd.sub continuous_fst) continuous_const).mem_nhds (by
      change t-t < S-d
      linarith)
  have hfilter : 𝓝[D ∩ {p | p.1 < p.2}] (t, t) ≤
      𝓝[triangle 0 S ∩ {p | p.1 < p.2}] (t, t) := by
    apply le_inf inf_le_left
    rw [Filter.le_principal_iff]
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hneigh] with p hp hn
    refine ⟨?_, hp.2⟩
    rcases hp.1 with hp | hp
    · exact hp
    · have hp1 := hp.1.2
      have hp2 := hp.2.1
      exact False.elim (by linarith)
  exact (hOld.axis_mu t htA).mono_left hfilter

end EmcsfAcExtension.Local
