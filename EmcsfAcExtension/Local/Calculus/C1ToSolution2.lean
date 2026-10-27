module

public import EmcsfAcExtension.Local.Defs.C1Class
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Local.Calculus.C1ToSolution
import EmcsfAcExtension.Local.Calculus.AxisLimits
import EmcsfAcExtension.Infra.Null.IntegralForm
import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # Every classical triangle solution belongs to the frozen class

The regularity clauses follow from uniform Lipschitz bounds on the compact
triangle. Integral equations use the continuous within-domain partials, and
`axis_mu` is supplied by the classical axis-limit argument.
-/

public section

open Set Filter MeasureTheory Topology
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem sectionLipV {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → ℝ → E} {D : Set (ℝ × ℝ)} {K : NNReal}
    (hf : LipschitzOnWith K (Function.uncurry f) D) {u c d : ℝ}
    (hs : outSeg u c d ⊆ D) : LipschitzOnWith K (f u) (Icc c d) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have h := hf.dist_le_mul (u, x) (hs ⟨rfl, hx.1, hx.2⟩)
    (u, y) (hs ⟨rfl, hy.1, hy.2⟩)
  simpa [Prod.dist_eq] using h

private theorem sectionLipU {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → ℝ → E} {D : Set (ℝ × ℝ)} {K : NNReal}
    (hf : LipschitzOnWith K (Function.uncurry f) D) {v c d : ℝ}
    (hs : inSeg c d v ⊆ D) : LipschitzOnWith K (fun u => f u v) (Icc c d) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have h := hf.dist_le_mul (x, v) (hs ⟨hx.1, hx.2, rfl⟩)
    (y, v) (hs ⟨hy.1, hy.2, rfl⟩)
  simpa [Prod.dist_eq] using h

private theorem variation_le_of_lipschitz {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {K : NNReal} {c d : ℝ} (hf : LipschitzOnWith K f (Icc c d)) :
    eVariationOn f (Icc c d) ≤ K * ENNReal.ofReal (d - c) := by
  simpa only [Function.comp_id, eVariationOn_id_Icc] using
    hf.comp_eVariationOn_le (mapsTo_id (Icc c d))

/-- A C¹ field has one positive characteristic variation constant on its whole triangle.
The constant may depend on the field and triangle, uniformly in both sections. -/
theorem c1_characteristic_variation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → ℝ → E} {a b : ℝ}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle a b)) :
    ∃ K : NNReal, 0 < K ∧
      (∀ u c d, outSeg u c d ⊆ triangle a b →
        eVariationOn (f u) (Icc c d) ≤ K * ENNReal.ofReal (d - c)) ∧
      (∀ c d v, inSeg c d v ⊆ triangle a b →
        eVariationOn (fun u => f u v) (Icc c d) ≤ K * ENNReal.ofReal (d - c)) := by
  obtain ⟨K, hK⟩ := hf.exists_lipschitzOnWith (by norm_num)
    (convex_triangle a b) (isCompact_triangle a b)
  have hK' : LipschitzOnWith (K + 1) (Function.uncurry f) (triangle a b) :=
    hK.weaken (le_add_of_nonneg_right bot_le)
  exact ⟨K + 1, by positivity,
    fun _ _ _ hs => variation_le_of_lipschitz (sectionLipV hK' hs),
    fun _ _ _ hs => variation_le_of_lipschitz (sectionLipU hK' hs)⟩

private theorem c1_ac_out {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → ℝ → E} {a b u c d : ℝ}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle a b)) (hcd : c ≤ d)
    (hs : outSeg u c d ⊆ triangle a b) : AbsolutelyContinuousOnInterval (f u) c d := by
  obtain ⟨K, hK⟩ := hf.exists_lipschitzOnWith (by norm_num)
    (convex_triangle a b) (isCompact_triangle a b)
  have hl : LipschitzOnWith K (f u) (uIcc c d) := by
    rw [uIcc_of_le hcd]
    exact sectionLipV hK hs
  exact hl.absolutelyContinuousOnInterval

private theorem c1_ac_in {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → ℝ → E} {a b v c d : ℝ}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle a b)) (hcd : c ≤ d)
    (hs : inSeg c d v ⊆ triangle a b) :
    AbsolutelyContinuousOnInterval (fun u => f u v) c d := by
  obtain ⟨K, hK⟩ := hf.exists_lipschitzOnWith (by norm_num)
    (convex_triangle a b) (isCompact_triangle a b)
  have hl : LipschitzOnWith K (fun u => f u v) (uIcc c d) := by
    rw [uIcc_of_le hcd]
    exact sectionLipU hK hs
  exact hl.absolutelyContinuousOnInterval

private theorem out_form {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f g : ℝ → ℝ → E} {a b u c d : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle a b))
    (heq : ∀ p ∈ triangle a b, p.1 < p.2 → pdV (triangle a b) f p.1 p.2 = g p.1 p.2)
    (huc : u < c) (hcd : c ≤ d) (hs : outSeg u c d ⊆ triangle a b) :
    IntegralForm (f u) (g u) c d := by
  apply (integralForm_pdV hf (uniqueDiffOn_triangle hab) hcd
    (fun x hx => hs ⟨rfl, hx.1, hx.2⟩)).congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIcc] with x hx
  rw [uIcc_of_le hcd] at hx
  exact heq (u, x) (hs ⟨rfl, hx.1, hx.2⟩) (huc.trans_le hx.1)

private theorem in_form {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f g : ℝ → ℝ → E} {a b v c d : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle a b))
    (heq : ∀ p ∈ triangle a b, p.1 < p.2 → pdU (triangle a b) f p.1 p.2 = g p.1 p.2)
    (hcd : c ≤ d) (hdv : d < v) (hs : inSeg c d v ⊆ triangle a b) :
    IntegralForm (fun u => f u v) (fun u => g u v) c d := by
  apply (integralForm_pdU hf (uniqueDiffOn_triangle hab) hcd
    (fun x hx => hs ⟨hx.1, hx.2, rfl⟩)).congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIcc] with x hx
  rw [uIcc_of_le hcd] at hx
  exact heq (x, v) (hs ⟨hx.1, hx.2, rfl⟩) (hx.2.trans_lt hdv)

private theorem variation_out_triangle_bound {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → ℝ → E} {a b : ℝ} {K L : NNReal} (hKL : K ≤ L)
    (hvar : ∀ u c d, outSeg u c d ⊆ triangle a b →
      eVariationOn (f u) (Icc c d) ≤ K * ENNReal.ofReal (d - c))
    {u c d : ℝ} (hs : outSeg u c d ⊆ triangle a b) :
    eVariationOn (f u) (Icc c d) ≤ L * ENNReal.ofReal (b - a) := by
  by_cases hcd : c ≤ d
  · have hc := hs (show (u, c) ∈ outSeg u c d from ⟨rfl, le_rfl, hcd⟩)
    have hd := hs (show (u, d) ∈ outSeg u c d from ⟨rfl, hcd, le_rfl⟩)
    exact (hvar u c d hs).trans (mul_le_mul (by exact_mod_cast hKL)
      (ENNReal.ofReal_le_ofReal (by linarith [hc.1, hc.2.1, hd.2.2])) bot_le bot_le)
  · simp [Icc_eq_empty_of_lt (lt_of_not_ge hcd)]

private theorem variation_in_triangle_bound {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → ℝ → E} {a b : ℝ} {K L : NNReal} (hKL : K ≤ L)
    (hvar : ∀ c d v, inSeg c d v ⊆ triangle a b →
      eVariationOn (fun u => f u v) (Icc c d) ≤ K * ENNReal.ofReal (d - c))
    {v c d : ℝ} (hs : inSeg c d v ⊆ triangle a b) :
    eVariationOn (fun u => f u v) (Icc c d) ≤ L * ENNReal.ofReal (b - a) := by
  by_cases hcd : c ≤ d
  · have hc := hs (show (c, v) ∈ inSeg c d v from ⟨le_rfl, hcd, rfl⟩)
    have hd := hs (show (d, v) ∈ inSeg c d v from ⟨hcd, le_rfl, rfl⟩)
    exact (hvar c d v hs).trans (mul_le_mul (by exact_mod_cast hKL)
      (ENNReal.ofReal_le_ofReal (by linarith [hc.1, hd.2.1, hd.2.2])) bot_le bot_le)
  · simp [Icc_eq_empty_of_lt (lt_of_not_ge hcd)]

variable {a b e : ℝ} {S : Fields}

/-- Every classical solution on a nondegenerate closed triangle satisfies every
field of the frozen AC/BV class on that same triangle (internal project record). -/
theorem IsC1Solution.toIsSolution (hS : IsC1Solution e S (triangle a b)) (hab : a < b) :
    IsSolution e S (triangle a b) where
  subset := hS.subset
  r_pos := hS.r_pos
  lam_pos := hS.lam_pos
  nu_neg := hS.nu_neg
  one_sub_mu_pos := hS.one_sub_mu_pos
  cont_r := hS.c1_r.continuousOn
  cont_lam := hS.c1_lam.continuousOn
  cont_nu := hS.c1_nu.continuousOn
  cont_m := hS.c1_m.continuousOn
  cont_Q := hS.c1_Q.continuousOn
  cont_phi := hS.c1_phi.continuousOn
  cont_A := hS.c1_A.continuousOn
  cont_theta := hS.c1_theta.continuousOn
  cont_xi := hS.c1_xi.continuousOn
  eq_out := by
    intro u c d huc hcd hs
    exact ⟨
      out_form hab hS.c1_r (fun p hp huv => (hS.eq_v p hp huv).1) huc hcd hs,
      out_form hab hS.c1_nu (fun p hp huv => (hS.eq_v p hp huv).2.1) huc hcd hs,
      out_form hab hS.c1_m (fun p hp huv => (hS.eq_v p hp huv).2.2.1) huc hcd hs,
      out_form hab hS.c1_Q (fun p hp huv => (hS.eq_v p hp huv).2.2.2.1) huc hcd hs,
      out_form hab hS.c1_A (fun p hp huv => (hS.eq_v p hp huv).2.2.2.2.1) huc hcd hs,
      out_form hab hS.c1_phi (fun p hp huv => (hS.eq_v p hp huv).2.2.2.2.2.1) huc hcd hs,
      out_form hab hS.c1_xi (fun p hp huv => (hS.eq_v p hp huv).2.2.2.2.2.2) huc hcd hs⟩
  eq_in := by
    intro c d v hcd hdv hs
    exact ⟨
      in_form hab hS.c1_r (fun p hp huv => (hS.eq_u p hp huv).1) hcd hdv hs,
      in_form hab hS.c1_lam (fun p hp huv => (hS.eq_u p hp huv).2.1) hcd hdv hs,
      in_form hab hS.c1_m (fun p hp huv => (hS.eq_u p hp huv).2.2.1) hcd hdv hs,
      in_form hab hS.c1_Q (fun p hp huv => (hS.eq_u p hp huv).2.2.2.1) hcd hdv hs,
      in_form hab hS.c1_phi (fun p hp huv => (hS.eq_u p hp huv).2.2.2.2.1) hcd hdv hs,
      in_form hab hS.c1_theta (fun p hp huv => (hS.eq_u p hp huv).2.2.2.2.2) hcd hdv hs⟩
  ac_out := fun _ _ _ hcd hs => ⟨c1_ac_out hS.c1_r hcd hs,
    c1_ac_out hS.c1_m hcd hs, c1_ac_out hS.c1_Q hcd hs,
    c1_ac_out hS.c1_phi hcd hs, c1_ac_out hS.c1_a hcd hs⟩
  ac_in := fun _ _ _ hcd hs => ⟨c1_ac_in hS.c1_r hcd hs,
    c1_ac_in hS.c1_m hcd hs, c1_ac_in hS.c1_Q hcd hs, c1_ac_in hS.c1_phi hcd hs⟩
  bv_loc := by
    intro K hKD _hcompact
    obtain ⟨Kl, _hKlpos, hlv, hlu⟩ := c1_characteristic_variation hS.c1_lam
    obtain ⟨Kn, _hKnpos, hnv, hnu⟩ := c1_characteristic_variation hS.c1_nu
    obtain ⟨Ka, _hKapos, hav, hau⟩ := c1_characteristic_variation hS.c1_a
    obtain ⟨Kb, _hKbpos, hbv, hbu⟩ := c1_characteristic_variation hS.c1_b
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
    refine ⟨L * ENNReal.ofReal (b - a), by finiteness, ?_, ?_⟩
    · intro u c d hs
      exact ⟨variation_out_triangle_bound hKl hlv (hs.trans hKD),
        variation_out_triangle_bound hKn hnv (hs.trans hKD),
        variation_out_triangle_bound hKa hav (hs.trans hKD),
        variation_out_triangle_bound hKb hbv (hs.trans hKD)⟩
    · intro c d v hs
      exact ⟨variation_in_triangle_bound hKl hlu (hs.trans hKD),
        variation_in_triangle_bound hKn hnu (hs.trans hKD),
        variation_in_triangle_bound hKa hau (hs.trans hKD),
        variation_in_triangle_bound hKb hbu (hs.trans hKD)⟩
  axis_small_var := by
    intro t _ht η hη
    obtain ⟨K, _hKpos, hv, hu⟩ := c1_characteristic_variation hS.c1_phi
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
        exact (hv u c d (fun p hp => (hs hp).1)).trans
          ((mul_le_mul le_rfl (ENNReal.ofReal_le_ofReal (by
            linarith [hc.1, hc.2.1, hd.2.2])) bot_le bot_le).trans hvar)
      · simp [Icc_eq_empty_of_lt (lt_of_not_ge hcd)]
    · intro c d v hs
      have htseg : inSeg c d v ⊆ triangle (t - δ) (t + δ) := fun p hp => (hs hp).2
      by_cases hcd : c ≤ d
      · have hc := htseg (show (c, v) ∈ inSeg c d v from ⟨le_rfl, hcd, rfl⟩)
        have hd := htseg (show (d, v) ∈ inSeg c d v from ⟨hcd, le_rfl, rfl⟩)
        exact (hu c d v (fun p hp => (hs hp).1)).trans
          ((mul_le_mul le_rfl (ENNReal.ofReal_le_ofReal (by
            linarith [hc.1, hd.2.1, hd.2.2])) bot_le bot_le).trans hvar)
      · simp [Icc_eq_empty_of_lt (lt_of_not_ge hcd)]
  axis := hS.axis
  axis_mu := fun t ht => hS.axis_mu hab ⟨ht.1, ht.2.2⟩

end EmcsfAcExtension.Local
