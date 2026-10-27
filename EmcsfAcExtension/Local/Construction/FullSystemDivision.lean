module

public import EmcsfAcExtension.Local.Construction.FullSystemIntegral
public import EmcsfAcExtension.Local.Calculus.Partials

/-! # Divided products without losing a derivative

internal project record (5): the product of two C¹ fields vanishing on the axis,
divided by the radial width, remains C¹ on the closed wedge. Only the
continuous first jets are averaged; no second derivative is used.
-/

public section

open Set MeasureTheory Complex
open scoped Topology

namespace EmcsfAcExtension.Local.Null

/-- Every point in the ambient interior of a construction wedge is off axis. -/
theorem off_axis_of_mem_interior_wedge {a b c : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ interior (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c})) : p.1 < p.2 := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hp)
  have hdist : dist (p.1, p.2 - ε / 2) p < ε := by
    simp only [Prod.dist_eq, Real.dist_eq, sub_self, abs_zero, sub_sub_cancel_left, abs_neg]
    rw [abs_of_pos (half_pos hε), max_eq_right (half_pos hε).le]
    exact half_lt_self hε
  have h := hball hdist
  exact lt_of_le_of_lt h.1.2.1 (sub_lt_self _ (half_pos hε))

/-- A zero-axis C¹ field equals its radial width times the average of its
outgoing partial. The identity also holds on collapsed radial sections. -/
theorem eq_width_mul_average_pdV {a b c : ℝ} (hac : a < c) (hcb : c ≤ b)
    {f : ℝ → ℝ → ℂ}
    (cf : ContDiffOn ℝ 1 (Function.uncurry f)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hzero : ∀ t ∈ Icc a c, f t t = 0)
    {p : ℝ × ℝ} (hp : p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) :
    f p.1 p.2 = ((p.2 - p.1 : ℝ) : ℂ) *
      ∫ t in (0 : ℝ)..1, pdV (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) f
        p.1 (p.1 + (p.2 - p.1) * t) := by
  have hi := integralForm_pdV cf (uniqueDiffOn_triangle_inter_fst_le hac hcb) hp.1.2.1
    (fun s hs => ⟨⟨hp.1.1, hs.1, hs.2.trans hp.1.2.2⟩, hp.2⟩)
  have hval := hi.2
  rw [hzero p.1 ⟨hp.1.1, hp.2⟩, sub_zero] at hval
  rw [hval, integral_eq_width_smul_radial_average]
  simp only [Complex.real_smul]

/-- Dividing a product of two zero-axis C¹ fields by the radial width
preserves C¹ on the entire closed wedge. The totalized quotient is already
zero on the diagonal. This is internal project record (5), in `(u,v)` coordinates. -/
theorem contDiffOn_divided_product {a b c : ℝ} (hac : a < c) (hcb : c ≤ b)
    {f g : ℝ → ℝ → ℂ}
    (cf : ContDiffOn ℝ 1 (Function.uncurry f)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cg : ContDiffOn ℝ 1 (Function.uncurry g)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hf0 : ∀ t ∈ Icc a c, f t t = 0) (hg0 : ∀ t ∈ Icc a c, g t t = 0) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => f p.1 p.2 * g p.1 p.2 /
      ((p.2 - p.1 : ℝ) : ℂ)) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) := by
  let D := triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}
  let F (p : ℝ × ℝ) := ∫ t in (0 : ℝ)..1, pdV D f p.1 (p.1 + (p.2 - p.1) * t)
  let G (p : ℝ × ℝ) := ∫ t in (0 : ℝ)..1, pdV D g p.1 (p.1 + (p.2 - p.1) * t)
  have hD : UniqueDiffOn ℝ D := uniqueDiffOn_triangle_inter_fst_le hac hcb
  have cF : ContinuousOn F D := continuousOn_radial_average (continuousOn_pdV cf hD)
  have cG : ContinuousOn G D := continuousOn_radial_average (continuousOn_pdV cg hD)
  have hf (p : ℝ × ℝ) (hp : p ∈ D) : f p.1 p.2 = ((p.2 - p.1 : ℝ) : ℂ) * F p :=
    eq_width_mul_average_pdV hac hcb cf hf0 hp
  have hg (p : ℝ × ℝ) (hp : p ∈ D) : g p.1 p.2 = ((p.2 - p.1 : ℝ) : ℂ) * G p :=
    eq_width_mul_average_pdV hac hcb cg hg0 hp
  let U (p : ℝ × ℝ) := pdU D f p.1 p.2 * G p + F p * pdU D g p.1 p.2 + F p * G p
  let V (p : ℝ × ℝ) := pdV D f p.1 p.2 * G p + F p * pdV D g p.1 p.2 - F p * G p
  have cT : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2 * g p.1 p.2 /
      ((p.2 - p.1 : ℝ) : ℂ)) D := by
    apply (((Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_snd.sub continuousOn_fst)).mul cF).mul cG).congr
    intro p hp
    change f p.1 p.2 * g p.1 p.2 / ((p.2 - p.1 : ℝ) : ℂ) =
      ((p.2 - p.1 : ℝ) : ℂ) * F p * G p
    rw [hf p hp, hg p hp]
    by_cases hx : ((p.2 - p.1 : ℝ) : ℂ) = 0
    · simp [hx]
    · field_simp
  have cU : ContinuousOn U D :=
    (((continuousOn_pdU cf hD).mul cG).add (cF.mul (continuousOn_pdU cg hD))).add (cF.mul cG)
  have cV : ContinuousOn V D :=
    (((continuousOn_pdV cf hD).mul cG).add (cF.mul (continuousOn_pdV cg hD))).sub (cF.mul cG)
  apply contDiffOn_wedge_of_interior_sectional_derivatives hac hcb cT cU cV
  · intro p hp
    have hpD : p ∈ D := interior_subset hp
    have hx : ((p.2 - p.1 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (sub_pos.mpr (off_axis_of_mem_interior_wedge hp)).ne'
    have hfu := (((cf.differentiableOn (by norm_num) p hpD).hasFDerivWithinAt).hasFDerivAt
      (mem_interior_iff_mem_nhds.mp hp)).comp_hasDerivAt p.1
      ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
    have hgu := (((cg.differentiableOn (by norm_num) p hpD).hasFDerivWithinAt).hasFDerivAt
      (mem_interior_iff_mem_nhds.mp hp)).comp_hasDerivAt p.1
      ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
    have hd := (hfu.mul hgu).div
      (((hasDerivAt_const p.1 p.2).sub (hasDerivAt_id p.1)).ofReal_comp) hx
    convert hd using 1
    · funext x; rfl
    · dsimp only [U, pdU, Function.comp_apply, Function.uncurry, Pi.mul_apply, Pi.div_apply,
        Pi.sub_apply, id_eq]
      rw [hf p hpD, hg p hpD]
      dsimp only [D]
      simp only [Prod.eta]
      push_cast at hx ⊢
      field_simp [hx]
      ring
  · intro p hp
    have hpD : p ∈ D := interior_subset hp
    have hx : ((p.2 - p.1 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (sub_pos.mpr (off_axis_of_mem_interior_wedge hp)).ne'
    have hfv := (((cf.differentiableOn (by norm_num) p hpD).hasFDerivWithinAt).hasFDerivAt
      (mem_interior_iff_mem_nhds.mp hp)).comp_hasDerivAt p.2
      ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
    have hgv := (((cg.differentiableOn (by norm_num) p hpD).hasFDerivWithinAt).hasFDerivAt
      (mem_interior_iff_mem_nhds.mp hp)).comp_hasDerivAt p.2
      ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
    have hd := (hfv.mul hgv).div
      (((hasDerivAt_id p.2).sub (hasDerivAt_const p.2 p.1)).ofReal_comp) hx
    convert hd using 1
    · funext x; rfl
    · dsimp only [V, pdV, Function.comp_apply, Function.uncurry, Pi.mul_apply, Pi.div_apply,
        Pi.sub_apply, id_eq]
      rw [hf p hpD, hg p hpD]
      dsimp only [D]
      simp only [Prod.eta]
      push_cast at hx ⊢
      field_simp [hx]
      ring
end EmcsfAcExtension.Local.Null
