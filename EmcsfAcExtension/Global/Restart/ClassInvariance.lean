module

public import EmcsfAcExtension.Global.Defs.Relabel
public import EmcsfAcExtension.Frozen.IsSolution
import EmcsfAcExtension.Global.Api.Definitions
import EmcsfAcExtension.Global.Api.Domains
import EmcsfAcExtension.Infra.Null.IntegralForm
import EmcsfAcExtension.Infra.AC.Relabel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Invariance of the frozen class under common null relabeling

One-dimensional substitution transports every integral equation, including its
integrability. Compact Jacobian and expansion bounds give uniform characteristic
BV. Exact partition variation and continuity transport the two axis limits.
The final theorem verifies all 22 frozen fields separately, without a second
coordinate derivative or absolute continuity of the Jacobian.
-/

public section

open Set MeasureTheory Filter Topology

namespace EmcsfAcExtension.Global

/-- [internal] A null label has its continuous, strictly positive derivative everywhere. -/
theorem IsNullRelabel.hasDerivAt {F : ℝ ≃o ℝ} (hF : IsNullRelabel F) (t : ℝ) :
    HasDerivAt (F : ℝ → ℝ) (deriv (F : ℝ → ℝ) t) t :=
  (hF.1.differentiable (by norm_num) t).hasDerivAt

namespace Restart

/-- [internal] A common increasing label carries a triangle to the corresponding triangle. -/
theorem nullLabel_mem_triangle_iff (F : ℝ ≃o ℝ) (a b u v : ℝ) :
    (F u, F v) ∈ triangle (F a) (F b) ↔ (u, v) ∈ triangle a b := by
  simp only [mem_triangle, F.le_iff_le]

/-- [internal] A common label maps every outgoing segment onto its endpoint image. -/
theorem nullLabel_image_outSeg (F : ℝ ≃o ℝ) (u a b : ℝ) :
    (fun p : ℝ × ℝ => (F p.1, F p.2)) '' outSeg u a b = outSeg (F u) (F a) (F b) := by
  ext p
  constructor
  · rintro ⟨q, ⟨hq, ha, hb⟩, rfl⟩
    exact ⟨congrArg F hq, F.monotone ha, F.monotone hb⟩
  · rintro ⟨hu, ha, hb⟩
    refine ⟨(F.symm p.1, F.symm p.2), ?_, by simp⟩
    exact ⟨by simpa using congrArg F.symm hu,
      by simpa using F.symm.monotone ha, by simpa using F.symm.monotone hb⟩

/-- [internal] A common label maps every incoming segment onto its endpoint image. -/
theorem nullLabel_image_inSeg (F : ℝ ≃o ℝ) (a b v : ℝ) :
    (fun p : ℝ × ℝ => (F p.1, F p.2)) '' inSeg a b v = inSeg (F a) (F b) (F v) := by
  ext p
  constructor
  · rintro ⟨q, ⟨ha, hb, hq⟩, rfl⟩
    exact ⟨F.monotone ha, F.monotone hb, congrArg F hq⟩
  · rintro ⟨ha, hb, hv⟩
    refine ⟨(F.symm p.1, F.symm p.2), ?_, by simp⟩
    exact ⟨by simpa using F.symm.monotone ha, by simpa using F.symm.monotone hb,
      by simpa using congrArg F.symm hv⟩

/-- [internal] Outgoing sections in a triangle map to sections of the image triangle. -/
theorem outSeg_nullLabel_subset {a b u c d : ℝ} (F : ℝ ≃o ℝ)
    (hs : outSeg u c d ⊆ triangle a b) :
    outSeg (F u) (F c) (F d) ⊆ triangle (F a) (F b) := by
  rw [← nullLabel_image_outSeg]
  rintro _ ⟨p, hp, rfl⟩
  exact (nullLabel_mem_triangle_iff F a b p.1 p.2).2 (hs hp)

/-- [internal] Incoming sections in a triangle map to sections of the image triangle. -/
theorem inSeg_nullLabel_subset {a b c d v : ℝ} (F : ℝ ≃o ℝ)
    (hs : inSeg c d v ⊆ triangle a b) :
    inSeg (F c) (F d) (F v) ⊆ triangle (F a) (F b) := by
  rw [← nullLabel_image_inSeg]
  rintro _ ⟨p, hp, rfl⟩
  exact (nullLabel_mem_triangle_iff F a b p.1 p.2).2 (hs hp)

/-- [internal] Increasing common labels preserve ordinary sectional variation exactly. -/
theorem variation_comp_nullLabel {E : Type*} [PseudoEMetricSpace E]
    (f : ℝ → E) (F : ℝ ≃o ℝ) (a b : ℝ) :
    eVariationOn (fun t => f (F t)) (Icc a b) =
      eVariationOn f (Icc (F a) (F b)) := by
  exact eVariationOn.comp_Icc_eq_of_monotoneOn f (F.monotone.monotoneOn _) (F.image_Icc a b)

/-- [internal] AC pulls back along a null label on every compact interval. -/
theorem ac_comp_nullLabel {E : Type*} [PseudoMetricSpace E]
    {f : ℝ → E} {F : ℝ ≃o ℝ} (hF : IsNullRelabel F) {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f (F a) (F b)) :
    AbsolutelyContinuousOnInterval (fun t => f (F t)) a b :=
  hf.comp_monotoneOn hF.1.contDiffOn.absolutelyContinuousOnInterval (F.monotone.monotoneOn _)

/-- [internal] Null substitution transports an integral equation, including integrability. -/
theorem integralForm_comp_nullLabel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {F : ℝ ≃o ℝ} (hF : IsNullRelabel F) {a b : ℝ}
    (h : IntegralForm f g (F a) (F b)) :
    IntegralForm (fun t => f (F t))
      (fun t => deriv (F : ℝ → ℝ) t • g (F t)) a b := by
  refine ⟨?_, ?_⟩
  · exact (intervalIntegral.integrable_deriv_smul_comp_iff_of_deriv_nonneg
      F.continuous.continuousOn (fun t _ => hF.hasDerivAt t)
      (fun t _ => (hF.2.1 t).le)).2 h.1
  · exact h.2.trans (intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
      (f := (F : ℝ → ℝ)) (f' := deriv (F : ℝ → ℝ)) (g := g)
      F.continuous.continuousOn (fun t _ => hF.hasDerivAt t)
      (fun t _ => (hF.2.1 t).le)).symm

/-- [internal] A fixed real factor multiplies both sides of an integral equation. -/
theorem integralForm_const_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {a b : ℝ} (c : ℝ) (h : IntegralForm f g a b) :
    IntegralForm (fun t => c • f t) (fun t => c • g t) a b := by
  refine ⟨h.1.smul c, ?_⟩
  rw [← smul_sub, h.2, intervalIntegral.integral_smul]

/-- [internal] The outgoing normalized scalar is invariant under positive null labels. -/
theorem nullPullback_a (S : Fields) {F : ℝ ≃o ℝ} (hF : IsNullRelabel F) (u v : ℝ) :
    (nullPullback S F F).a u v = S.a (F u) (F v) := by
  have hd : ((deriv (F : ℝ → ℝ) v : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hF.2.1 v).ne'
  simp only [Fields.a, nullPullback, Complex.ofReal_mul]
  rw [mul_div_mul_left _ _ hd]

/-- [internal] The incoming normalized scalar is invariant under positive null labels. -/
theorem nullPullback_b (S : Fields) {F : ℝ ≃o ℝ} (hF : IsNullRelabel F) (u v : ℝ) :
    (nullPullback S F F).b u v = S.b (F u) (F v) := by
  have hd : ((deriv (F : ℝ → ℝ) u : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hF.2.1 u).ne'
  simp only [Fields.b, nullPullback, Complex.ofReal_mul]
  rw [mul_div_mul_left _ _ hd]

/-- [internal] Function-level outgoing normalized-field invariance, for AC and TV transport. -/
theorem nullPullback_a_section (S : Fields) {F : ℝ ≃o ℝ} (hF : IsNullRelabel F) (u : ℝ) :
    (nullPullback S F F).a u = fun v => S.a (F u) (F v) :=
  funext (nullPullback_a S hF u)

/-- [internal] Function-level incoming normalized-field invariance, for TV transport. -/
theorem nullPullback_b_section (S : Fields) {F : ℝ ≃o ℝ} (hF : IsNullRelabel F) (u : ℝ) :
    (nullPullback S F F).b u = fun v => S.b (F u) (F v) :=
  funext (nullPullback_b S hF u)

end Restart
end EmcsfAcExtension.Global

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace EmcsfAcExtension.Global.Restart

private theorem weighted_variation_le {f g : ℝ → ℝ} {s : Set ℝ}
    {C D V B : ℝ≥0∞} (hf : ∀ x ∈ s, ‖f x‖ₑ ≤ D) (hg : ∀ x ∈ s, ‖g x‖ₑ ≤ C)
    (hv : eVariationOn f s ≤ V) (hb : eVariationOn g s ≤ B) :
    eVariationOn (fun x => f x * g x) s ≤ D * B + C * V := by
  apply (eVariationOn_fun_mul_le hf hg).trans
  gcongr

private theorem const_variation_le (c : ℝ) (s : Set ℝ) (V : ℝ≥0∞) :
    eVariationOn (fun _ : ℝ => c) s ≤ V := by
  rw [(eVariationOn.eq_zero_iff _).2 (by intros; exact edist_self c)]
  exact zero_le

/-- [internal] A common null label preserves the frozen locally uniform characteristic
BV clause on a closed triangle. The transported bound may depend on the source
triangle, its solution, and the Jacobian bounds and variation on `[a,b]`. -/
theorem relabel_bv_loc {e a b : ℝ} {S : Fields} {F : ℝ ≃o ℝ}
    (hF : IsNullRelabel F) (hS : IsSolution e S (triangle (F a) (F b))) :
    ∀ K ⊆ triangle a b, IsCompact K → ∃ B : ℝ≥0∞, B < ⊤ ∧
      (∀ u v₁ v₂, outSeg u v₁ v₂ ⊆ K →
        eVariationOn ((nullPullback S F F).lam u) (Icc v₁ v₂) ≤ B ∧
        eVariationOn ((nullPullback S F F).nu u) (Icc v₁ v₂) ≤ B ∧
        eVariationOn ((nullPullback S F F).a u) (Icc v₁ v₂) ≤ B ∧
        eVariationOn ((nullPullback S F F).b u) (Icc v₁ v₂) ≤ B) ∧
      (∀ u₁ u₂ v, inSeg u₁ u₂ v ⊆ K →
        eVariationOn (fun u => (nullPullback S F F).lam u v) (Icc u₁ u₂) ≤ B ∧
        eVariationOn (fun u => (nullPullback S F F).nu u v) (Icc u₁ u₂) ≤ B ∧
        eVariationOn (fun u => (nullPullback S F F).a u v) (Icc u₁ u₂) ≤ B ∧
        eVariationOn (fun u => (nullPullback S F F).b u v) (Icc u₁ u₂) ≤ B) := by
  obtain ⟨B, hB, ho, hi⟩ := hS.bv_loc _ Subset.rfl (isCompact_triangle (F a) (F b))
  obtain ⟨Ml, hl⟩ := (isCompact_triangle (F a) (F b)).bddAbove_image hS.cont_lam.norm
  obtain ⟨Mn, hn⟩ := (isCompact_triangle (F a) (F b)).bddAbove_image hS.cont_nu.norm
  obtain ⟨Md, hd⟩ := isCompact_Icc.bddAbove_image hF.1.continuous_deriv_one.continuousOn.norm
  let C := ENNReal.ofReal (max Ml Mn)
  let D := ENNReal.ofReal Md
  let V := eVariationOn (deriv (F : ℝ → ℝ)) (Icc a b)
  have bl {u v : ℝ} (hp : (u, v) ∈ triangle (F a) (F b)) : ‖S.lam u v‖ₑ ≤ C := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal ((hl (mem_image_of_mem _ hp)).trans (le_max_left _ _))
  have bn {u v : ℝ} (hp : (u, v) ∈ triangle (F a) (F b)) : ‖S.nu u v‖ₑ ≤ C := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal ((hn (mem_image_of_mem _ hp)).trans (le_max_right _ _))
  have bd {t : ℝ} (ht : t ∈ Icc a b) : ‖deriv (F : ℝ → ℝ) t‖ₑ ≤ D := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hd (mem_image_of_mem _ ht))
  have vj {c d : ℝ} (hs : Icc c d ⊆ Icc a b) :
      eVariationOn (deriv (F : ℝ → ℝ)) (Icc c d) ≤ V := eVariationOn.mono _ hs
  have hfinite : B + (D * B + C * V) < ⊤ := by
    exact ENNReal.add_lt_top.2 ⟨hB, ENNReal.add_lt_top.2
      ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hB,
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hF.2.2 a b)⟩⟩
  intro K hK _
  refine ⟨B + (D * B + C * V), hfinite, ?_, ?_⟩
  · intro u c d hs
    by_cases hcd : c ≤ d
    · have ht := hs.trans hK
      have he := (outSeg_subset_triangle_iff hcd).1 ht
      have hlabel : Icc c d ⊆ Icc a b := fun t hx =>
        ⟨he.1.trans (he.2.1.trans hx.1), hx.2.trans he.2.2⟩
      have hu : u ∈ Icc a b := ⟨he.1, (he.2.1.trans hcd).trans he.2.2⟩
      have hsource := outSeg_nullLabel_subset F ht
      obtain ⟨hlam, hnu, ha, hb⟩ := ho (F u) (F c) (F d) hsource
      have hp (t : ℝ) (hx : t ∈ Icc c d) : (F u, F t) ∈ triangle (F a) (F b) :=
        (nullLabel_mem_triangle_iff F a b u t).2 (ht ⟨rfl, hx.1, hx.2⟩)
      have hlam' : eVariationOn (fun t => S.lam (F u) (F t)) (Icc c d) ≤ B := by
        rwa [variation_comp_nullLabel]
      have hnu' : eVariationOn (fun t => S.nu (F u) (F t)) (Icc c d) ≤ B := by
        rwa [variation_comp_nullLabel]
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact (weighted_variation_le (fun t hx => bd (hlabel hx))
          (fun t hx => bl (hp t hx)) (vj hlabel) hlam').trans (le_add_left le_rfl)
      · exact (weighted_variation_le (fun _ _ => bd hu) (fun t hx => bn (hp t hx))
          (const_variation_le _ _ _) hnu').trans (le_add_left le_rfl)
      · simpa only [nullPullback_a_section S hF, variation_comp_nullLabel] using ha.trans
          (le_add_right le_rfl : B ≤ B + (D * B + C * V))
      · simpa only [nullPullback_b_section S hF, variation_comp_nullLabel] using hb.trans
          (le_add_right le_rfl : B ≤ B + (D * B + C * V))
    · have hsing := subsingleton_Icc_of_ge (le_of_not_ge hcd)
      refine ⟨?_, ?_, ?_, ?_⟩
      all_goals rw [eVariationOn.subsingleton _ hsing]; exact zero_le
  · intro c d v hs
    by_cases hcd : c ≤ d
    · have ht := hs.trans hK
      have he := (inSeg_subset_triangle_iff hcd).1 ht
      have hlabel : Icc c d ⊆ Icc a b := fun t hx =>
        ⟨he.1.trans hx.1, hx.2.trans (he.2.1.trans he.2.2)⟩
      have hv : v ∈ Icc a b := ⟨(he.1.trans hcd).trans he.2.1, he.2.2⟩
      have hsource := inSeg_nullLabel_subset F ht
      obtain ⟨hlam, hnu, ha, hb⟩ := hi (F c) (F d) (F v) hsource
      have hp (t : ℝ) (hx : t ∈ Icc c d) : (F t, F v) ∈ triangle (F a) (F b) :=
        (nullLabel_mem_triangle_iff F a b t v).2 (ht ⟨hx.1, hx.2, rfl⟩)
      have hlam' : eVariationOn (fun t => S.lam (F t) (F v)) (Icc c d) ≤ B := by
        rw [variation_comp_nullLabel (fun x => S.lam x (F v)) F c d]
        exact hlam
      have hnu' : eVariationOn (fun t => S.nu (F t) (F v)) (Icc c d) ≤ B := by
        rw [variation_comp_nullLabel (fun x => S.nu x (F v)) F c d]
        exact hnu
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact (weighted_variation_le (fun _ _ => bd hv) (fun t hx => bl (hp t hx))
          (const_variation_le _ _ _) hlam').trans (le_add_left le_rfl)
      · exact (weighted_variation_le (fun t hx => bd (hlabel hx))
          (fun t hx => bn (hp t hx)) (vj hlabel) hnu').trans (le_add_left le_rfl)
      · simp only [nullPullback_a_section S hF]
        rw [variation_comp_nullLabel (fun x => S.a x (F v)) F c d]
        exact ha.trans (le_add_right le_rfl)
      · simp only [nullPullback_b_section S hF]
        rw [variation_comp_nullLabel (fun x => S.b x (F v)) F c d]
        exact hb.trans (le_add_right le_rfl)
    · have hsing := subsingleton_Icc_of_ge (le_of_not_ge hcd)
      refine ⟨?_, ?_, ?_, ?_⟩
      all_goals rw [eVariationOn.subsingleton _ hsing]; exact zero_le

private theorem centered_triangle_mapsTo (F : ℝ ≃o ℝ) (t ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ MapsTo (fun p : ℝ × ℝ => (F p.1, F p.2))
      (triangle (t - δ) (t + δ)) (triangle (F t - ε) (F t + ε)) := by
  obtain ⟨d, hd, hmap⟩ := Metric.continuousAt_iff.mp F.continuous.continuousAt ε hε
  have hc {x : ℝ} (hx : t - d / 2 ≤ x ∧ x ≤ t + d / 2) :
      F t - ε ≤ F x ∧ F x ≤ F t + ε := by
    have hx' : dist x t < d := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith only [hx.1, hx.2, hd]
    have hf := hmap hx'
    rw [Real.dist_eq, abs_lt] at hf
    constructor <;> linarith only [hf.1, hf.2]
  refine ⟨d / 2, half_pos hd, ?_⟩
  intro p hp
  exact ⟨(hc ⟨hp.1, hp.2.1.trans hp.2.2⟩).1, F.monotone hp.2.1,
    (hc ⟨hp.1.trans hp.2.1, hp.2.2⟩).2⟩

/-- [internal] The ordinary scalar axis variation modulus is preserved with exactly
the same error, by continuity of the label and exact partition variation invariance. -/
theorem relabel_axis_small_var {e a b : ℝ} {S : Fields} {F : ℝ ≃o ℝ}
    (hS : IsSolution e S (triangle (F a) (F b))) (t : ℝ) (ht : (t, t) ∈ triangle a b)
    (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ u c d, outSeg u c d ⊆ triangle a b ∩ triangle (t - δ) (t + δ) →
        eVariationOn ((nullPullback S F F).phi u) (Icc c d) ≤ ENNReal.ofReal η) ∧
      (∀ c d v, inSeg c d v ⊆ triangle a b ∩ triangle (t - δ) (t + δ) →
        eVariationOn (fun u => (nullPullback S F F).phi u v) (Icc c d) ≤ ENNReal.ofReal η) := by
  obtain ⟨ε, hε, ho, hi⟩ := hS.axis_small_var (F t)
    ((nullLabel_mem_triangle_iff F a b t t).2 ht) η hη
  obtain ⟨δ, hδ, hmap⟩ := centered_triangle_mapsTo F t ε hε
  refine ⟨δ, hδ, ?_, ?_⟩
  · intro u c d hs
    change eVariationOn (fun x => S.phi (F u) (F x)) (Icc c d) ≤ _
    rw [variation_comp_nullLabel]
    apply ho
    rw [← nullLabel_image_outSeg]
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨(nullLabel_mem_triangle_iff F a b p.1 p.2).2 (hs hp).1, hmap (hs hp).2⟩
  · intro c d v hs
    change eVariationOn (fun x => S.phi (F x) (F v)) (Icc c d) ≤ _
    rw [variation_comp_nullLabel (fun x => S.phi x (F v)) F c d]
    apply hi
    rw [← nullLabel_image_inSeg]
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨(nullLabel_mem_triangle_iff F a b p.1 p.2).2 (hs hp).1, hmap (hs hp).2⟩

/-- [internal] The zero mass-ratio axis limit transports through the common label,
with the off-axis domain restriction retained. -/
theorem relabel_axis_mu {e a b : ℝ} {S : Fields} {F : ℝ ≃o ℝ}
    (hS : IsSolution e S (triangle (F a) (F b))) (t : ℝ) (ht : (t, t) ∈ triangle a b) :
    Tendsto (Function.uncurry (nullPullback S F F).mu)
      (𝓝[triangle a b ∩ {p | p.1 < p.2}] (t, t)) (𝓝 0) := by
  change Tendsto (Function.uncurry S.mu ∘ fun p : ℝ × ℝ => (F p.1, F p.2))
    (𝓝[triangle a b ∩ {p | p.1 < p.2}] (t, t)) (𝓝 0)
  apply (hS.axis_mu (F t) ((nullLabel_mem_triangle_iff F a b t t).2 ht)).comp
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨((F.continuous.comp continuous_fst).prodMk
    (F.continuous.comp continuous_snd)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with p hp
  exact ⟨(nullLabel_mem_triangle_iff F a b p.1 p.2).2 hp.1, F.strictMono hp.2⟩

end EmcsfAcExtension.Global.Restart

open Set MeasureTheory Filter Topology

namespace EmcsfAcExtension.Global.Restart

private theorem continuousOn_common_label {E : Type*} [TopologicalSpace E]
    {f : ℝ → ℝ → E} {a b : ℝ} (F : ℝ ≃o ℝ)
    (hf : ContinuousOn (Function.uncurry f) (triangle (F a) (F b))) :
    ContinuousOn (fun p : ℝ × ℝ => f (F p.1) (F p.2)) (triangle a b) :=
  hf.comp ((F.continuous.comp continuous_fst).prodMk
    (F.continuous.comp continuous_snd)).continuousOn
    (fun p hp => (nullLabel_mem_triangle_iff F a b p.1 p.2).2 hp)

/-- [node sec:charged-closure#relabeled-class-invariance]
A common increasing C¹ null coordinate change with positive locally BV
Jacobian preserves every clause of the frozen AC/BV solution class
(`charged_SF_new_version.tex:L3954`–L4161, L4189–L4190; approved internal project record).
This applies also to the canonical inverse, by `IsNullRelabel.symm`.
The local BV witnesses may depend on the fixed solution, triangle and label. -/
theorem relabel_class (e a b : ℝ) (S : Fields) (F : ℝ ≃o ℝ)
    (hF : IsNullRelabel F) (_hab : a < b)
    (hS : IsSolution e S (triangle (F a) (F b))) :
    IsSolution e (nullPullback S F F) (triangle a b) := by
  have rhs (u v : ℝ) := nullPullback_rhs S F F e u v
    (deriv (F : ℝ → ℝ) u) (deriv (F : ℝ → ℝ) v)
    (hF.hasDerivAt u) (hF.hasDerivAt v) (hF.2.1 u) (hF.2.1 v)
  have kuv (u : ℝ) := funext (fun v : ℝ => (rhs u v).1)
  have kmv (u : ℝ) := funext (fun v : ℝ => (rhs u v).2.1)
  have kmu (u : ℝ) := funext (fun v : ℝ => (rhs u v).2.2.1)
  have kqv (u : ℝ) := funext (fun v : ℝ => (rhs u v).2.2.2.1)
  have kqu (u : ℝ) := funext (fun v : ℝ => (rhs u v).2.2.2.2.1)
  have kav (u : ℝ) := funext (fun v : ℝ => (rhs u v).2.2.2.2.2.1)
  have kpv (u : ℝ) := funext (fun v : ℝ => (rhs u v).2.2.2.2.2.2.1)
  have kpu (u : ℝ) := funext (fun v : ℝ => (rhs u v).2.2.2.2.2.2.2.1)
  have kxv (u : ℝ) := funext (fun v : ℝ => (rhs u v).2.2.2.2.2.2.2.2.1)
  have ktu (u : ℝ) := funext (fun v : ℝ => (rhs u v).2.2.2.2.2.2.2.2.2)
  have cju : Continuous (fun p : ℝ × ℝ => deriv (F : ℝ → ℝ) p.1) :=
    hF.1.continuous_deriv_one.comp continuous_fst
  have cjv : Continuous (fun p : ℝ × ℝ => deriv (F : ℝ → ℝ) p.2) :=
    hF.1.continuous_deriv_one.comp continuous_snd
  refine {
    subset := fun _ hp => hp.2.1
    r_pos := ?_
    lam_pos := ?_
    nu_neg := ?_
    one_sub_mu_pos := ?_
    cont_r := continuousOn_common_label F hS.cont_r
    cont_lam := cjv.continuousOn.mul (continuousOn_common_label F hS.cont_lam)
    cont_nu := cju.continuousOn.mul (continuousOn_common_label F hS.cont_nu)
    cont_m := continuousOn_common_label F hS.cont_m
    cont_Q := continuousOn_common_label F hS.cont_Q
    cont_phi := continuousOn_common_label F hS.cont_phi
    cont_A := cju.continuousOn.mul (continuousOn_common_label F hS.cont_A)
    cont_theta := (Complex.continuous_ofReal.comp cjv).continuousOn.mul
      (continuousOn_common_label F hS.cont_theta)
    cont_xi := (Complex.continuous_ofReal.comp cju).continuousOn.mul
      (continuousOn_common_label F hS.cont_xi)
    eq_out := ?_
    eq_in := ?_
    ac_out := ?_
    ac_in := ?_
    bv_loc := relabel_bv_loc hF hS
    axis_small_var := relabel_axis_small_var hS
    axis := ?_
    axis_mu := relabel_axis_mu hS }
  · intro p hp hlt
    exact hS.r_pos (F p.1, F p.2) ((nullLabel_mem_triangle_iff F a b p.1 p.2).2 hp)
      (F.strictMono hlt)
  · intro p hp
    exact mul_pos (hF.2.1 _) (hS.lam_pos _ ((nullLabel_mem_triangle_iff F a b p.1 p.2).2 hp))
  · intro p hp
    exact mul_neg_of_pos_of_neg (hF.2.1 _)
      (hS.nu_neg _ ((nullLabel_mem_triangle_iff F a b p.1 p.2).2 hp))
  · intro p hp
    exact hS.one_sub_mu_pos _ ((nullLabel_mem_triangle_iff F a b p.1 p.2).2 hp)
  · intro u c d huc hcd hs
    obtain ⟨hr, hn, hm, hq, ha, hp, hx⟩ := hS.eq_out (F u) (F c) (F d)
      (F.strictMono huc) (F.monotone hcd) (outSeg_nullLabel_subset F hs)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [nullPullback, smul_eq_mul] using integralForm_comp_nullLabel hF hr
    · simp only [kuv]
      simpa only [nullPullback, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
        integralForm_const_smul (deriv (F : ℝ → ℝ) u) (integralForm_comp_nullLabel hF hn)
    · simp only [kmv]
      simpa only [nullPullback, smul_eq_mul] using integralForm_comp_nullLabel hF hm
    · simp only [kqv]
      simpa only [nullPullback, smul_eq_mul] using integralForm_comp_nullLabel hF hq
    · simp only [kav]
      simpa only [nullPullback, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
        integralForm_const_smul (deriv (F : ℝ → ℝ) u) (integralForm_comp_nullLabel hF ha)
    · simp only [kpv]
      simpa only [nullPullback, Complex.real_smul] using integralForm_comp_nullLabel hF hp
    · simp only [kxv]
      simpa only [nullPullback, Complex.real_smul, Complex.ofReal_mul,
        mul_comm, mul_left_comm, mul_assoc] using
        integralForm_const_smul (deriv (F : ℝ → ℝ) u) (integralForm_comp_nullLabel hF hx)
  · intro c d v hcd hdv hs
    obtain ⟨hr, hl, hm, hq, hp, ht⟩ := hS.eq_in (F c) (F d) (F v)
      (F.monotone hcd) (F.strictMono hdv) (inSeg_nullLabel_subset F hs)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [nullPullback, smul_eq_mul] using integralForm_comp_nullLabel hF hr
    · simp only [kuv]
      simpa only [nullPullback, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
        integralForm_const_smul (deriv (F : ℝ → ℝ) v) (integralForm_comp_nullLabel hF hl)
    · simp only [kmu]
      simpa only [nullPullback, smul_eq_mul] using integralForm_comp_nullLabel hF hm
    · simp only [kqu]
      simpa only [nullPullback, smul_eq_mul] using integralForm_comp_nullLabel hF hq
    · simp only [kpu]
      simpa only [nullPullback, Complex.real_smul] using integralForm_comp_nullLabel hF hp
    · simp only [ktu]
      simpa only [nullPullback, Complex.real_smul, Complex.ofReal_mul,
        mul_comm, mul_left_comm, mul_assoc] using
        integralForm_const_smul (deriv (F : ℝ → ℝ) v) (integralForm_comp_nullLabel hF ht)
  · intro u c d hcd hs
    obtain ⟨hr, hm, hq, hp, ha⟩ := hS.ac_out (F u) (F c) (F d)
      (F.monotone hcd) (outSeg_nullLabel_subset F hs)
    refine ⟨ac_comp_nullLabel (f := S.r (F u)) (a := c) (b := d) hF hr,
      ac_comp_nullLabel (f := S.m (F u)) (a := c) (b := d) hF hm,
      ac_comp_nullLabel (f := S.Q (F u)) (a := c) (b := d) hF hq,
      ac_comp_nullLabel (f := S.phi (F u)) (a := c) (b := d) hF hp, ?_⟩
    simpa only [nullPullback_a_section S hF] using
      ac_comp_nullLabel (f := S.a (F u)) (a := c) (b := d) hF ha
  · intro c d v hcd hs
    obtain ⟨hr, hm, hq, hp⟩ := hS.ac_in (F c) (F d) (F v)
      (F.monotone hcd) (inSeg_nullLabel_subset F hs)
    exact ⟨ac_comp_nullLabel (f := fun x => S.r x (F v)) (a := c) (b := d) hF hr,
      ac_comp_nullLabel (f := fun x => S.m x (F v)) (a := c) (b := d) hF hm,
      ac_comp_nullLabel (f := fun x => S.Q x (F v)) (a := c) (b := d) hF hq,
      ac_comp_nullLabel (f := fun x => S.phi x (F v)) (a := c) (b := d) hF hp⟩
  · intro t ht
    obtain ⟨hr, hm, hq, hln, ha, hb⟩ := hS.axis (F t)
      ((nullLabel_mem_triangle_iff F a b t t).2 ht)
    refine ⟨hr, hm, hq, ?_, ?_, ?_⟩
    · change deriv (F : ℝ → ℝ) t * S.lam (F t) (F t) +
        deriv (F : ℝ → ℝ) t * S.nu (F t) (F t) = 0
      rw [← mul_add, hln, mul_zero]
    · rw [nullPullback_a S hF]
      change S.a (F t) (F t) = S.phi (F t) (F t)
      exact ha
    · rw [nullPullback_b S hF]
      change S.b (F t) (F t) = S.phi (F t) (F t)
      exact hb

end EmcsfAcExtension.Global.Restart
