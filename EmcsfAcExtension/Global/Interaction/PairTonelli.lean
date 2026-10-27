module

public import EmcsfAcExtension.Infra.Triangle
public import EmcsfAcExtension.Global.Defs.Stages
public import EmcsfAcExtension.Global.Defs.Domains
public import EmcsfAcExtension.Frozen.InSeg
public import EmcsfAcExtension.Frozen.OutSeg
import Mathlib.Tactic
import EmcsfAcExtension.Infra.AC.Primitive
import EmcsfAcExtension.Infra.AC.Quotient

/-! # Moving-history Tonelli identities for interaction sources

This split keeps the physical pair and optical modules below 600 lines.
All identities retain their full finite domains in nonnegative integrals.
Source: charged_SF_new_version.tex:L3641–L3656, L3730–L3773; internal project record.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global.InteractionEstimate

/-- [internal]
Tonelli on the actual moving outgoing triangles and measurable incoming
histories. The outgoing integration is performed before the incoming one;
no separation, endpoint, multiplicity, or duration is discarded. The
identity is valid for extended nonnegative integrals before finiteness.
Source: internal project record auxiliary ordered-domain and incoming-change formulas. -/
theorem lintegral_history_swap {U : Set ℝ} (hU : MeasurableSet U)
    {v₀ : ℝ} {vb : ℝ → ℝ} (hvb : Measurable vb)
    (hbound : ∀ u ∈ U, v₀ ≤ vb u ∧ vb u ≤ 0)
    (K A : ℝ → ℝ → ℝ≥0∞) (hK : Measurable (Function.uncurry K))
    (hA : Measurable (Function.uncurry A)) (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ u in U, ∫⁻ v in Icc (vb u) 0,
      K u v * (∫⁻ s in Icc (vb u) v, A u s * G s)) =
      ∫⁻ s in Icc v₀ 0, G s * ∫⁻ u in U ∩ {u | vb u ≤ s},
        A u s * (∫⁻ v in Icc s 0, K u v) := by
  let T := fun u s => ∫⁻ v in Icc s 0, K u v
  have hT : Measurable (Function.uncurry T) := by
    have hm : Measurable (fun p : (ℝ × ℝ) × ℝ =>
        {p : (ℝ × ℝ) × ℝ | p.1.2 ≤ p.2 ∧ p.2 ≤ 0}.indicator
          (fun p => K p.1.1 p.2) p) := by
      apply Measurable.indicator
      · exact hK.comp (measurable_fst.fst.prodMk measurable_snd)
      · exact (measurableSet_le measurable_fst.snd measurable_snd).inter
          (measurableSet_le measurable_snd measurable_const)
    convert hm.lintegral_prod_right' (ν := volume) using 1
    ext p
    dsimp only [Function.uncurry, T]
    rw [← lintegral_indicator measurableSet_Icc]
    apply lintegral_congr
    intro v
    simp only [indicator, mem_Icc, mem_ofPred_eq]
  have hrow (u : ℝ) :
      (∫⁻ v in Icc (vb u) 0, K u v * (∫⁻ s in Icc (vb u) v, A u s * G s)) =
        ∫⁻ s in Icc (vb u) 0, A u s * G s * T u s := by
    have hF : Measurable (fun p : ℝ × ℝ => (A u p.1 * G p.1) * K u p.2) :=
      ((hA.comp (measurable_const.prodMk measurable_fst)).mul
        (hG.comp measurable_fst)).mul (hK.comp (measurable_const.prodMk measurable_snd))
    calc
      _ = ∫⁻ v in Icc (vb u) 0, ∫⁻ s in Icc (vb u) v, (A u s * G s) * K u v := by
        apply lintegral_congr
        intro v
        have hAu : Measurable (fun s => A u s * G s) :=
          (hA.comp (measurable_const.prodMk measurable_id)).mul hG
        have hh := lintegral_mul_const (μ := volume.restrict (Icc (vb u) v)) (K u v) hAu
        rw [hh]
        exact mul_comm _ _
      _ = ∫⁻ s in Icc (vb u) 0, ∫⁻ v in Icc s 0, (A u s * G s) * K u v :=
        (EmcsfAcExtension.lintegral_lintegral_swap_triangle hF).symm
      _ = _ := by
        apply lintegral_congr
        intro s
        exact lintegral_const_mul _ (hK.comp (measurable_const.prodMk measurable_id))
  let F := fun u s => (Ici (vb u)).indicator (fun s => A u s * G s * T u s) s
  have hF : Measurable (Function.uncurry F) := by
    exact (((hA.mul (hG.comp measurable_snd)).mul hT).indicator
      (measurableSet_le (hvb.comp measurable_fst) measurable_snd))
  calc
    _ = ∫⁻ u in U, ∫⁻ s in Icc v₀ 0, F u s := by
      apply setLIntegral_congr_fun hU
      intro u hu
      dsimp only
      rw [hrow]
      dsimp only [F]
      rw [lintegral_indicator measurableSet_Ici,
        Measure.restrict_restrict measurableSet_Ici]
      have hset : Ici (vb u) ∩ Icc v₀ 0 = Icc (vb u) 0 := by
        ext s
        simp only [mem_inter_iff, mem_Ici, mem_Icc]
        exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, (hbound u hu).1.trans h.1, h.2⟩⟩
      rw [hset]
    _ = ∫⁻ s in Icc v₀ 0, ∫⁻ u in U, F u s := lintegral_lintegral_swap hF.aemeasurable
    _ = _ := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro s _
      change (∫⁻ u in U, F u s) = G s * ∫⁻ u in U ∩ {u | vb u ≤ s}, A u s * T u s
      have hs : MeasurableSet {u | vb u ≤ s} := measurableSet_le hvb measurable_const
      have heq : (fun u => F u s) =
          {u | vb u ≤ s}.indicator (fun u => G s * (A u s * T u s)) := by
        funext u
        dsimp [F]
        by_cases hu : vb u ≤ s <;> simp [hu, mul_assoc, mul_left_comm]
      rw [heq, lintegral_indicator hs, Measure.restrict_restrict hs, inter_comm]
      exact lintegral_const_mul _
        (((hA.comp (measurable_id.prodMk measurable_const)).mul
          (hT.comp (measurable_id.prodMk measurable_const))))

end EmcsfAcExtension.Global.InteractionEstimate

namespace EmcsfAcExtension.Global.InteractionEstimate

/-- [internal]
Exchange incoming time with one contributing label on the exact history
set. This nonnegative identity retains the moving lower endpoint and is
valid before proving finiteness, without a duration or multiplicity factor.
Source: internal project record auxiliary ordered-domain formula. -/
theorem lintegral_history_labels {U : Set ℝ} (hU : MeasurableSet U)
    {a b : ℝ} {vb : ℝ → ℝ} (hvb : Measurable vb)
    (hbound : ∀ u ∈ U, a ≤ vb u)
    (f : ℝ → ℝ → ℝ≥0∞) (hf : Measurable (Function.uncurry f))
    (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ u in U, ∫⁻ s in Icc (vb u) b, f u s * G s) =
      ∫⁻ s in Icc a b, G s * (∫⁻ u in U ∩ {u | vb u ≤ s}, f u s) := by
  let F := fun u s => (Ici (vb u)).indicator (fun s => f u s * G s) s
  have hF : Measurable (Function.uncurry F) :=
    (hf.mul (hG.comp measurable_snd)).indicator
      (measurableSet_le (hvb.comp measurable_fst) measurable_snd)
  calc
    _ = ∫⁻ u in U, ∫⁻ s in Icc a b, F u s := by
      apply setLIntegral_congr_fun hU
      intro u hu
      dsimp only [F]
      rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
      have hset : Ici (vb u) ∩ Icc a b = Icc (vb u) b := by
        ext s
        simp only [mem_inter_iff, mem_Ici, mem_Icc]
        exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, (hbound u hu).trans h.1, h.2⟩⟩
      rw [hset]
    _ = ∫⁻ s in Icc a b, ∫⁻ u in U, F u s := lintegral_lintegral_swap hF.aemeasurable
    _ = _ := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro s _
      dsimp only
      have hs : MeasurableSet {u | vb u ≤ s} := measurableSet_le hvb measurable_const
      have heq : (fun u => F u s) = {u | vb u ≤ s}.indicator (fun u => G s * f u s) := by
        funext u
        dsimp [F]
        by_cases hu : vb u ≤ s <;> simp [hu, mul_comm]
      rw [heq, lintegral_indicator hs, Measure.restrict_restrict hs, inter_comm]
      have hm : Measurable (fun u => f u s) := hf.comp (measurable_id.prodMk measurable_const)
      exact lintegral_const_mul _ hm

/-- [internal]
The actual finite stopped exterior is measurable. The boundary graph is
extended measurably only for this domain calculation; its values and all
solution objects on the closed construction interval remain literal. -/
theorem measurableSet_exteriorDomain {ui u₀ u₁ v₀ ρ : ℝ} {S : Fields}
    {vb : ℝ → ℝ} {N : ℕ} (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) :
    MeasurableSet (exteriorDomain ui u₀ u₁ vb) := by
  classical
  let w := (Icc u₀ u₁).indicator vb
  have hw : Measurable w := by
    convert B.cont.measurable_piecewise (g := fun _ => (0 : ℝ))
      continuousOn_const measurableSet_Icc using 1
    ext u
    by_cases hu : u ∈ Icc u₀ u₁ <;> simp [w, Set.piecewise, hu]
  have heq : exteriorDomain ui u₀ u₁ vb =
      {p : ℝ × ℝ | p.1 ∈ Icc u₀ u₁ ∧ w p.1 ≤ p.2 ∧ p.2 ≤ 0} := by
    ext p
    constructor
    · rintro ⟨hp, hu, hu', hv⟩
      have hi : p.1 ∈ Icc u₀ u₁ := ⟨hu, hu'⟩
      exact ⟨hi, by simpa only [w, indicator_of_mem hi] using hv, hp.2.2.2⟩
    · rintro ⟨hi, hv, hv0⟩
      have hv' : vb p.1 ≤ p.2 := by simpa only [w, indicator_of_mem hi] using hv
      exact ⟨⟨(B.mem p.1 hi).1, (B.mem p.1 hi).2.1,
        (B.off_axis p.1 hi).le.trans hv', hv0⟩, hi.1, hi.2, hv'⟩
  rw [heq]
  exact (measurableSet_Icc.preimage measurable_fst).inter
    ((measurableSet_le (hw.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const))

/-- [internal]
A continuous nonnegative kernel on the actual stopped exterior has a
measurable zero extension. This supplies the geometric kernels used in
Tonelli; it imposes no regularity on fields outside the solution domain. -/
theorem measurable_exterior_indicator {ui u₀ u₁ v₀ ρ : ℝ} {S : Fields}
    {vb : ℝ → ℝ} {N : ℕ} (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N)
    (f : ℝ × ℝ → ℝ≥0∞) (hf : ContinuousOn f (exteriorDomain ui u₀ u₁ vb)) :
    Measurable ((exteriorDomain ui u₀ u₁ vb).indicator f) := by
  classical
  exact hf.measurable_piecewise continuousOn_const (measurableSet_exteriorDomain B)

/-- [internal] The actual finite boundary's complete exterior row lies in
the unchanged exterior domain, including both outgoing endpoints. -/
theorem finite_boundary_row {ui u₀ u₁ v₀ ρ : ℝ} {S : Fields}
    {vb : ℝ → ℝ} {N : ℕ} (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N)
    (u : ℝ) (hu : u ∈ Icc u₀ u₁) :
    outSeg u (vb u) 0 ⊆ exteriorDomain ui u₀ u₁ vb := by
  rintro ⟨x, v⟩ ⟨hx, hv⟩
  dsimp only at hx
  subst x
  exact ⟨⟨(B.mem u hu).1, (B.mem u hu).2.1,
    (B.off_axis u hu).le.trans hv.1, hv.2⟩, hu.1, hu.2, hv.1⟩

/-- [internal] All actual boundary labels lie between the entry label and
zero. This follows from the finite path's monotonicity and original-domain
membership, with no additional geometric premise. -/
theorem finite_boundary_label_bounds {ui u₀ u₁ v₀ ρ : ℝ} {S : Fields}
    {vb : ℝ → ℝ} {N : ℕ} (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N)
    (u : ℝ) (hu : u ∈ Icc u₀ u₁) : v₀ ≤ vb u ∧ vb u ≤ 0 := by
  have h01 : u₀ ≤ u₁ := calc
    _ = B.cuts 0 := B.first.symm
    _ ≤ B.cuts (Fin.last N) := B.ordered (Fin.zero_le _)
    _ = _ := B.last
  refine ⟨?_, (B.mem u hu).2.2.2⟩
  rw [← B.entry_label]
  exact B.mono ⟨le_rfl, h01⟩ hu hu.1

/-- [internal]
Every contributing incoming history of the actual finite stopped exterior
is one closed interval inside the solution domain, with a strictly
off-axis last point. Arbitrary measurable portions can therefore use the
incoming change-of-variables kernels without a component count. The last
point is geometric data and no uniform estimate is selected from it. -/
theorem label_history_interval {ui u₀ u₁ v₀ ρ : ℝ} {S : Fields}
    {vb : ℝ → ℝ} {N : ℕ} (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N)
    {v : ℝ} (hv : v ∈ Icc v₀ 0) :
    ∃ t ∈ Icc u₀ u₁, t < v ∧
      {u | u ∈ Icc u₀ u₁ ∧ vb u ≤ v} = Icc u₀ t ∧
      inSeg u₀ t v ⊆ exteriorDomain ui u₀ u₁ vb := by
  have h01 : u₀ ≤ u₁ := calc
    _ = B.cuts 0 := B.first.symm
    _ ≤ B.cuts (Fin.last N) := B.ordered (Fin.zero_le _)
    _ = _ := B.last
  let U := {u | u ∈ Icc u₀ u₁ ∧ vb u ≤ v}
  have hU : IsCompact U := isCompact_Icc.of_isClosed_subset
    (isClosed_Icc.isClosed_le B.cont continuousOn_const) (fun _ hu => hu.1)
  have hu0 : u₀ ∈ U := ⟨⟨le_rfl, h01⟩, by simpa only [B.entry_label] using hv.1⟩
  obtain ⟨t, ht, hmax⟩ := hU.exists_isMaxOn ⟨u₀, hu0⟩ continuousOn_id
  have hset : U = Icc u₀ t := by
    ext u
    constructor
    · intro hu
      exact ⟨hu.1.1, hmax hu⟩
    · intro hu
      have hui : u ∈ Icc u₀ u₁ := ⟨hu.1, hu.2.trans ht.1.2⟩
      exact ⟨hui, (B.mono hui ht.1 hu.2).trans ht.2⟩
  refine ⟨t, ht.1, (B.off_axis t ht.1).trans_le ht.2, hset, ?_⟩
  rintro ⟨u, w⟩ ⟨hu, hut, rfl⟩
  have humem : u ∈ U := hset.symm ▸ (show u ∈ Icc u₀ t from ⟨hu, hut⟩)
  exact ⟨⟨(B.mem u humem.1).1, (B.mem u humem.1).2.1,
    (B.off_axis u humem.1).le.trans humem.2, hv.2⟩,
      humem.1.1, humem.1.2, humem.2⟩

/-- [internal]
Exact ordered product identity for an `L¹` label density. Its universal
coefficient is `1/2`; no square integrability of the density is assumed.
The proof differentiates the square of its AC primitive.
Source: charged_SF_new_version.tex:L3657–L3662. -/
theorem integral_ordered_label_product {a b : ℝ} (_hab : a ≤ b)
    (g : ℝ → ℝ) (hg : IntervalIntegrable g volume a b) :
    (∫ s in a..b, (∫ t in a..s, g t) * g s) = (∫ s in a..b, g s) ^ 2 / 2 := by
  let P := fun s => ∫ t in a..s, g t
  have hP := hg.absolutelyContinuousOnInterval_intervalIntegral_normed left_mem_uIcc
  have cP := intervalIntegral.continuousOn_primitive_interval' hg left_mem_uIcc
  have iPg := hg.continuousOn_mul cP
  have hsq : AbsolutelyContinuousOnInterval (fun s => P s ^ 2 / 2) a b := by
    convert (hP.mul_normed_ring hP).const_mul (1 / 2 : ℝ) using 1
    funext s
    dsimp only [P, Pi.mul_apply]
    ring
  have hd : ∀ᵐ s, s ∈ uIcc a b → HasDerivAt (fun x => P x ^ 2 / 2) (P s * g s) s := by
    filter_upwards [hg.ae_hasDerivAt_integral] with s hs hsm
    apply (((hs hsm a left_mem_uIcc).pow 2).div_const 2).congr_deriv
    dsimp only [P]
    ring
  have heq := hsq.integral_eq_sub_of_ae_hasDerivAt_normed iPg hd
  simpa only [P, intervalIntegral.integral_same, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_div, sub_zero] using! heq

/-- [internal]
The ordered nonnegative label mass of any measurable representative of a
real nonnegative `L¹` envelope is exactly half its squared mass. This is
the precise diagonal-free factor used after both ordered radius kernels;
its only coefficient is the universal `1/2`.
Source: charged_SF_new_version.tex:L3657–L3662. -/
theorem lintegral_ordered_label_product_of_real_envelope {a b : ℝ} (hab : a ≤ b)
    (g : ℝ → ℝ) (hg : IntervalIntegrable g volume a b)
    (hg0 : ∀ᵐ s ∂volume.restrict (Icc a b), 0 ≤ g s)
    (G : ℝ → ℝ≥0∞) (hG : Measurable G)
    (hGeq : (fun s => ENNReal.ofReal (g s)) =ᵐ[volume.restrict (Icc a b)] G) :
    (∫⁻ s in Icc a b, ∫⁻ t in Icc a s, G t * G s) =
      ENNReal.ofReal ((∫ s in a..b, g s) ^ 2 / 2) := by
  let P := fun s => ∫ t in a..s, g t
  have cP := intervalIntegral.continuousOn_primitive_interval' hg left_mem_uIcc
  have iPg := hg.continuousOn_mul cP
  have hP (s : ℝ) (hs : s ∈ Icc a b) : 0 ≤ P s ∧
      ENNReal.ofReal (P s) = ∫⁻ t in Icc a s, G t := by
    have hsub : Icc a s ⊆ Icc a b := Icc_subset_Icc le_rfl hs.2
    have hsub' : uIcc a s ⊆ uIcc a b := by
      simpa only [uIcc_of_le hs.1, uIcc_of_le hab] using hsub
    have h0 := hg0.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
    refine ⟨intervalIntegral.integral_nonneg_of_ae_restrict hs.1 h0, ?_⟩
    dsimp only [P]
    rw [intervalIntegral.integral_of_le hs.1, ← integral_Icc_eq_integral_Ioc,
      ofReal_integral_eq_lintegral_ofReal
        ((intervalIntegrable_iff_integrableOn_Icc_of_le hs.1).mp (hg.mono_set hsub')) h0]
    exact lintegral_congr_ae (hGeq.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)))
  calc
    _ = ∫⁻ s in Icc a b, ENNReal.ofReal (P s * g s) := by
      apply lintegral_congr_ae
      filter_upwards [hGeq, ae_restrict_mem measurableSet_Icc] with s hgs hs
      rw [lintegral_mul_const _ hG, ← (hP s hs).2, ← hgs, ← ENNReal.ofReal_mul (hP s hs).1]
    _ = ENNReal.ofReal (∫ s in a..b, P s * g s) := by
      rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
      symm
      exact ofReal_integral_eq_lintegral_ofReal
        ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp iPg)
        (by filter_upwards [hg0, ae_restrict_mem measurableSet_Icc] with s hgs hs;
            exact mul_nonneg (hP s hs).1 hgs)
    _ = _ := by rw [integral_ordered_label_product hab g hg]

end EmcsfAcExtension.Global.InteractionEstimate

namespace EmcsfAcExtension.Global.InteractionEstimate

/-- [internal]
The exact two-label square identity retains the finite endpoint
`b - max s t`. The identity has no constants and allows infinite masses;
Tonelli is applied before any integrability conclusion.
Source: charged_SF_new_version.tex:L3756–L3765. -/
theorem lintegral_prefix_square_eq {a b : ℝ} (_hab : a ≤ b)
    (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ x in Icc a b, (∫⁻ s in Icc a x, G s) ^ 2) =
      ∫⁻ s in Icc a b, ∫⁻ t in Icc a b,
        ENNReal.ofReal (b - max s t) * G s * G t := by
  let μ := volume.restrict (Icc a b)
  let F := fun (x : ℝ) (z : ℝ × ℝ) =>
    (Ici (max z.1 z.2)).indicator (fun _ => G z.1 * G z.2) x
  have hF : Measurable (Function.uncurry F) := by
    change Measurable ({p : ℝ × (ℝ × ℝ) | max p.2.1 p.2.2 ≤ p.1}.indicator
      (fun p => G p.2.1 * G p.2.2))
    exact ((hG.comp measurable_snd.fst).mul (hG.comp measurable_snd.snd)).indicator
      (measurableSet_le (measurable_snd.fst.max measurable_snd.snd) measurable_fst)
  have hprefix (x : ℝ) (hx : x ∈ Icc a b) :
      (∫⁻ s in Icc a x, G s) ^ 2 = ∫⁻ z, F x z ∂(μ.prod μ) := by
    have hFx : Measurable (F x) := hF.comp (measurable_const.prodMk measurable_id)
    rw [lintegral_prod _ hFx.aemeasurable]
    have hsep (s t : ℝ) : F x (s, t) =
        (Iic x).indicator G s * (Iic x).indicator G t := by
      dsimp [F]
      by_cases hs : s ≤ x <;> by_cases ht : t ≤ x <;> simp [hs, ht]
    simp_rw [hsep]
    have hset : Iic x ∩ Icc a b = Icc a x := by
      ext s
      simp only [mem_inter_iff, mem_Iic, mem_Icc]
      exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2.trans hx.2⟩⟩
    have hGI := hG.indicator (measurableSet_Iic : MeasurableSet (Iic x))
    have hI : (∫⁻ s, (Iic x).indicator G s ∂μ) = ∫⁻ s in Icc a x, G s := by
      dsimp only [μ]
      rw [lintegral_indicator measurableSet_Iic,
        Measure.restrict_restrict measurableSet_Iic, hset]
    simp_rw [lintegral_const_mul _ hGI, lintegral_mul_const _ hGI, hI, pow_two]
  have htail (z : ℝ × ℝ) (hz : z ∈ Icc a b ×ˢ Icc a b) :
      (∫⁻ x, F x z ∂μ) = ENNReal.ofReal (b - max z.1 z.2) * G z.1 * G z.2 := by
    have hmaxa : a ≤ max z.1 z.2 := hz.1.1.trans (le_max_left _ _)
    have hmaxb : max z.1 z.2 ≤ b := max_le hz.1.2 hz.2.2
    have hset : Ici (max z.1 z.2) ∩ Icc a b = Icc (max z.1 z.2) b := by
      ext x
      simp only [mem_inter_iff, mem_Ici, mem_Icc]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hmaxa.trans h.1, h.2⟩⟩
    dsimp only [F, μ]
    rw [lintegral_indicator measurableSet_Ici,
      Measure.restrict_restrict measurableSet_Ici, hset, lintegral_const,
      Measure.restrict_apply_univ, Real.volume_Icc]
    ring
  calc
    _ = ∫⁻ x, (∫⁻ z, F x z ∂(μ.prod μ)) ∂μ := by
      exact setLIntegral_congr_fun measurableSet_Icc hprefix
    _ = ∫⁻ z, (∫⁻ x, F x z ∂μ) ∂(μ.prod μ) := lintegral_lintegral_swap hF.aemeasurable
    _ = ∫⁻ z, ENNReal.ofReal (b - max z.1 z.2) * G z.1 * G z.2 ∂(μ.prod μ) := by
      apply lintegral_congr_ae
      dsimp only [μ]
      rw [MeasureTheory.Measure.prod_restrict]
      exact ae_restrict_of_forall_mem (measurableSet_Icc.prod measurableSet_Icc) (fun z hz =>
        htail z hz)
    _ = _ := by
      rw [lintegral_prod]
      fun_prop

end EmcsfAcExtension.Global.InteractionEstimate
