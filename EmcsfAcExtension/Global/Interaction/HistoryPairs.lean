module

public import EmcsfAcExtension.Global.Interaction.PairTonelli
import Mathlib.Tactic

/-! # Exact two-label histories

Tonelli identities for the actual moving boundary. Finite endpoints and
both label admission conditions are retained before any estimate.
Source: charged_SF_new_version.tex:L3649–L3663, L3756–L3777; internal project record.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global.InteractionEstimate

/-- [internal]
Exchange incoming time and a square of admitted labels, retaining the
intersection history `vb ≤ min s t`. This is an exact nonnegative identity
with no finiteness premises or constants. -/
theorem lintegral_history_square {U : Set ℝ} (hU : MeasurableSet U)
    {a b : ℝ} {vb : ℝ → ℝ} (hvb : Measurable vb)
    (hbound : ∀ u ∈ U, a ≤ vb u ∧ vb u ≤ b)
    (H : ℝ → ℝ × ℝ → ℝ≥0∞) (hH : Measurable (Function.uncurry H)) :
    (∫⁻ u in U, ∫⁻ s in Icc (vb u) b, ∫⁻ t in Icc (vb u) b, H u (s, t)) =
      ∫⁻ s in Icc a b, ∫⁻ t in Icc a b,
        ∫⁻ u in U ∩ {u | vb u ≤ min s t}, H u (s, t) := by
  let μ := volume.restrict (Icc a b)
  let F := fun u (z : ℝ × ℝ) =>
    (Ici (vb u) ×ˢ Ici (vb u)).indicator (H u) z
  have hF : Measurable (Function.uncurry F) := by
    exact hH.indicator
      ((measurableSet_le (hvb.comp measurable_fst) measurable_snd.fst).inter
        (measurableSet_le (hvb.comp measurable_fst) measurable_snd.snd))
  have hrow (u : ℝ) (hu : u ∈ U) :
      (∫⁻ s in Icc (vb u) b, ∫⁻ t in Icc (vb u) b, H u (s, t)) =
        ∫⁻ z, F u z ∂(μ.prod μ) := by
    have hFu : Measurable (F u) := hF.comp (measurable_const.prodMk measurable_id)
    rw [lintegral_prod _ hFu.aemeasurable]
    have hset : Ici (vb u) ∩ Icc a b = Icc (vb u) b := by
      ext t
      simp only [mem_inter_iff, mem_Ici, mem_Icc]
      exact ⟨fun h => ⟨h.1, h.2.2⟩,
        fun h => ⟨h.1, (hbound u hu).1.trans h.1, h.2⟩⟩
    have heq (s : ℝ) : (∫⁻ t, F u (s, t) ∂μ) =
        (Ici (vb u)).indicator (fun s => ∫⁻ t in Icc (vb u) b, H u (s, t)) s := by
      by_cases hs : vb u ≤ s
      · rw [indicator_of_mem (show s ∈ Ici (vb u) from hs)]
        have hf : (fun t => F u (s, t)) = (Ici (vb u)).indicator (fun t => H u (s, t)) := by
          funext t
          simp only [F, indicator, mem_prod, mem_Ici, hs, true_and]
        rw [hf]
        dsimp only [μ]
        rw [lintegral_indicator measurableSet_Ici,
          Measure.restrict_restrict measurableSet_Ici, hset]
      · rw [indicator_of_notMem (show s ∉ Ici (vb u) from hs)]
        have hf : (fun t => F u (s, t)) = 0 := by
          funext t
          simp only [F, indicator, mem_prod, mem_Ici, hs, false_and, ↓reduceIte, Pi.zero_apply]
        rw [hf]
        exact lintegral_zero_fun
    simp_rw [heq]
    dsimp only [μ]
    rw [lintegral_indicator measurableSet_Ici,
      Measure.restrict_restrict measurableSet_Ici, hset]
  have hcol (s t : ℝ) :
      (∫⁻ u in U, F u (s, t)) =
        ∫⁻ u in U ∩ {u | vb u ≤ min s t}, H u (s, t) := by
    have hs : MeasurableSet {u | vb u ≤ min s t} := measurableSet_le hvb measurable_const
    have heq : (fun u => F u (s, t)) = {u | vb u ≤ min s t}.indicator (fun u => H u (s, t)) := by
      funext u
      simp only [F, indicator, mem_prod, mem_Ici, le_min_iff, mem_ofPred_eq]
    rw [heq, lintegral_indicator hs, Measure.restrict_restrict hs, inter_comm]
  calc
    _ = ∫⁻ u in U, ∫⁻ z, F u z ∂(μ.prod μ) := setLIntegral_congr_fun hU hrow
    _ = ∫⁻ z, (∫⁻ u in U, F u z) ∂(μ.prod μ) := lintegral_lintegral_swap hF.aemeasurable
    _ = _ := by
      rw [lintegral_prod _]
      · simp_rw [hcol]
        rfl
      · exact hF.aemeasurable.lintegral_prod_left'

/-- [internal]
The upper outgoing tail of a jointly measurable kernel is jointly
measurable, with its finite upper endpoint retained. -/
theorem measurable_kernel_tail (K : ℝ → ℝ → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (b : ℝ) :
    Measurable (fun p : ℝ × ℝ => ∫⁻ v in Icc p.2 b, K p.1 v) := by
  have hm : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      {p : (ℝ × ℝ) × ℝ | p.1.2 ≤ p.2 ∧ p.2 ≤ b}.indicator
        (fun p => K p.1.1 p.2) p) := by
    exact (hK.comp (measurable_fst.fst.prodMk measurable_snd)).indicator
      ((measurableSet_le measurable_fst.snd measurable_snd).inter
        (measurableSet_le measurable_snd measurable_const))
  convert hm.lintegral_prod_right' (ν := volume) using 1
  ext p
  rw [← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro v
  simp only [indicator, mem_Icc, mem_ofPred_eq]

/-- [internal]
The separation-weighted lower primitive of a measurable label density is
jointly measurable in incoming time and its endpoint. This assertion has
no integrability premise and preserves the moving lower endpoint. -/
theorem measurable_separation_history {vb : ℝ → ℝ} (hvb : Measurable vb)
    (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    Measurable (fun p : ℝ × ℝ => ∫⁻ t in Icc (vb p.1) p.2,
      ENNReal.ofReal (p.2 - t) * G t) := by
  have hm : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      {p : (ℝ × ℝ) × ℝ | vb p.1.1 ≤ p.2 ∧ p.2 ≤ p.1.2}.indicator
        (fun p => ENNReal.ofReal (p.1.2 - p.2) * G p.2) p) := by
    exact ((ENNReal.continuous_ofReal.measurable.comp
      (measurable_fst.snd.sub measurable_snd)).mul (hG.comp measurable_snd)).indicator
      ((measurableSet_le (hvb.comp measurable_fst.fst) measurable_snd).inter
        (measurableSet_le measurable_snd measurable_fst.snd))
  convert hm.lintegral_prod_right' (ν := volume) using 1
  ext p
  rw [← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro t
  simp only [indicator, mem_Icc, mem_ofPred_eq]

/-- [internal]
A label history is a compact incoming interval. Every later admitted
label has its entire incoming segment in the same actual stopped
exterior. No extension of the solution domain is assumed. -/
theorem label_history_later {ui u₀ u₁ v₀ ρ : ℝ} {S : Fields}
    {vb : ℝ → ℝ} {N : ℕ} (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N)
    {t s : ℝ} (ht : t ∈ Icc v₀ 0) (hts : t ≤ s) (hs : s ≤ 0) :
    ∃ z ∈ Icc u₀ u₁, z < t ∧
      {u | u ∈ Icc u₀ u₁ ∧ vb u ≤ t} = Icc u₀ z ∧
      inSeg u₀ z s ⊆ exteriorDomain ui u₀ u₁ vb := by
  obtain ⟨z, hz, hzt, hist, _⟩ := label_history_interval B ht
  refine ⟨z, hz, hzt, hist, ?_⟩
  rintro ⟨u, v⟩ ⟨hu, huz, rfl⟩
  have humem : u ∈ {u | u ∈ Icc u₀ u₁ ∧ vb u ≤ t} := hist.symm ▸ ⟨hu, huz⟩
  exact finite_boundary_row B u humem.1 ⟨rfl, humem.2.trans hts, hs⟩

/-- [internal]
A measurable two-label density integrated over a moving square remains
measurable in incoming time. The finite square endpoints are literal. -/
theorem measurable_history_square {vb : ℝ → ℝ} (hvb : Measurable vb) (b : ℝ)
    (H : ℝ → ℝ × ℝ → ℝ≥0∞) (hH : Measurable (Function.uncurry H)) :
    Measurable (fun u => ∫⁻ s in Icc (vb u) b, ∫⁻ t in Icc (vb u) b, H u (s, t)) := by
  have hT : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      {p : (ℝ × ℝ) × ℝ | vb p.1.1 ≤ p.2 ∧ p.2 ≤ b}.indicator
        (fun p => H p.1.1 (p.1.2, p.2)) p) := by
    exact (hH.comp (measurable_fst.fst.prodMk
      (measurable_fst.snd.prodMk measurable_snd))).indicator
      ((measurableSet_le (hvb.comp measurable_fst.fst) measurable_snd).inter
        (measurableSet_le measurable_snd measurable_const))
  have hinner : Measurable (fun p : ℝ × ℝ => ∫⁻ t in Icc (vb p.1) b, H p.1 (p.2, t)) := by
    convert hT.lintegral_prod_right' (ν := volume) using 1
    ext p
    rw [← lintegral_indicator measurableSet_Icc]
    apply lintegral_congr
    intro t
    simp only [indicator, mem_Icc, mem_ofPred_eq]
  have hQ : Measurable (fun p : ℝ × ℝ =>
      {p : ℝ × ℝ | vb p.1 ≤ p.2 ∧ p.2 ≤ b}.indicator
        (fun p => ∫⁻ t in Icc (vb p.1) b, H p.1 (p.2, t)) p) :=
    hinner.indicator ((measurableSet_le (hvb.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const))
  convert hQ.lintegral_prod_right' (ν := volume) using 1
  ext u
  rw [← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro s
  simp only [indicator, mem_Icc, mem_ofPred_eq]

/-- [internal]
A nonnegative source majorized by an actual row primitive has spacetime
cost at most its uniform incoming tail moment times its label mass.
This helper performs outgoing integration before incoming integration.
Its consumer must prove both the source bound and the tail moment. -/
theorem lintegral_source_of_history_bound {U : Set ℝ} (hU : MeasurableSet U)
    {a : ℝ} {vb : ℝ → ℝ} (hvb : Measurable vb)
    (hbound : ∀ u ∈ U, a ≤ vb u ∧ vb u ≤ 0)
    (f K A : ℝ → ℝ → ℝ≥0∞) (hK : Measurable (Function.uncurry K))
    (hA : Measurable (Function.uncurry A)) (G : ℝ → ℝ≥0∞) (hG : Measurable G)
    {C L : ℝ} (hC : 0 ≤ C)
    (hpoint : ∀ u ∈ U, ∀ v ∈ Icc (vb u) 0,
      f u v ≤ ENNReal.ofReal C * (K u v * (∫⁻ s in Icc (vb u) v, A u s * G s)))
    (htail : ∀ s ∈ Icc a 0,
      (∫⁻ u in U ∩ {u | vb u ≤ s}, A u s * (∫⁻ v in Icc s 0, K u v)) ≤ ENNReal.ofReal L) :
    (∫⁻ u in U, ∫⁻ v in Icc (vb u) 0, f u v) ≤
      ENNReal.ofReal (C * L) * (∫⁻ s in Icc a 0, G s) := by
  calc
    _ ≤ ∫⁻ u in U, ∫⁻ v in Icc (vb u) 0,
        ENNReal.ofReal C * (K u v * (∫⁻ s in Icc (vb u) v, A u s * G s)) := by
      apply setLIntegral_mono' hU
      intro u hu
      exact setLIntegral_mono' measurableSet_Icc (hpoint u hu)
    _ = ENNReal.ofReal C * (∫⁻ u in U, ∫⁻ v in Icc (vb u) 0,
        K u v * (∫⁻ s in Icc (vb u) v, A u s * G s)) := by
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal C * (∫⁻ s in Icc a 0, G s *
        ∫⁻ u in U ∩ {u | vb u ≤ s}, A u s * (∫⁻ v in Icc s 0, K u v)) := by
      rw [lintegral_history_swap hU hvb hbound K A hK hA G hG]
    _ ≤ ENNReal.ofReal C * (∫⁻ s in Icc a 0, G s * ENNReal.ofReal L) := by
      apply mul_le_mul le_rfl _ bot_le bot_le
      apply setLIntegral_mono' measurableSet_Icc
      intro s hs
      exact mul_le_mul le_rfl (htail s hs) bot_le bot_le
    _ = _ := by
      rw [lintegral_mul_const _ hG, ENNReal.ofReal_mul hC]
      ring

/-- [internal]
A nonnegative real `L¹` envelope has a globally measurable nonnegative
representative with the same label mass. The representative changes no
restricted integral and selects no data-dependent estimate constant. -/
theorem exists_measurable_envelope {a b : ℝ} (hab : a ≤ b)
    (g : ℝ → ℝ) (hg : IntervalIntegrable g volume a b)
    (hg0 : ∀ᵐ s ∂volume.restrict (Icc a b), 0 ≤ g s) :
    ∃ G : ℝ → ℝ≥0∞, Measurable G ∧
      (fun s => ENNReal.ofReal (g s)) =ᵐ[volume.restrict (Icc a b)] G ∧
      (∫⁻ s in Icc a b, G s) = ENNReal.ofReal (∫ s in a..b, g s) := by
  have ig := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hg
  have hm : AEMeasurable (fun s => ENNReal.ofReal (g s)) (volume.restrict (Icc a b)) :=
    ENNReal.continuous_ofReal.measurable.comp_aemeasurable ig.aestronglyMeasurable.aemeasurable
  refine ⟨hm.mk _, hm.measurable_mk, hm.ae_eq_mk, ?_⟩
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal ig hg0]
  exact lintegral_congr_ae hm.ae_eq_mk.symm

/-- [internal]
Convert a nonnegative continuous row weight times an `L¹` envelope to its
nonnegative integral. It holds for every measurable representative equal
a.e. on a containing label interval, with no extra regularity of the
envelope. There are no estimate constants. -/
theorem ofReal_integral_weighted_envelope {a b A B : ℝ} (hab : a ≤ b)
    (hsub : Icc a b ⊆ Icc A B) (g : ℝ → ℝ)
    (hg : IntervalIntegrable g volume a b)
    (hg0 : ∀ᵐ s ∂volume.restrict (Icc A B), 0 ≤ g s)
    (G : ℝ → ℝ≥0∞)
    (hGeq : (fun s => ENNReal.ofReal (g s)) =ᵐ[volume.restrict (Icc A B)] G)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Icc a b)) (hw0 : ∀ s ∈ Icc a b, 0 ≤ w s) :
    ENNReal.ofReal (∫ s in a..b, w s * g s) =
      ∫⁻ s in Icc a b, ENNReal.ofReal (w s) * G s := by
  have iw := hg.continuousOn_mul (by simpa only [uIcc_of_le hab] using hw)
  have h0 := hg0.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp iw)
      (by filter_upwards [h0, ae_restrict_mem measurableSet_Icc] with s hgs hs;
          exact mul_nonneg (hw0 s hs) hgs)]
  apply lintegral_congr_ae
  filter_upwards [hGeq.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)),
    ae_restrict_mem measurableSet_Icc] with s hgs hs
  rw [ENNReal.ofReal_mul (hw0 s hs), hgs]

end EmcsfAcExtension.Global.InteractionEstimate
