module

public import EmcsfAcExtension.Global.Interaction.PairSource
public import EmcsfAcExtension.Global.Interaction.PairKernel
public import EmcsfAcExtension.Global.Interaction.HistoryPairs
import EmcsfAcExtension.Local.Api.Mono
import Mathlib.Tactic

/-! # Integrated ordered pair source

The outgoing radius integration precedes the incoming integration. Label
separation is cancelled only after the incoming radius substitution.
Source: charged_SF_new_version.tex:L3649–L3663; internal project record `(pair)`.
-/

public section
open Set MeasureTheory
open scoped ENNReal
namespace EmcsfAcExtension.Global.InteractionEstimate

/-- [internal]
The actual ordered geometric pair kernel costs `1/(c²(2-ε))` per ordered
label pair. Its coefficient depends only on the fixed stops, uniformly in
all physical data, scales, stage counts, and durations. -/
theorem pair_source_kernel {e ui u₀ u₁ v₀ ρ δ c Λ F ε : ℝ}
    {S : Fields} {vb : ℝ → ℝ} {N : ℕ}
    (hS : IsSolution e S (origDomain ui))
    (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N)
    (hstop : ExteriorStops S (exteriorDomain ui u₀ u₁ vb) δ c Λ F ε)
    (hc : 0 < c) (hε : ε < 2) (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ u in Icc u₀ u₁, ∫⁻ v in Icc (vb u) 0,
      ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 3) *
        (∫⁻ s in Icc (vb u) v, (∫⁻ t in Icc (vb u) s,
          ENNReal.ofReal (s - t) * G t) * G s)) ≤
      ENNReal.ofReal (1 / (c ^ 2 * (2 - ε))) *
        (∫⁻ s in Icc v₀ 0, ∫⁻ t in Icc v₀ s, G t * G s) := by
  classical
  let E := exteriorDomain ui u₀ u₁ vb
  let I := Icc u₀ u₁
  let w := I.indicator vb
  let K := fun u v => E.indicator
    (fun p => ENNReal.ofReal ((-S.nu p.1 p.2) / S.r p.1 p.2 ^ 3)) (u, v)
  let T := fun u s => ∫⁻ v in Icc s 0, K u v
  let A := fun u s => ∫⁻ t in Icc (w u) s, ENNReal.ofReal (s - t) * G t
  let H := fun t => I ∩ {u | w u ≤ t}
  have hw (u : ℝ) (hu : u ∈ I) : w u = vb u := indicator_of_mem hu _
  have hwm : Measurable w := by
    convert B.cont.measurable_piecewise (g := fun _ => (0 : ℝ))
      continuousOn_const measurableSet_Icc using 1
    ext u
    by_cases hu : u ∈ Icc u₀ u₁ <;> simp [w, I, Set.piecewise, hu]
  have hHm (t : ℝ) : MeasurableSet (H t) :=
    measurableSet_Icc.inter (measurableSet_le hwm measurable_const)
  have hSE : IsSolution e S E := Local.isSolution_mono hS inter_subset_left
  have hr (p : ℝ × ℝ) (hp : p ∈ E) : 0 < S.r p.1 p.2 :=
    hSE.r_pos p hp ((B.off_axis p.1 ⟨hp.2.1, hp.2.2.1⟩).trans_le hp.2.2.2)
  have hKm : Measurable (Function.uncurry K) := measurable_exterior_indicator B _
    (ENNReal.continuous_ofReal.comp_continuousOn
      (hSE.cont_nu.neg.div (hSE.cont_r.pow 3) (fun p hp => pow_ne_zero _ (hr p hp).ne')))
  have hTm : Measurable (Function.uncurry T) := measurable_kernel_tail K hKm 0
  have hAm : Measurable (Function.uncurry A) := measurable_separation_history hwm G hG
  have hbnd (u : ℝ) (hu : u ∈ I) : v₀ ≤ w u ∧ w u ≤ 0 := by
    rw [hw u hu]
    exact finite_boundary_label_bounds B u hu
  have hKeq (u : ℝ) (hu : u ∈ I) (v : ℝ) (hv : v ∈ Icc (vb u) 0) :
      K u v = ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 3) :=
    indicator_of_mem (show (u, v) ∈ E from finite_boundary_row B u hu ⟨rfl, hv⟩) _
  have hhistory (t : ℝ) : H t = {u | u ∈ I ∧ vb u ≤ t} := by
    ext u
    constructor
    · rintro ⟨hu, ht⟩
      exact ⟨hu, by change w u ≤ t at ht; rwa [hw u hu] at ht⟩
    · rintro ⟨hu, ht⟩
      exact ⟨hu, by change w u ≤ t; rw [hw u hu]; exact ht⟩
  have hkernel (s t : ℝ) (hs : s ∈ Icc v₀ 0) (ht : t ∈ Icc v₀ s) :
      (∫⁻ u in H t, ENNReal.ofReal (s - t) * T u s) ≤
        ENNReal.ofReal (1 / (c ^ 2 * (2 - ε))) := by
    obtain ⟨z, hz, hzt, hist, hin⟩ := label_history_later B ⟨ht.1, ht.2.trans hs.2⟩ ht.2 hs.2
    have hsub : H t ⊆ Icc u₀ z := by rw [hhistory, hist]
    have hgeom (u : ℝ) (hu : u ∈ H t) : u < t ∧ outSeg u t 0 ⊆ E := by
      have hvb : vb u ≤ t := by
        have hwu : w u ≤ t := hu.2
        rwa [hw u hu.1] at hwu
      exact ⟨(B.off_axis u hu.1).trans_le hvb,
        fun p hp => finite_boundary_row B u hu.1 ⟨hp.1, hvb.trans hp.2.1, hp.2.2⟩⟩
    obtain ⟨hout, hinc⟩ := ordered_two_label_kernels hSE hz.1 (hzt.le.trans ht.2) hin
      (hHm t) hsub hc hε ht.2 hs.2 hgeom
      (fun u hu v hv => (hstop (u, v) ((hgeom u hu).2 ⟨rfl, hv⟩)).2.2.1)
      (fun u hu v hv => (hstop (u, v) ((hgeom u hu).2 ⟨rfl, hv⟩)).2.2.2.2.2.1)
    have htail (u : ℝ) (hu : u ∈ H t) : T u s ≤
        ENNReal.ofReal ((c * (2 - ε))⁻¹) *
          ENNReal.ofReal ((-S.nu u s) / S.r u s ^ 2) := by
      dsimp only [T]
      have heq : (∫⁻ v in Icc s 0, K u v) =
          ∫⁻ v in Icc s 0, ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 3) := by
        apply setLIntegral_congr_fun measurableSet_Icc
        intro v hv
        have hvb : vb u ≤ t := by
          have hwu : w u ≤ t := hu.2
          rwa [hw u hu.1] at hwu
        exact hKeq u hu.1 v ⟨hvb.trans (ht.2.trans hv.1), hv.2⟩
      rw [heq]
      apply (hout u hu).trans_eq
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    calc
      _ ≤ ∫⁻ u in H t, ENNReal.ofReal (s - t) *
          (ENNReal.ofReal ((c * (2 - ε))⁻¹) * ENNReal.ofReal ((-S.nu u s) / S.r u s ^ 2)) := by
        apply setLIntegral_mono' (hHm t)
        intro u hu
        exact mul_le_mul le_rfl (htail u hu) bot_le bot_le
      _ = ENNReal.ofReal ((c * (2 - ε))⁻¹) *
          (ENNReal.ofReal (s - t) * ∫⁻ u in H t, ENNReal.ofReal ((-S.nu u s) / S.r u s ^ 2)) := by
        simp_rw [mul_left_comm (ENNReal.ofReal (s - t)),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal ((c * (2 - ε))⁻¹) * ENNReal.ofReal c⁻¹ :=
        mul_le_mul le_rfl hinc bot_le bot_le
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
  have hmoment (s : ℝ) (hs : s ∈ Icc v₀ 0) :
      (∫⁻ u in H s, A u s * T u s) ≤
        ENNReal.ofReal (1 / (c ^ 2 * (2 - ε))) * (∫⁻ t in Icc v₀ s, G t) := by
    have hf : Measurable (Function.uncurry (fun u t => ENNReal.ofReal (s - t) * T u s)) :=
      (ENNReal.continuous_ofReal.measurable.comp (measurable_const.sub measurable_snd)).mul
        (hTm.comp (measurable_fst.prodMk measurable_const))
    have heq (t : ℝ) (ht : t ≤ s) : H s ∩ {u | w u ≤ t} = H t := by
      ext u
      simp only [H, mem_inter_iff, mem_ofPred_eq]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.trans ht⟩, h.2⟩⟩
    calc
      _ = ∫⁻ u in H s, ∫⁻ t in Icc (w u) s, (ENNReal.ofReal (s - t) * T u s) * G t := by
        apply setLIntegral_congr_fun (hHm s)
        intro u _
        dsimp only [A]
        have hF : Measurable (fun t => ENNReal.ofReal (s - t) * G t) :=
          (ENNReal.continuous_ofReal.measurable.comp (measurable_const.sub measurable_id)).mul hG
        rw [← lintegral_mul_const (T u s) hF]
        apply lintegral_congr
        intro t
        ring
      _ = ∫⁻ t in Icc v₀ s, G t * ∫⁻ u in H s ∩ {u | w u ≤ t},
          ENNReal.ofReal (s - t) * T u s :=
        lintegral_history_labels (hHm s) hwm (fun u hu => (hbnd u hu.1).1) _ hf G hG
      _ ≤ ∫⁻ t in Icc v₀ s, G t * ENNReal.ofReal (1 / (c ^ 2 * (2 - ε))) := by
        apply setLIntegral_mono' measurableSet_Icc
        intro t ht
        rw [heq t ht.2]
        exact mul_le_mul le_rfl (hkernel s t hs ht) bot_le bot_le
      _ = _ := by
        simp_rw [mul_comm (G _) (ENNReal.ofReal _)]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  calc
    _ = ∫⁻ u in I, ∫⁻ v in Icc (w u) 0, K u v * (∫⁻ s in Icc (w u) v, A u s * G s) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro u hu
      dsimp only
      rw [hw u hu]
      apply setLIntegral_congr_fun measurableSet_Icc
      intro v hv
      dsimp only
      rw [hKeq u hu v hv]
      congr 1
      apply setLIntegral_congr_fun measurableSet_Icc
      intro s _
      dsimp only [A]
      rw [hw u hu]
    _ = ∫⁻ s in Icc v₀ 0, G s * ∫⁻ u in H s, A u s * T u s :=
      lintegral_history_swap measurableSet_Icc hwm hbnd K A hKm hAm G hG
    _ ≤ ∫⁻ s in Icc v₀ 0, G s *
        (ENNReal.ofReal (1 / (c ^ 2 * (2 - ε))) * (∫⁻ t in Icc v₀ s, G t)) := by
      apply setLIntegral_mono' measurableSet_Icc
      intro s hs
      exact mul_le_mul le_rfl (hmoment s hs) bot_le bot_le
    _ = _ := by
      simp_rw [mul_left_comm (G _), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_mul_const _ hG]
      congr 1
      apply lintegral_congr
      intro s
      exact mul_comm _ _

private theorem ordered_separation_of_envelope {a b : ℝ} (hab : a ≤ b)
    (g : ℝ → ℝ) (hg : IntervalIntegrable g volume a b)
    (hg0 : ∀ᵐ s ∂volume.restrict (Icc a b), 0 ≤ g s)
    (G : ℝ → ℝ≥0∞) (_hG : Measurable G)
    (hGeq : (fun s => ENNReal.ofReal (g s)) =ᵐ[volume.restrict (Icc a b)] G) :
    ENNReal.ofReal (∫ s in a..b, (∫ t in a..s, (s - t) * g t) * g s) =
      ∫⁻ s in Icc a b, (∫⁻ t in Icc a s, ENNReal.ofReal (s - t) * G t) * G s := by
  let P := fun s => ∫ t in a..s, (s - t) * g t
  have cP := continuousOn_separation_primitive hab g hg
  have iPg := hg.continuousOn_mul (by simpa only [uIcc_of_le hab] using cP)
  have hP (s : ℝ) (hs : s ∈ Icc a b) : 0 ≤ P s ∧
      ENNReal.ofReal (P s) = ∫⁻ t in Icc a s, ENNReal.ofReal (s - t) * G t := by
    have hsub : Icc a s ⊆ Icc a b := Icc_subset_Icc le_rfl hs.2
    have hsub' : uIcc a s ⊆ uIcc a b := by
      simpa only [uIcc_of_le hs.1, uIcc_of_le hab] using hsub
    have h0 := hg0.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
    have ih : IntervalIntegrable (fun t => (s - t) * g t) volume a s :=
      (hg.mono_set hsub').continuousOn_mul
        ((continuousOn_const : ContinuousOn (fun _ : ℝ => s) (uIcc a s)).sub continuousOn_id)
    have h0p : ∀ᵐ t ∂volume.restrict (Icc a s), 0 ≤ (s - t) * g t := by
      filter_upwards [h0, ae_restrict_mem measurableSet_Icc] with t hgt ht
      exact mul_nonneg (sub_nonneg.mpr ht.2) hgt
    refine ⟨intervalIntegral.integral_nonneg_of_ae_restrict hs.1 h0p, ?_⟩
    dsimp only [P]
    rw [intervalIntegral.integral_of_le hs.1, ← integral_Icc_eq_integral_Ioc,
      ofReal_integral_eq_lintegral_ofReal
        ((intervalIntegrable_iff_integrableOn_Icc_of_le hs.1).mp ih) h0p]
    apply lintegral_congr_ae
    filter_upwards [hGeq.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)),
      ae_restrict_mem measurableSet_Icc] with t hgt ht
    rw [ENNReal.ofReal_mul (sub_nonneg.mpr ht.2), hgt]
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp iPg)
      (by filter_upwards [hg0, ae_restrict_mem measurableSet_Icc] with s hgs hs;
          exact mul_nonneg (hP s hs).1 hgs)]
  apply lintegral_congr_ae
  filter_upwards [hGeq, ae_restrict_mem measurableSet_Icc] with s hgs hs
  rw [ENNReal.ofReal_mul (hP s hs).1, (hP s hs).2, hgs]

/-- [internal]
The actual selected pair source costs the exact coefficient
`3FΛ³/(2δ(1-F²)(2-ε)c⁴)` times `J²`. The positive constant is chosen
from `δ,c,Λ,F,ε` before coupling, solution, boundary, radii, stage count,
envelope, and all durations. Only an `L¹` envelope is assumed. Both
ordered kernels precede the exact half-square label integration.
Source: charged_SF_new_version.tex:L3658–L3663; internal project record `(pair)`. -/
theorem pair_source_integrated (δ c Λ F ε : ℝ)
    (hδ : 0 < δ) (hc : 0 < c) (hΛ : 0 < Λ)
    (hF : 0 ≤ F) (hF1 : F < 1) (hε : ε < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (e ui u₀ u₁ v₀ ρ : ℝ) (S : Fields)
      (vb g : ℝ → ℝ) (N : ℕ) (_B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N),
      IsSolution e S (origDomain ui) →
      ExteriorStops S (exteriorDomain ui u₀ u₁ vb) δ c Λ F ε →
      IntervalIntegrable g volume v₀ 0 →
      (∀ᵐ s ∂volume.restrict (Icc v₀ 0), 0 ≤ g s) →
      (∀ u ∈ Icc u₀ u₁, ∀ᵐ v ∂volume.restrict (Icc (vb u) 0), ‖weightedJ S u v‖ ≤ g v) →
      (∫⁻ u in Icc u₀ u₁, ∫⁻ v in Icc (vb u) 0,
        ENNReal.ofReal ‖curvatureScalarSource S u v (S.theta u v / S.lam u v)
          (radialCurvatureWith S u (vb u) v (radialZSource S u (vb u)))‖) ≤
        ENNReal.ofReal (C * F * (∫ s in v₀..0, g s) ^ 2) := by
  let p := 1 - F ^ 2
  let C := 3 * Λ ^ 3 / (2 * δ * p * (2 - ε) * c ^ 4)
  let β := 3 * F * Λ ^ 3 / (δ * p * c ^ 2)
  have hp : 0 < p := by dsimp [p]; nlinarith only [hF, hF1, sq_nonneg (F - 1)]
  have hC : 0 < C := by dsimp [C]; positivity
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  refine ⟨C, hC, ?_⟩
  intro e ui u₀ u₁ v₀ ρ S vb g N B hS hstop hg hg0 hmajor
  let E := exteriorDomain ui u₀ u₁ vb
  have hSE : IsSolution e S E := Local.isSolution_mono hS inter_subset_left
  have h01 : u₀ ≤ u₁ := calc
    _ = B.cuts 0 := B.first.symm
    _ ≤ B.cuts (Fin.last N) := B.ordered (Fin.zero_le _)
    _ = _ := B.last
  have hv0 : v₀ ≤ 0 := by
    rw [← B.entry_label]
    exact (B.mem u₀ ⟨le_rfl, h01⟩).2.2.2
  let μ := volume.restrict (Icc v₀ 0)
  have ig : Integrable g μ := (intervalIntegrable_iff_integrableOn_Icc_of_le hv0).mp hg
  have hm : AEMeasurable (fun s => ENNReal.ofReal (g s)) μ :=
    ENNReal.continuous_ofReal.measurable.comp_aemeasurable ig.aestronglyMeasurable.aemeasurable
  let G := hm.mk (fun s => ENNReal.ofReal (g s))
  have hG : Measurable G := hm.measurable_mk
  have hGeq : (fun s => ENNReal.ofReal (g s)) =ᵐ[μ] G := hm.ae_eq_mk
  have hpoint (u : ℝ) (hu : u ∈ Icc u₀ u₁) (v : ℝ) (hv : v ∈ Icc (vb u) 0) :
      ENNReal.ofReal ‖curvatureScalarSource S u v (S.theta u v / S.lam u v)
        (radialCurvatureWith S u (vb u) v (radialZSource S u (vb u)))‖ ≤
        ENNReal.ofReal β * (ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 3) *
          (∫⁻ s in Icc (vb u) v, (∫⁻ t in Icc (vb u) s,
            ENNReal.ofReal (s - t) * G t) * G s)) := by
    have hs : outSeg u (vb u) v ⊆ E :=
      fun z hz => finite_boundary_row B u hu ⟨hz.1, hz.2.1, hz.2.2.trans hv.2⟩
    have hsub : Icc (vb u) v ⊆ Icc v₀ 0 :=
      Icc_subset_Icc (finite_boundary_label_bounds B u hu).1 hv.2
    have hsub' : uIcc (vb u) v ⊆ uIcc v₀ 0 := by
      simpa only [uIcc_of_le hv.1, uIcc_of_le hv0] using hsub
    have hg' := hg.mono_set hsub'
    have h0 := hg0.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
    have hmaj := (hmajor u hu).filter_mono
      (ae_mono (Measure.restrict_mono (Icc_subset_Icc le_rfl hv.2) le_rfl))
    have hpt := pair_source_pointwise hSE hstop (B.off_axis u hu) hv.1 hs hδ hc hF hF1 g hg' hmaj
    have heq := ordered_separation_of_envelope hv.1 g hg' h0 G hG
      (hGeq.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)))
    have hn := (neg_pos.mpr (hSE.nu_neg (u, v) (hs ⟨rfl, hv.1, le_rfl⟩))).le
    have hr := hSE.r_pos (u, v) (hs ⟨rfl, hv.1, le_rfl⟩) ((B.off_axis u hu).trans_le hv.1)
    apply (ENNReal.ofReal_le_ofReal hpt).trans_eq
    change ENNReal.ofReal (β * ((-S.nu u v) / S.r u v ^ 3) * _) = _
    rw [ENNReal.ofReal_mul (mul_nonneg hβ (by positivity)), ENNReal.ofReal_mul hβ, heq, mul_assoc]
  calc
    _ ≤ ∫⁻ u in Icc u₀ u₁, ∫⁻ v in Icc (vb u) 0, ENNReal.ofReal β *
        (ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 3) *
          (∫⁻ s in Icc (vb u) v, (∫⁻ t in Icc (vb u) s,
            ENNReal.ofReal (s - t) * G t) * G s)) := by
      apply setLIntegral_mono' measurableSet_Icc
      intro u hu
      exact setLIntegral_mono' measurableSet_Icc (hpoint u hu)
    _ = ENNReal.ofReal β * (∫⁻ u in Icc u₀ u₁, ∫⁻ v in Icc (vb u) 0,
        ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 3) *
          (∫⁻ s in Icc (vb u) v, (∫⁻ t in Icc (vb u) s,
            ENNReal.ofReal (s - t) * G t) * G s)) := by
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal β * (ENNReal.ofReal (1 / (c ^ 2 * (2 - ε))) *
        (∫⁻ s in Icc v₀ 0, ∫⁻ t in Icc v₀ s, G t * G s)) := by
      gcongr
      exact pair_source_kernel hS B hstop hc hε G hG
    _ = _ := by
      rw [lintegral_ordered_label_product_of_real_envelope hv0 g hg hg0 G hG hGeq,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hβ]
      congr 1
      dsimp [β, C]
      field_simp [hp.ne', hδ.ne', hc.ne', (sub_pos.mpr hε).ne']

end EmcsfAcExtension.Global.InteractionEstimate
