module

public import EmcsfAcExtension.Global.Interaction.IncomingOptics
public import EmcsfAcExtension.Global.Interaction.HistoryPairs
public import EmcsfAcExtension.Global.Interaction.PairSource
public import EmcsfAcExtension.Global.Interaction.PairKernel
import EmcsfAcExtension.Local.Api.Mono
import Mathlib.Tactic

/-! # Incoming optical estimate on the actual finite exterior

The square-source kernel retains its finite endpoint through incoming
radius substitution. Stage budgets and the electromagnetic area moment
are then combined with the actual radial mass reconstruction.
Source: charged_SF_new_version.tex:L3747–L3777; internal project record.
-/

public section
open Set MeasureTheory
open scoped ENNReal
namespace EmcsfAcExtension.Global.InteractionEstimate

/-- [internal]
The incoming square-source geometric kernel costs exactly `c⁻¹ J²`.
The finite endpoint is retained through incoming integration; the
coefficient depends only on `c` before all physical data, labels,
boundaries, stages, radii, and durations. -/
theorem incoming_source_optical_kernel {e ui u₀ u₁ v₀ ρ δ c Λ F ε : ℝ}
    {S : Fields} {vb : ℝ → ℝ} {N : ℕ}
    (hS : IsSolution e S (origDomain ui))
    (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N)
    (hstop : ExteriorStops S (exteriorDomain ui u₀ u₁ vb) δ c Λ F ε)
    (hc : 0 < c) (v : ℝ) (hv : v ∈ Icc v₀ 0)
    (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ u in {u | u ∈ Icc u₀ u₁ ∧ vb u ≤ v},
      ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 2) *
        (∫⁻ s in Icc (vb u) v, ∫⁻ t in Icc (vb u) v,
          ENNReal.ofReal (v - max s t) * G s * G t)) ≤
      ENNReal.ofReal c⁻¹ * (∫⁻ s in Icc v₀ 0, G s) ^ 2 := by
  classical
  let E := exteriorDomain ui u₀ u₁ vb
  let I := Icc u₀ u₁
  let w := I.indicator vb
  let U := fun t => I ∩ {u | w u ≤ t}
  let K := fun u => E.indicator
    (fun p => ENNReal.ofReal ((-S.nu p.1 p.2) / S.r p.1 p.2 ^ 2)) (u, v)
  have hw (u : ℝ) (hu : u ∈ I) : w u = vb u := indicator_of_mem hu _
  have hwm : Measurable w := by
    convert B.cont.measurable_piecewise (g := fun _ => (0 : ℝ))
      continuousOn_const measurableSet_Icc using 1
    ext u
    by_cases hu : u ∈ Icc u₀ u₁ <;> simp [w, I, Set.piecewise, hu]
  have hUm (t : ℝ) : MeasurableSet (U t) :=
    measurableSet_Icc.inter (measurableSet_le hwm measurable_const)
  have hhistory (t : ℝ) : U t = {u | u ∈ I ∧ vb u ≤ t} := by
    ext u
    constructor
    · rintro ⟨hu, ht⟩
      exact ⟨hu, by change w u ≤ t at ht; rwa [hw u hu] at ht⟩
    · rintro ⟨hu, ht⟩
      exact ⟨hu, by change w u ≤ t; rw [hw u hu]; exact ht⟩
  have hSE : IsSolution e S E := Local.isSolution_mono hS inter_subset_left
  have hr (p : ℝ × ℝ) (hp : p ∈ E) : 0 < S.r p.1 p.2 :=
    hSE.r_pos p hp ((B.off_axis p.1 ⟨hp.2.1, hp.2.2.1⟩).trans_le hp.2.2.2)
  have hKm : Measurable K := (measurable_exterior_indicator B _
    (ENNReal.continuous_ofReal.comp_continuousOn
      (hSE.cont_nu.neg.div (hSE.cont_r.pow 2) (fun p hp => pow_ne_zero _ (hr p hp).ne')))).comp
        (measurable_id.prodMk measurable_const)
  have hKeq (u : ℝ) (hu : u ∈ U v) : K u =
      ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 2) := by
    have hlabel : vb u ≤ v := by
      have hwu : w u ≤ v := hu.2
      rwa [hw u hu.1] at hwu
    exact indicator_of_mem (show (u, v) ∈ E from finite_boundary_row B u hu.1
      ⟨rfl, hlabel, hv.2⟩) _
  let H := fun u (z : ℝ × ℝ) => K u * ENNReal.ofReal (v - max z.1 z.2) * G z.1 * G z.2
  have hHm : Measurable (Function.uncurry H) :=
    (((hKm.comp measurable_fst).mul (ENNReal.continuous_ofReal.measurable.comp
      (measurable_const.sub (measurable_snd.fst.max measurable_snd.snd)))).mul
      (hG.comp measurable_snd.fst)).mul (hG.comp measurable_snd.snd)
  have hbound (u : ℝ) (hu : u ∈ U v) : v₀ ≤ w u ∧ w u ≤ v :=
    ⟨by rw [hw u hu.1]; exact (finite_boundary_label_bounds B u hu.1).1, hu.2⟩
  have hkernel (s t : ℝ) (hs : s ∈ Icc v₀ v) (ht : t ∈ Icc v₀ v) :
      ENNReal.ofReal (v - max s t) * (∫⁻ u in U (min s t), K u) ≤ ENNReal.ofReal c⁻¹ := by
    have hmin : min s t ≤ v := (min_le_left _ _).trans hs.2
    have hmax : max s t ≤ v := max_le hs.2 ht.2
    rcases hmin.eq_or_lt with heq | hlt
    · have hmaxeq : max s t = v := le_antisymm hmax (heq ▸ min_le_max)
      simp only [hmaxeq, sub_self, ENNReal.ofReal_zero, zero_mul]
      exact bot_le
    obtain ⟨z, hz, hzt, hist, hin⟩ := label_history_later B
      ⟨le_min hs.1 ht.1, hmin.trans hv.2⟩ hmin hv.2
    have hsub : U (min s t) ⊆ Icc u₀ z := by rw [hhistory, hist]
    have hlabels (u : ℝ) (hu : u ∈ U (min s t)) :
        u < min s t ∧ outSeg u (min s t) v ⊆ E := by
      have hlabel : vb u ≤ min s t := by
        have hwu : w u ≤ min s t := hu.2
        rwa [hw u hu.1] at hwu
      exact ⟨(B.off_axis u hu.1).trans_le hlabel,
        fun p hp => finite_boundary_row B u hu.1 ⟨hp.1, hlabel.trans hp.2.1, hp.2.2.trans hv.2⟩⟩
    have hk := incoming_optical_separation_kernel hSE hz.1 (hzt.le.trans hmin) hin
      (hUm _) hsub hc hlt hmax hlabels
      (fun u hu x hx => (hstop (u, x) ((hlabels u hu).2 ⟨rfl, hx⟩)).2.2.1)
    have heq : (∫⁻ u in U (min s t), K u) =
        ∫⁻ u in U (min s t), ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 2) := by
      apply setLIntegral_congr_fun (hUm _)
      intro u hu
      exact hKeq u ⟨hu.1, hu.2.trans hmin⟩
    rw [heq]
    exact hk.2.1.trans hk.2.2
  calc
    _ = ∫⁻ u in U v, ∫⁻ s in Icc (w u) v, ∫⁻ t in Icc (w u) v, H u (s, t) := by
      rw [← hhistory v]
      apply setLIntegral_congr_fun (hUm v)
      intro u hu
      change ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 2) *
        (∫⁻ s in Icc (vb u) v, ∫⁻ t in Icc (vb u) v,
          ENNReal.ofReal (v - max s t) * G s * G t) =
        ∫⁻ s in Icc (w u) v, ∫⁻ t in Icc (w u) v, H u (s, t)
      rw [hw u hu.1, ← hKeq u hu]
      let Q := fun (s t : ℝ) => ENNReal.ofReal (v - max s t) * G s * G t
      have hQ : Measurable (Function.uncurry Q) := by
        exact ((ENNReal.continuous_ofReal.measurable.comp
          (measurable_const.sub (measurable_fst.max measurable_snd))).mul
            (hG.comp measurable_fst)).mul (hG.comp measurable_snd)
      have hqi : Measurable (fun s => ∫⁻ t in Icc (vb u) v, Q s t) :=
        hQ.lintegral_prod_right'
      rw [← lintegral_const_mul (K u) hqi]
      apply lintegral_congr
      intro s
      have hqt : Measurable (Q s) :=
        hQ.comp (f := fun t : ℝ => (s, t)) (measurable_const.prodMk measurable_id)
      rw [← lintegral_const_mul (K u) hqt]
      apply lintegral_congr
      intro t
      dsimp only [Q, H]
      ring
    _ = ∫⁻ s in Icc v₀ v, ∫⁻ t in Icc v₀ v,
        ∫⁻ u in U v ∩ {u | w u ≤ min s t}, H u (s, t) :=
      lintegral_history_square (hUm v) hwm hbound H hHm
    _ ≤ ∫⁻ s in Icc v₀ v, ∫⁻ t in Icc v₀ v, ENNReal.ofReal c⁻¹ * (G s * G t) := by
      apply setLIntegral_mono' measurableSet_Icc
      intro s hs
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      have hset : U v ∩ {u | w u ≤ min s t} = U (min s t) := by
        ext u
        simp only [U, mem_inter_iff, mem_ofPred_eq]
        exact ⟨fun h => ⟨h.1.1, h.2⟩,
          fun h => ⟨⟨h.1, h.2.trans ((min_le_left _ _).trans hs.2)⟩, h.2⟩⟩
      rw [hset]
      have heq : (∫⁻ u in U (min s t), H u (s, t)) =
          (ENNReal.ofReal (v - max s t) * ∫⁻ u in U (min s t), K u) * (G s * G t) := by
        calc
          _ = ∫⁻ u in U (min s t), K u *
              (ENNReal.ofReal (v - max s t) * (G s * G t)) := by
            apply lintegral_congr
            intro u
            dsimp only [H]
            ring
          _ = _ := by rw [lintegral_mul_const _ hKm]; ring
      rw [heq]
      exact mul_le_mul (hkernel s t hs ht) le_rfl bot_le bot_le
    _ = ENNReal.ofReal c⁻¹ * (∫⁻ s in Icc v₀ v, G s) ^ 2 := by
      have heq (s : ℝ) : (∫⁻ t in Icc v₀ v, ENNReal.ofReal c⁻¹ * (G s * G t)) =
          (ENNReal.ofReal c⁻¹ * G s) * (∫⁻ t in Icc v₀ v, G t) := by
        simp only [← mul_assoc]
        exact lintegral_const_mul _ hG
      simp_rw [heq]
      have hCG : Measurable (fun s => ENNReal.ofReal c⁻¹ * G s) := measurable_const.mul hG
      rw [lintegral_mul_const _ hCG, lintegral_const_mul _ hG, pow_two]
      ring
    _ ≤ _ := by
      gcongr
      exact hv.2

end EmcsfAcExtension.Global.InteractionEstimate
