module

public import EmcsfAcExtension.Global.Interaction.BoundaryKernels
public import EmcsfAcExtension.Global.Interaction.HistoryPairs
import EmcsfAcExtension.Local.Api.Mono
import Mathlib.Tactic

/-! # Outgoing-first boundary source reduction

The power weight is retained through the outgoing radius integration.
Consumers discharge the remaining incoming label moment with the actual
field budgets and radius kernels.
Source: charged_SF_new_version.tex:L3673–L3697; internal project record `(sb)`, `(ib)`.
-/

public section
open Set MeasureTheory
open scoped ENNReal
namespace EmcsfAcExtension.Global.InteractionEstimate

/-- [internal]
The weighted row-history kernel is controlled by its actual incoming
label moment. Its exact outgoing coefficient is `1/(c(2+α-ε))`, uniform
in the fields, radii, stage count, label density, and all durations.
The production consumer proves the displayed label-moment bound.
Source: internal project record `(outer)`, `(sb)`, `(ib)`. -/
theorem radial_history_kernel_of_label_bound {e ui u₀ u₁ v₀ ρ δ c Λ F ε α L : ℝ}
    {S : Fields} {vb : ℝ → ℝ} {N : ℕ}
    (hS : IsSolution e S (origDomain ui))
    (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N)
    (hstop : ExteriorStops S (exteriorDomain ui u₀ u₁ vb) δ c Λ F ε)
    (hc : 0 < c) (hq : 0 < 2 + α - ε) (n : Fin N)
    (P : ℝ × ℝ → ℝ) (hP : ContinuousOn P (exteriorDomain ui u₀ u₁ vb))
    (hP0 : ∀ p ∈ exteriorDomain ui u₀ u₁ vb, 0 ≤ P p)
    (G : ℝ → ℝ≥0∞) (hG : Measurable G)
    (hlabel : ∀ s ∈ Icc v₀ 0,
      (∫⁻ u in Icc (B.cuts n.castSucc) (B.cuts n.succ) ∩ {u | vb u ≤ s},
        ENNReal.ofReal (P (u, s) * (-S.nu u s) / S.r u s ^ 2)) ≤ ENNReal.ofReal L) :
    (∫⁻ u in Icc (B.cuts n.castSucc) (B.cuts n.succ), ∫⁻ v in Icc (vb u) 0,
      ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 3) *
        (∫⁻ s in Icc (vb u) v,
          ENNReal.ofReal ((S.r u s / S.r u v) ^ α * P (u, s)) * G s)) ≤
      ENNReal.ofReal (L / (c * (2 + α - ε))) * (∫⁻ s in Icc v₀ 0, G s) := by
  classical
  let D := exteriorDomain ui u₀ u₁ vb
  let I := Icc u₀ u₁
  let U := Icc (B.cuts n.castSucc) (B.cuts n.succ)
  let w := I.indicator vb
  let K := fun u v => D.indicator (fun p => ENNReal.ofReal
    (((-S.nu p.1 p.2) / S.r p.1 p.2 ^ 3) / S.r p.1 p.2 ^ α)) (u, v)
  let A := fun u s => D.indicator
    (fun p => ENNReal.ofReal (S.r p.1 p.2 ^ α * P p)) (u, s)
  have hSE : IsSolution e S D := Local.isSolution_mono hS inter_subset_left
  have hr (p : ℝ × ℝ) (hp : p ∈ D) : 0 < S.r p.1 p.2 :=
    hSE.r_pos p hp ((B.off_axis p.1 ⟨hp.2.1, hp.2.2.1⟩).trans_le hp.2.2.2)
  have crp := hSE.cont_r.rpow_const (p := α) (fun p hp => Or.inl (hr p hp).ne')
  have hKm : Measurable (Function.uncurry K) := measurable_exterior_indicator B _
    (ENNReal.continuous_ofReal.comp_continuousOn
      ((hSE.cont_nu.neg.div (hSE.cont_r.pow 3) (fun p hp => pow_ne_zero _ (hr p hp).ne')).div
        crp (fun p hp => (Real.rpow_pos_of_pos (hr p hp) _).ne')))
  have hAm : Measurable (Function.uncurry A) := measurable_exterior_indicator B _
    (ENNReal.continuous_ofReal.comp_continuousOn (crp.mul hP))
  have hw (u : ℝ) (hu : u ∈ U) : w u = vb u :=
    indicator_of_mem (finite_boundary_stage_subset B n hu) _
  have hwm : Measurable w := by
    convert B.cont.measurable_piecewise (g := fun _ => (0 : ℝ))
      continuousOn_const measurableSet_Icc using 1
    ext u
    by_cases hu : u ∈ Icc u₀ u₁ <;> simp [w, I, Set.piecewise, hu]
  have hbnd (u : ℝ) (hu : u ∈ U) : v₀ ≤ w u ∧ w u ≤ 0 := by
    rw [hw u hu]
    exact finite_boundary_label_bounds B u (finite_boundary_stage_subset B n hu)
  have hmem (u : ℝ) (hu : u ∈ U) (v : ℝ) (hv : v ∈ Icc (vb u) 0) : (u, v) ∈ D :=
    finite_boundary_row B u (finite_boundary_stage_subset B n hu) ⟨rfl, hv⟩
  have hKeq (u : ℝ) (hu : u ∈ U) (v : ℝ) (hv : v ∈ Icc (vb u) 0) :
      K u v = ENNReal.ofReal (((-S.nu u v) / S.r u v ^ 3) / S.r u v ^ α) :=
    indicator_of_mem (hmem u hu v hv) _
  have hAeq (u : ℝ) (hu : u ∈ U) (v : ℝ) (hv : v ∈ Icc (vb u) 0) :
      A u v = ENNReal.ofReal (S.r u v ^ α * P (u, v)) :=
    indicator_of_mem (hmem u hu v hv) _
  have htail (s : ℝ) (hs : s ∈ Icc v₀ 0) :
      (∫⁻ u in U ∩ {u | w u ≤ s}, A u s * (∫⁻ v in Icc s 0, K u v)) ≤
        ENNReal.ofReal (L / (c * (2 + α - ε))) := by
    have hset : U ∩ {u | w u ≤ s} = U ∩ {u | vb u ≤ s} := by
      ext u
      constructor
      · rintro ⟨hu, hwus⟩
        change w u ≤ s at hwus
        exact ⟨hu, by rwa [hw u hu] at hwus⟩
      · rintro ⟨hu, hvus⟩
        exact ⟨hu, by change w u ≤ s; rw [hw u hu]; exact hvus⟩
    have hUs : MeasurableSet (U ∩ {u | vb u ≤ s}) := hset ▸
      (measurableSet_Icc.inter (measurableSet_le hwm measurable_const))
    rw [hset]
    have hpoint (u : ℝ) (hu : u ∈ U ∩ {u | vb u ≤ s}) :
        A u s * (∫⁻ v in Icc s 0, K u v) ≤
          ENNReal.ofReal ((c * (2 + α - ε))⁻¹) *
            ENNReal.ofReal (P (u, s) * (-S.nu u s) / S.r u s ^ 2) := by
      have hui := finite_boundary_stage_subset B n hu.1
      have hrow : outSeg u s 0 ⊆ D := fun p hp =>
        finite_boundary_row B u hui ⟨hp.1, hu.2.trans hp.2.1, hp.2.2⟩
      have hrv := hr (u, s) (hrow ⟨rfl, le_rfl, hs.2⟩)
      have hα := Real.rpow_pos_of_pos hrv α
      have hPu := hP0 (u, s) (hrow ⟨rfl, le_rfl, hs.2⟩)
      have hout := outgoing_inverse_cube_power_kernel hSE ((B.off_axis u hui).trans_le hu.2)
        hs.2 hrow hc hq (fun v hv => (hstop (u, v) (hrow ⟨rfl, hv⟩)).2.2.1)
        (fun v hv => (hstop (u, v) (hrow ⟨rfl, hv⟩)).2.2.2.2.2.1)
      have heq : A u s * (∫⁻ v in Icc s 0, K u v) = ENNReal.ofReal (P (u, s)) *
          (∫⁻ v in Icc s 0, ENNReal.ofReal
            (((-S.nu u v) / S.r u v ^ 3) * (S.r u s / S.r u v) ^ α)) := by
        rw [hAeq u hu.1 s ⟨hu.2, hs.2⟩]
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        apply setLIntegral_congr_fun measurableSet_Icc
        intro v hv
        change ENNReal.ofReal (S.r u s ^ α * P (u, s)) * K u v =
          ENNReal.ofReal (P (u, s)) * ENNReal.ofReal
            (((-S.nu u v) / S.r u v ^ 3) * (S.r u s / S.r u v) ^ α)
        rw [hKeq u hu.1 v ⟨hu.2.trans hv.1, hv.2⟩,
          ← ENNReal.ofReal_mul (mul_nonneg hα.le hPu), ← ENNReal.ofReal_mul hPu]
        congr 1
        rw [Real.div_rpow hrv.le (hr (u, v) (hrow ⟨rfl, hv⟩)).le]
        ring
      rw [heq]
      apply (mul_le_mul le_rfl hout bot_le bot_le).trans_eq
      rw [← ENNReal.ofReal_mul hPu, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    calc
      _ ≤ ∫⁻ u in U ∩ {u | vb u ≤ s}, ENNReal.ofReal ((c * (2 + α - ε))⁻¹) *
          ENNReal.ofReal (P (u, s) * (-S.nu u s) / S.r u s ^ 2) :=
        setLIntegral_mono' hUs hpoint
      _ = ENNReal.ofReal ((c * (2 + α - ε))⁻¹) *
          (∫⁻ u in U ∩ {u | vb u ≤ s}, ENNReal.ofReal (P (u, s) * (-S.nu u s) / S.r u s ^ 2)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ((c * (2 + α - ε))⁻¹) * ENNReal.ofReal L := by
        gcongr
        exact hlabel s hs
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  calc
    _ = ∫⁻ u in U, ∫⁻ v in Icc (w u) 0, K u v * (∫⁻ s in Icc (w u) v, A u s * G s) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro u hu
      change (∫⁻ v in Icc (vb u) 0, _) = ∫⁻ v in Icc (w u) 0, _
      rw [hw u hu]
      apply setLIntegral_congr_fun measurableSet_Icc
      intro v hv
      change ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 3) * _ = K u v * _
      rw [hKeq u hu v hv, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply setLIntegral_congr_fun measurableSet_Icc
      intro s hs
      change ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 3) *
        (ENNReal.ofReal ((S.r u s / S.r u v) ^ α * P (u, s)) * G s) =
        ENNReal.ofReal (((-S.nu u v) / S.r u v ^ 3) / S.r u v ^ α) * (A u s * G s)
      rw [hAeq u hu s ⟨hs.1, hs.2.trans hv.2⟩]
      have hnu : 0 ≤ -S.nu u v := (neg_pos.mpr (hSE.nu_neg (u, v) (hmem u hu v hv))).le
      have hrv := hr (u, v) (hmem u hu v hv)
      have hrs := hr (u, s) (hmem u hu s ⟨hs.1, hs.2.trans hv.2⟩)
      rw [← mul_assoc, ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      rw [Real.div_rpow hrs.le hrv.le]
      ring
    _ ≤ ENNReal.ofReal (1 * (L / (c * (2 + α - ε)))) * (∫⁻ s in Icc v₀ 0, G s) := by
      apply lintegral_source_of_history_bound measurableSet_Icc hwm hbnd _ K A hKm hAm G hG
        (by norm_num : (0 : ℝ) ≤ 1) _ htail
      intro u _ v _
      simp only [ENNReal.ofReal_one, one_mul]
      exact le_rfl
    _ = _ := by rw [one_mul]

end EmcsfAcExtension.Global.InteractionEstimate
