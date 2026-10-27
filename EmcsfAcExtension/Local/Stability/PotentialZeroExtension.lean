module

public import EmcsfAcExtension.Local.Defs.Setting

/-! # Incoming primitives of a zero-axis triangle density

Extending by zero past the moving diagonal truncates the incoming
primitive at the minimum of the two labels. The zero diagonal trace
removes the otherwise moving boundary term exactly.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

/-- A continuous triangle density vanishing on the axis and with a
continuous incoming derivative has an exact rectangle primitive after
zero extension. The identity has coefficient one and no quantitative
regularity, integrability or estimate-constant hypothesis. -/
theorem stab_triangle_zero_extension_incoming_primitive
    {T : ℝ} {G H : ℝ → ℝ → ℝ}
    (cG : ContinuousOn (Function.uncurry G) (triangle 0 T))
    (cH : ContinuousOn (Function.uncurry H) (triangle 0 T))
    (haxis : ∀ t ∈ Icc 0 T, G t t = 0)
    (hd : ∀ u v, 0 ≤ u → u < v → v ≤ T →
      HasDerivWithinAt (fun s => G s v) (H u v) (Icc 0 v) u)
    {u w : ℝ} (hu : u ∈ Icc 0 T) (hw : w ∈ Icc 0 T) :
    (triangle 0 T).indicator (Function.uncurry G) (u, w) =
      (triangle 0 T).indicator (Function.uncurry G) (0, w) +
        ∫ s in 0..u, (triangle 0 T).indicator (Function.uncurry H) (s, w) := by
  let r := min u w
  have hr0 : 0 ≤ r := le_min hu.1 hw.1
  have hrw : r ≤ w := min_le_right _ _
  have hm : MapsTo (fun s : ℝ => (s, w)) (Icc 0 r) (triangle 0 T) :=
    fun s hs => ⟨hs.1, hs.2.trans hrw, hw.2⟩
  have cp : ContinuousOn (fun s : ℝ => (s, w)) (Icc 0 r) :=
    (continuous_id.prodMk continuous_const).continuousOn
  have hFTC : (∫ s in 0..r, H s w) = G r w - G 0 w := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr0 (cG.comp cp hm)
      (fun s hs => (hd s w hs.1.le (hs.2.trans_le hrw) hw.2).hasDerivAt
        (Icc_mem_nhds hs.1 (hs.2.trans_le hrw)))
      (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hr0 (cH.comp cp hm))
  have hInt : (∫ s in 0..u, (triangle 0 T).indicator (Function.uncurry H) (s, w)) =
      ∫ s in 0..r, H s w := by
    rw [intervalIntegral.integral_of_le hu.1, intervalIntegral.integral_of_le hr0]
    calc
      _ = ∫ s in Ioc 0 u, (Iic w).indicator (fun s => H s w) s := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        by_cases hsw : s ≤ w
        · rw [indicator_of_mem (show (s, w) ∈ triangle 0 T from ⟨hs.1.le, hsw, hw.2⟩),
            indicator_of_mem (show s ∈ Iic w from hsw)]
          rfl
        · rw [indicator_of_notMem (show (s, w) ∉ triangle 0 T from fun hp => hsw hp.2.1),
            indicator_of_notMem (show s ∉ Iic w from hsw)]
      _ = ∫ s in Iic w ∩ Ioc 0 u, H s w := by
        rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
      _ = ∫ s in Ioc 0 r, H s w := by
        have hset : Iic w ∩ Ioc 0 u = Ioc 0 r := by
          ext s
          simp only [r, mem_inter_iff, mem_Iic, mem_Ioc, le_min_iff]
          tauto
        rw [hset]
  have hGR : (triangle 0 T).indicator (Function.uncurry G) (u, w) = G r w := by
    rcases le_total u w with huw | hwu
    · rw [indicator_of_mem (show (u, w) ∈ triangle 0 T from ⟨hu.1, huw, hw.2⟩)]
      simp only [r, min_eq_left huw, Function.uncurry_def]
    · have heq : G r w = 0 := by simpa only [r, min_eq_right hwu] using haxis w hw
      rw [heq]
      by_cases huw : u ≤ w
      · have he : u = w := le_antisymm huw hwu
        subst u
        rw [indicator_of_mem (show (w, w) ∈ triangle 0 T from ⟨hw.1, le_rfl, hw.2⟩)]
        exact haxis w hw
      · exact indicator_of_notMem (fun hp => huw hp.2.1) _
  rw [hGR, indicator_of_mem (show (0, w) ∈ triangle 0 T from ⟨le_rfl, hw.1, hw.2⟩),
    hInt, hFTC]
  simp only [Function.uncurry_def]
  ring

/-- Integrating the zero extension of a triangle density over a fixed
outgoing label interval gives its moving-axis primitive exactly.
No measurability or finiteness premise, and no estimate constant, is
needed for this equality of Bochner integrals. -/
theorem stab_triangle_zero_extension_outgoing_integral
    {T : ℝ} (K : ℝ → ℝ → ℝ) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    (∫ w in Icc 0 v, (triangle 0 T).indicator (Function.uncurry K) (u, w)) =
      ∫ w in u..v, K u w := by
  have heq : (∫ w in Icc 0 v, (triangle 0 T).indicator (Function.uncurry K) (u, w)) =
      ∫ w in Icc 0 v, (Ici u).indicator (K u) w := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with w hw
    by_cases huw : u ≤ w
    · rw [indicator_of_mem (show (u, w) ∈ triangle 0 T from ⟨hu, huw, hw.2.trans hvT⟩),
        indicator_of_mem (show w ∈ Ici u from huw)]
      rfl
    · rw [indicator_of_notMem (show (u, w) ∉ triangle 0 T from fun hp => huw hp.2.1),
        indicator_of_notMem (show w ∉ Ici u from huw)]
  rw [heq, integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
    intervalIntegral.integral_of_le huv, restrict_Ioc_eq_restrict_Icc]
  have hset : Ici u ∩ Icc 0 v = Icc u v := by
    ext w
    simp only [mem_inter_iff, mem_Ici, mem_Icc]
    constructor
    · rintro ⟨huw, _, hwv⟩
      exact ⟨huw, hwv⟩
    · intro hw
      exact ⟨hw.1, hu.trans hw.1, hw.2⟩
  rw [hset]

end EmcsfAcExtension.Local
