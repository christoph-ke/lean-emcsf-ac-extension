module

public import EmcsfAcExtension.Local.Stability.DifferenceMomentsKernel
public import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux
public import EmcsfAcExtension.Local.Stability.MomentsReflection
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Separated incoming moments at common labels

Reflection uses the increasing parameter `t = -u`, with positive
radius derivative `-ν`. Both nested integration intervals are reversed
explicitly before returning to the original null labels.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The incoming `1/2`, `3/4` convolution has the exact universal cost
`4`, independently of all parameters, the pair and the minimum radius. -/
theorem stab_in_separated_moment_convolution
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    (∫⁻ t in Icc u v,
      ENNReal.ofReal ((S₁.r t v / S₁.r u v) ^ (1 / 2 : ℝ) * (-S₁.nu t v / S₁.r t v)) *
        ∫⁻ s in Icc t v, ENNReal.ofReal ((S₁.r s v / S₁.r t v) ^ (3 / 4 : ℝ)) *
          inEnv T (kC1 e (triangle 0 T) S₂) s) ≤
      ENNReal.ofReal 4 * ∫⁻ s in Icc u v,
        ENNReal.ofReal ((S₁.r s v / S₁.r u v) ^ (1 / 2 : ℝ)) *
          inEnv T (kC1 e (triangle 0 T) S₂) s := by
  classical
  let R := (Icc (-v) (-u)).indicator (fun t => S₁.r (-t) v)
  let W := (Icc (-v) (-u)).indicator (fun t => -S₁.nu (-t) v)
  let J := fun t => (Icc 0 T).indicator (inEnv T (kC1 e (triangle 0 T) S₂)) (-t)
  have hmap : MapsTo (fun t : ℝ => (-t, v)) (Icc (-v) (-u)) (triangle 0 T) := by
    intro t ht
    exact ⟨by linarith only [hu, ht.2], by linarith only [ht.1], hvT⟩
  have cR : ContinuousOn (fun t => S₁.r (-t) v) (Icc (-v) (-u)) :=
    h₁s.c1.c1_r.continuousOn.comp (continuous_neg.prodMk continuous_const).continuousOn hmap
  have cW : ContinuousOn (fun t => -S₁.nu (-t) v) (Icc (-v) (-u)) :=
    (h₁s.c1.c1_nu.continuousOn.comp
      (continuous_neg.prodMk continuous_const).continuousOn hmap).neg
  have hRval : ∀ t ∈ Icc (-v) (-u), R t = S₁.r (-t) v :=
    fun t ht => indicator_of_mem ht _
  have hWval : ∀ t ∈ Icc (-v) (-u), W t = -S₁.nu (-t) v :=
    fun t ht => indicator_of_mem ht _
  have hJval : ∀ t ∈ Icc (-v) (-u), J t = inEnv T (kC1 e (triangle 0 T) S₂) (-t) :=
    fun t ht => indicator_of_mem (show -t ∈ Icc 0 T from
      ⟨(hmap ht).1, (hmap ht).2.1.trans hvT⟩) _
  have hRm : Measurable R := by
    change Measurable ((Icc (-v) (-u)).indicator (fun t => S₁.r (-t) v))
    rw [← Set.piecewise_eq_indicator]
    exact cR.measurable_piecewise (continuousOn_const (c := (0 : ℝ))) measurableSet_Icc
  have hWm : Measurable W := by
    change Measurable ((Icc (-v) (-u)).indicator (fun t => -S₁.nu (-t) v))
    rw [← Set.piecewise_eq_indicator]
    exact cW.measurable_piecewise (continuousOn_const (c := (0 : ℝ))) measurableSet_Icc
  have hJm : Measurable J := (measurable_indicator_inEnv
    (continuousOn_kC1_aux h₂s.pos h₂s.c1)).comp measurable_neg
  have hR0 : ∀ t ∈ Icc (-v) (-u), 0 ≤ R t := by
    intro t ht
    rw [hRval t ht]
    have hb := (stab_radius_bounds h₁s (hmap ht).1 (hmap ht).2.1 hvT).1
    linarith only [hb, ht.1]
  have hRp : ∀ t ∈ Ioc (-v) (-u), 0 < R t := by
    intro t ht
    rw [hRval t ⟨ht.1.le, ht.2⟩]
    exact h₁s.c1.r_pos (-t, v) (hmap ⟨ht.1.le, ht.2⟩) (by linarith only [ht.1])
  have hW0 : ∀ t ∈ Icc (-v) (-u), 0 ≤ W t := by
    intro t ht
    rw [hWval t ht]
    exact (neg_pos.mpr (h₁s.c1.nu_neg (-t, v) (hmap ht))).le
  have hdR : ∀ t ∈ Ioo (-v) (-u), HasDerivAt R (W t) t := by
    intro t ht
    have hut : 0 < -t := by linarith only [hu, ht.2]
    have htv : -t < v := by linarith only [ht.1]
    have hp := hmap ⟨ht.1.le, ht.2.le⟩
    have hd := hasDerivWithinAt_u_aux h₁s.c1.c1_r hut.le htv.le hvT
    rw [(h₁s.c1.eq_u (-t, v) hp htv).1] at hd
    have hdA := hd.hasDerivAt (Icc_mem_nhds hut htv)
    have hd' := (by simpa only [zero_sub] using! hdA :
      HasDerivAt (fun s => S₁.r s v) _ (0 - t)).comp_const_sub 0 t
    have hdR : HasDerivAt (fun s => S₁.r (-s) v) (-S₁.nu (-t) v) t := by
      simpa only [zero_sub, add_zero] using! hd'
    rw [hWval t ⟨ht.1.le, ht.2.le⟩]
    apply hdR.congr_of_eventuallyEq
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    exact hRval s hs
  have hi := stab_separated_radial_convolution_le
    (p := (1 / 2 : ℝ)) (q := (3 / 4 : ℝ)) (by norm_num) hRm hWm hJm
    (cR.congr hRval) (cW.congr hWval) hR0 hRp hW0 hdR
  have hleft : (∫⁻ t in Icc (-v) (-u),
      ENNReal.ofReal ((R t / R (-u)) ^ (1 / 2 : ℝ) * (W t / R t)) *
        ∫⁻ s in Icc (-v) t, ENNReal.ofReal ((R s / R t) ^ (3 / 4 : ℝ)) * J s) =
      ∫⁻ t in Icc u v,
        ENNReal.ofReal ((S₁.r t v / S₁.r u v) ^ (1 / 2 : ℝ) * (-S₁.nu t v / S₁.r t v)) *
          ∫⁻ s in Icc t v, ENNReal.ofReal ((S₁.r s v / S₁.r t v) ^ (3 / 4 : ℝ)) *
            inEnv T (kC1 e (triangle 0 T) S₂) s := by
    rw [← stab_lintegral_neg_Icc (a := u) (b := v)]
    apply setLIntegral_congr_fun measurableSet_Icc
    intro t ht
    dsimp only
    rw [hRval t ht, hRval (-u) ⟨neg_le_neg huv.le, le_rfl⟩, hWval t ht, neg_neg]
    congr 1
    rw [← stab_lintegral_neg_Icc (a := -t) (b := v), neg_neg]
    apply setLIntegral_congr_fun measurableSet_Icc
    intro s hs
    dsimp only
    rw [hRval s ⟨hs.1, hs.2.trans ht.2⟩, hJval s ⟨hs.1, hs.2.trans ht.2⟩]
  have hright : (∫⁻ s in Icc (-v) (-u),
      ENNReal.ofReal ((R s / R (-u)) ^ (1 / 2 : ℝ)) * J s) =
      ∫⁻ s in Icc u v, ENNReal.ofReal ((S₁.r s v / S₁.r u v) ^ (1 / 2 : ℝ)) *
        inEnv T (kC1 e (triangle 0 T) S₂) s := by
    rw [← stab_lintegral_neg_Icc (a := u) (b := v)]
    apply setLIntegral_congr_fun measurableSet_Icc
    intro s hs
    dsimp only
    rw [hRval s hs, hRval (-u) ⟨neg_le_neg huv.le, le_rfl⟩, hJval s hs, neg_neg]
  rw [hleft, hright] at hi
  norm_num at hi
  simpa only [ENNReal.ofReal_ofNat] using hi

end EmcsfAcExtension.Local
