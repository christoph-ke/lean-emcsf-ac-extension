module

public import EmcsfAcExtension.Local.Stability.DifferenceMomentsKernel
public import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Separated moments on actual outgoing field sections

Measurable extensions are used only inside the proof. The exported
estimate uses the original fields at common labels, with no global
measurability or extension hypothesis on `Fields`.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The outgoing `1/2` and `3/4` kernels convolve with the exact
universal coefficient `4`. No constant depends on the pair, parameters,
domain, derivative suprema or minimum radius. -/
theorem stab_out_separated_moment_convolution
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    (∫⁻ t in Icc u v,
      ENNReal.ofReal ((S₁.r u t / S₁.r u v) ^ (1 / 2 : ℝ) * (S₁.lam u t / S₁.r u t)) *
        ∫⁻ s in Icc u t, ENNReal.ofReal ((S₁.r u s / S₁.r u t) ^ (3 / 4 : ℝ)) *
          outEnv 0 (jC1 (triangle 0 T) S₂) s) ≤
      ENNReal.ofReal 4 * ∫⁻ s in Icc u v,
        ENNReal.ofReal ((S₁.r u s / S₁.r u v) ^ (1 / 2 : ℝ)) *
          outEnv 0 (jC1 (triangle 0 T) S₂) s := by
  classical
  let R := (Icc u v).indicator (S₁.r u)
  let W := (Icc u v).indicator (S₁.lam u)
  let J := (Icc 0 T).indicator (outEnv 0 (jC1 (triangle 0 T) S₂))
  have hmap : MapsTo (fun s : ℝ => (u, s)) (Icc u v) (triangle 0 T) :=
    fun s hs => ⟨hu, hs.1, hs.2.trans hvT⟩
  have cR : ContinuousOn (S₁.r u) (Icc u v) := h₁s.c1.c1_r.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cW : ContinuousOn (S₁.lam u) (Icc u v) := h₁s.c1.c1_lam.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have hRval : ∀ s ∈ Icc u v, R s = S₁.r u s := fun s hs => indicator_of_mem hs _
  have hWval : ∀ s ∈ Icc u v, W s = S₁.lam u s := fun s hs => indicator_of_mem hs _
  have hJval : ∀ s ∈ Icc u v, J s = outEnv 0 (jC1 (triangle 0 T) S₂) s :=
    fun s hs => indicator_of_mem (show s ∈ Icc 0 T from
      ⟨hu.trans hs.1, hs.2.trans hvT⟩) _
  have hRm : Measurable R := by
    change Measurable ((Icc u v).indicator (S₁.r u))
    rw [← Set.piecewise_eq_indicator]
    exact cR.measurable_piecewise (continuousOn_const (c := (0 : ℝ))) measurableSet_Icc
  have hWm : Measurable W := by
    change Measurable ((Icc u v).indicator (S₁.lam u))
    rw [← Set.piecewise_eq_indicator]
    exact cW.measurable_piecewise (continuousOn_const (c := (0 : ℝ))) measurableSet_Icc
  have hJm : Measurable J := measurable_indicator_outEnv
    (continuousOn_jC1_aux h₂s.pos h₂s.c1)
  have hR0 : ∀ t ∈ Icc u v, 0 ≤ R t := by
    intro t ht
    rw [hRval t ht]
    have hb := (stab_radius_bounds h₁s hu ht.1 (ht.2.trans hvT)).1
    linarith only [hb, ht.1]
  have hRp : ∀ t ∈ Ioc u v, 0 < R t := by
    intro t ht
    rw [hRval t ⟨ht.1.le, ht.2⟩]
    exact h₁s.c1.r_pos (u, t) ⟨hu, ht.1.le, ht.2.trans hvT⟩ ht.1
  have hW0 : ∀ t ∈ Icc u v, 0 ≤ W t := by
    intro t ht
    rw [hWval t ht]
    exact (h₁s.c1.lam_pos (u, t) (hmap ht)).le
  have hdR : ∀ t ∈ Ioo u v, HasDerivAt R (W t) t := by
    intro t ht
    have hp : (u, t) ∈ triangle 0 T := ⟨hu, ht.1.le, ht.2.le.trans hvT⟩
    have hd := hasDerivWithinAt_v_aux h₁s.c1.c1_r hu ht.1.le (ht.2.le.trans hvT)
    rw [(h₁s.c1.eq_v (u, t) hp ht.1).1] at hd
    rw [hWval t ⟨ht.1.le, ht.2.le⟩]
    apply (hd.hasDerivAt (Icc_mem_nhds ht.1 (ht.2.trans_le hvT))).congr_of_eventuallyEq
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    exact hRval s hs
  have hi := stab_separated_radial_convolution_le
    (p := (1 / 2 : ℝ)) (q := (3 / 4 : ℝ)) (by norm_num) hRm hWm hJm
    (cR.congr hRval) (cW.congr hWval) hR0 hRp hW0 hdR
  have hleft : (∫⁻ t in Icc u v, ENNReal.ofReal ((R t / R v) ^ (1 / 2 : ℝ) * (W t / R t)) *
      ∫⁻ s in Icc u t, ENNReal.ofReal ((R s / R t) ^ (3 / 4 : ℝ)) * J s) =
      ∫⁻ t in Icc u v,
        ENNReal.ofReal ((S₁.r u t / S₁.r u v) ^ (1 / 2 : ℝ) * (S₁.lam u t / S₁.r u t)) *
          ∫⁻ s in Icc u t, ENNReal.ofReal ((S₁.r u s / S₁.r u t) ^ (3 / 4 : ℝ)) *
            outEnv 0 (jC1 (triangle 0 T) S₂) s := by
    apply setLIntegral_congr_fun measurableSet_Icc
    intro t ht
    dsimp only
    rw [hRval t ht, hRval v ⟨huv.le, le_rfl⟩, hWval t ht]
    congr 1
    apply setLIntegral_congr_fun measurableSet_Icc
    intro s hs
    dsimp only
    rw [hRval s ⟨hs.1, hs.2.trans ht.2⟩, hJval s ⟨hs.1, hs.2.trans ht.2⟩]
  have hright : (∫⁻ s in Icc u v, ENNReal.ofReal ((R s / R v) ^ (1 / 2 : ℝ)) * J s) =
      ∫⁻ s in Icc u v, ENNReal.ofReal ((S₁.r u s / S₁.r u v) ^ (1 / 2 : ℝ)) *
        outEnv 0 (jC1 (triangle 0 T) S₂) s := by
    apply setLIntegral_congr_fun measurableSet_Icc
    intro s hs
    dsimp only
    rw [hRval s hs, hRval v ⟨huv.le, le_rfl⟩, hJval s hs]
  rw [hleft, hright] at hi
  norm_num at hi
  simpa only [ENNReal.ofReal_ofNat] using hi

end EmcsfAcExtension.Local
