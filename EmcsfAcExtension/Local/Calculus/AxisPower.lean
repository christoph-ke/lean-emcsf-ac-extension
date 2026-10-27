module

public import EmcsfAcExtension.Local.Calculus.AxisFactor
import EmcsfAcExtension.Infra.Calculus.PartialsC1

/-! # Higher-order continuous section factors at the axis

A prescribed derivative with a continuous power of `v-u` integrates to the next
power. This is a statement about C¹ fields and their section primitives, with no
higher differentiability requirement.
-/

public section

open Set MeasureTheory Filter
open scoped Topology

namespace EmcsfAcExtension.Local

private theorem continuousOn_power_integral_aux {F : (ℝ × ℝ) → ℝ → ℝ} {T : ℝ}
    (hF : ContinuousOn (Function.uncurry F) (triangle 0 T ×ˢ Icc (0 : ℝ) 1)) :
    ContinuousOn (fun p => ∫ t in (0 : ℝ)..1, F p t) (triangle 0 T) := by
  obtain ⟨C, hC⟩ := ((isCompact_triangle 0 T).prod isCompact_Icc).exists_bound_of_continuousOn hF
  have hsec (p : ℝ × ℝ) (hp : p ∈ triangle 0 T) :
      ContinuousOn (F p) (Icc (0 : ℝ) 1) :=
    hF.comp (continuousOn_const.prodMk continuousOn_id) (fun _ ht => ⟨hp, ht⟩)
  intro p hp
  apply intervalIntegral.continuousWithinAt_of_dominated_interval (bound := fun _ => C)
  · filter_upwards [self_mem_nhdsWithin] with q hq
    exact ((hsec q hq).aestronglyMeasurable measurableSet_Icc).mono_set
      (by simp only [uIoc_of_le zero_le_one]; exact Ioc_subset_Icc_self)
  · filter_upwards [self_mem_nhdsWithin] with q hq
    exact Filter.Eventually.of_forall (fun t ht => hC (q, t)
      ⟨hq, by simpa only [uIcc_of_le zero_le_one] using (uIoc_subset_uIcc ht)⟩)
  · exact intervalIntegrable_const
  · apply Filter.Eventually.of_forall
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le zero_le_one] using (uIoc_subset_uIcc ht)
    exact (hF.comp (continuousOn_id.prodMk continuousOn_const)
      (fun _ hq => ⟨hq, ht'⟩)) p hp

/-- Integrating a continuous factor of `(v-u)^n` in the outgoing derivative gives
a continuous factor of `(v-u)^(n+1)` in the field. The field vanishes at the axis;
there is no bound or constant, and the conclusion includes the terminal vertex. -/
theorem exists_continuous_axis_power_factor_of_deriv_aux {T : ℝ} {f G : ℝ → ℝ → ℝ}
    (n : ℕ) (hf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle 0 T))
    (hG : ContinuousOn (Function.uncurry G) (triangle 0 T))
    (haxis : ∀ t ∈ Icc 0 T, f t t = 0)
    (heq : ∀ u v, (u, v) ∈ triangle 0 T → pdV (triangle 0 T) f u v = (v - u) ^ n * G u v) :
    ∃ g : (ℝ × ℝ) → ℝ, ContinuousOn g (triangle 0 T) ∧
      ∀ u v, (u, v) ∈ triangle 0 T → f u v = (v - u) ^ (n + 1) * g (u, v) := by
  let F (p : ℝ × ℝ) (t : ℝ) := t ^ n * G p.1 (p.1 + (p.2 - p.1) * t)
  have hmap : ∀ q ∈ triangle 0 T ×ˢ Icc (0 : ℝ) 1,
      (q.1.1, q.1.1 + (q.1.2 - q.1.1) * q.2) ∈ triangle 0 T := by
    intro q hq
    refine ⟨hq.1.1, ?_, ?_⟩
    · exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hq.1.2.1) hq.2.1)
    · calc
        q.1.1 + (q.1.2 - q.1.1) * q.2 ≤ q.1.1 + (q.1.2 - q.1.1) * 1 :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hq.2.2
            (sub_nonneg.mpr hq.1.2.1))
        _ = q.1.2 := by ring
        _ ≤ T := hq.1.2.2
  have hF : ContinuousOn (Function.uncurry F) (triangle 0 T ×ˢ Icc (0 : ℝ) 1) :=
    (continuousOn_snd.pow n).mul (hG.comp
      (show ContinuousOn
        (fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.1.1 + (q.1.2 - q.1.1) * q.2))
        (triangle 0 T ×ˢ Icc (0 : ℝ) 1) from (by fun_prop : Continuous _).continuousOn)
      hmap)
  refine ⟨fun p => ∫ t in (0 : ℝ)..1, F p t, continuousOn_power_integral_aux hF, ?_⟩
  intro u v hp
  have hc := hG.comp (continuousOn_const.prodMk continuousOn_id)
    (s := Icc u v) (fun _ hs => ⟨hp.1, hs.1, hs.2.trans hp.2.2⟩)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hp.2.1
    (hf.continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
      (fun _ hs => ⟨hp.1, hs.1, hs.2.trans hp.2.2⟩))
    (f' := fun s => (s - u) ^ n * G u s)
    (fun s hs => by
      have hd := hasDerivWithinAt_uncurry_triangle_v (u := u) (v := s) hf
        ⟨hp.1, hs.1.le, hs.2.le.trans hp.2.2⟩
      change HasDerivWithinAt (f u) (pdV (triangle 0 T) f u s) (Icc u T) s at hd
      rw [heq u s ⟨hp.1, hs.1.le, hs.2.le.trans hp.2.2⟩] at hd
      exact hd.hasDerivAt (Icc_mem_nhds hs.1 (hs.2.trans_le hp.2.2)))
    ((((continuousOn_id.sub continuousOn_const).pow n).mul hc).intervalIntegrable_of_Icc hp.2.1)
  change (∫ s in u..v, (s - u) ^ n * G u s) = f u v - f u u at hftc
  rw [haxis u ⟨hp.1, hp.2.1.trans hp.2.2⟩, sub_zero] at hftc
  rw [← hftc]
  calc
    _ = (v - u) * ∫ t in (0 : ℝ)..1,
        (u + (v - u) * t - u) ^ n * G u (u + (v - u) * t) := by
      simpa only [smul_eq_mul, mul_zero, mul_one, add_zero, add_sub_cancel_left,
        show u + (v - u) = v by ring] using
        (intervalIntegral.smul_integral_comp_add_mul
          (fun s => (s - u) ^ n * G u s) (v - u) u (a := (0 : ℝ)) (b := 1)).symm
    _ = (v - u) * ((v - u) ^ n * ∫ t in (0 : ℝ)..1, F (u, v) t) := by
      congr 1
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only [F]
      rw [add_sub_cancel_left, mul_pow]
      ring
    _ = _ := by rw [pow_succ]; ring

end EmcsfAcExtension.Local
