module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.Moments
import EmcsfAcExtension.Local.Stability.MomentsIncoming

/-! # Quadratic versions of the stability Hardy bounds

Multiplying the correctly oriented linear estimate by the small ratio
bound gives the quadratic flux estimate. Both axis endpoints are retained.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem quadratic_integral_le {I : Set ℝ} {W y : ℝ → ℝ} {ε : ℝ}
    (hI : MeasurableSet I) (hε : 0 ≤ ε)
    (hW : ∀ s ∈ I, 0 ≤ W s) (hy : ∀ s ∈ I, 0 ≤ y s ∧ y s ≤ ε) :
    (∫⁻ s in I, ENNReal.ofReal (W s * y s ^ 2)) ≤
      ENNReal.ofReal ε * ∫⁻ s in I, ENNReal.ofReal (W s * y s) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' hI
  intro s hs
  rw [← ENNReal.ofReal_mul hε]
  apply ENNReal.ofReal_le_ofReal
  have hb := mul_le_mul_of_nonneg_right (hy s hs).2 (hy s hs).1
  calc
    _ ≤ W s * (ε * y s) := by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_left hb (hW s hs)
    _ = _ := by ring

variable {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}

/-- The outgoing quadratic Hardy estimate from the exact outgoing identity.
The exact coefficient is `(16/3) ε`, with the numerical constant universal
and independent of all fields, scales, and derivative suprema. -/
theorem stab_out_hardy_quadratic_of_identity (hset : StabSetting e T ε M A S h)
    (hidentity : ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ T →
      HasDerivWithinAt (fun s => S.theta u s / (S.lam u s : ℂ))
        (jC1 (triangle 0 T) S u v / ((1 - S.mu u v : ℝ) : ℂ) -
          (S.lam u v / S.r u v * (1 - ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2)) •
            (S.theta u v / (S.lam u v : ℂ))) (Icc u T) v)
    (hε : ε ^ 2 ≤ 1 / 4) {u : ℝ} (hu : 0 ≤ u) (huT : u ≤ T) :
    (∫⁻ s in Ioc u T, ENNReal.ofReal
      (S.lam u s / S.r u s * ‖S.theta u s / (S.lam u s : ℂ)‖ ^ 2)) ≤
      ENNReal.ofReal ((16 / 3) * ε) *
        ∫⁻ s in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S) s := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S.xi u u / (S.nu u u : ℂ)))).trans
      (hset.box.2 (u, u) ⟨hu, le_rfl, huT⟩).2.2.2.2.2.1)
  have hquad := quadratic_integral_le (I := Ioc u T)
    (W := fun s => S.lam u s / S.r u s)
    (y := fun s => ‖S.theta u s / (S.lam u s : ℂ)‖) measurableSet_Ioc hε0
    (fun s hs => div_nonneg (hset.c1.lam_pos (u, s) ⟨hu, hs.1.le, hs.2⟩).le
      (hset.c1.r_pos (u, s) ⟨hu, hs.1.le, hs.2⟩ hs.1).le)
    (fun s hs => ⟨norm_nonneg _,
      (le_add_of_nonneg_right (norm_nonneg (S.xi u s / (S.nu u s : ℂ)))).trans
        (hset.box.2 (u, s) ⟨hu, hs.1.le, hs.2⟩).2.2.2.2.2.1⟩)
  apply hquad.trans
  apply (mul_le_mul' le_rfl (stab_out_hardy_of_identity hset hidentity hε hu huT)).trans_eq
  rw [← mul_assoc, ← ENNReal.ofReal_mul hε0, mul_comm ε]

/-- The incoming quadratic Hardy estimate from the exact incoming identity.
The exact coefficient is `(16/3) ε`, uniformly in every solution parameter.
The incoming ratio is `ξ/ν`, in the orientation required by the source. -/
theorem stab_in_hardy_quadratic_of_identity (hset : StabSetting e T ε M A S h)
    (hidentity : ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ T →
      HasDerivWithinAt (fun s => S.xi s v / (S.nu s v : ℂ))
        (kC1 e (triangle 0 T) S u v / ((1 - S.mu u v : ℝ) : ℂ) -
          (S.nu u v / S.r u v * (1 - ‖S.xi u v / (S.nu u v : ℂ)‖ ^ 2)) •
            (S.xi u v / (S.nu u v : ℂ)) -
          (e * S.A u v) • (Complex.I * (S.xi u v / (S.nu u v : ℂ)))) (Icc 0 v) u)
    (hε : ε ^ 2 ≤ 1 / 4) {v : ℝ} (hv : 0 ≤ v) (hvT : v ≤ T) :
    (∫⁻ s in Icc 0 v, ENNReal.ofReal
      (-S.nu s v / S.r s v * ‖S.xi s v / (S.nu s v : ℂ)‖ ^ 2)) ≤
      ENNReal.ofReal ((16 / 3) * ε) *
        ∫⁻ s in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S) s := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S.xi v v / (S.nu v v : ℂ)))).trans
      (hset.box.2 (v, v) ⟨hv, le_rfl, hvT⟩).2.2.2.2.2.1)
  have hquad := quadratic_integral_le (I := Icc 0 v)
    (W := fun s => -S.nu s v / S.r s v)
    (y := fun s => ‖S.xi s v / (S.nu s v : ℂ)‖) measurableSet_Icc hε0
    (fun s hs => div_nonneg (neg_pos.mpr
      (hset.c1.nu_neg (s, v) ⟨hs.1, hs.2, hvT⟩)).le
      ((div_nonneg (sub_nonneg.mpr hs.2) (by norm_num : (0 : ℝ) ≤ 4)).trans
        (stab_radius_bounds hset hs.1 hs.2 hvT).1))
    (fun s hs => ⟨norm_nonneg _,
      (le_add_of_nonneg_left (norm_nonneg (S.theta s v / (S.lam s v : ℂ)))).trans
        (hset.box.2 (s, v) ⟨hs.1, hs.2, hvT⟩).2.2.2.2.2.1⟩)
  apply hquad.trans
  apply (mul_le_mul' le_rfl (stab_in_hardy_of_identity hset hidentity hε hv hvT)).trans_eq
  rw [← mul_assoc, ← ENNReal.ofReal_mul hε0, mul_comm ε]

end EmcsfAcExtension.Local
