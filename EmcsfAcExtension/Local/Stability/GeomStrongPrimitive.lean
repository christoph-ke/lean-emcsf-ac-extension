module

public import EmcsfAcExtension.Local.Stability.OrderedKernelArea
import EmcsfAcExtension.Local.Stability.GeomStrongMoment

/-! # Ordered bounds for variable geometric scalar primitives

A signed primitive radius and an independent moment radius allow the
four terms in a geometric source subtraction to use the same lemma.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- A geometric primitive obeys its ordered majorant before area
integration. The coefficient is exactly `C * B * D`, uniformly in
every function and endpoint. `B` is the moment coefficient, `D` the
relative primitive-radius bound, and `C` the outer cubic coefficient.
-/
theorem stab_geometric_primitive_ordered_of_moment
    {u v p B C D : ℝ} {R r : ℝ → ℝ} {ρ : ℝ → ℝ → ℝ}
    {y j : ℝ → ℂ} {K J : ℝ → ℝ≥0∞} {c : ℂ}
    (huv : u < v) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hR : ∀ w ∈ Ioc u v, 0 < R w ∧ R w ≤ v - u)
    (hr : ∀ w ∈ Ioc u v, |r w| ≤ D * R w)
    (hρ : ∀ w ∈ Ioc u v, ∀ s ∈ Icc u w, 0 ≤ ρ w s ∧ ρ w s ≤ w - s)
    (hk : ∀ w ∈ Ioc u v, AEMeasurable
      (fun s => ENNReal.ofReal ((ρ w s / R w) ^ p) * K s) (volume.restrict (Icc u w)))
    (hmoment : ∀ w ∈ Ioc u v, ENNReal.ofReal ‖y w‖ ≤
      ENNReal.ofReal B * ∫⁻ s in Icc u w, ENNReal.ofReal ((ρ w s / R w) ^ p) * K s)
    (hj : ∀ w ∈ Ioc u v, ‖j w‖ₑ ≤ J w)
    (hc : ‖c‖ₑ ≤ ENNReal.ofReal (C / (v - u) ^ 3)) :
    ‖c * ∫ w in u..v, (r w : ℂ) * starRingEnd ℂ (y w) * j w‖ₑ ≤
      ENNReal.ofReal (C * B * D) * stabOrderedKernel p K J u v := by
  have hL : 0 < v - u := sub_pos.mpr huv
  have hpower w (hw : w ∈ Ioc u v) s (hs : s ∈ Icc u w) :
      |r w| * (ρ w s / R w) ^ p ≤
        (D * (v - u) ^ (1 - p)) * (w - s) ^ p := by
    calc
      _ ≤ (D * R w) * (ρ w s / R w) ^ p :=
        mul_le_mul_of_nonneg_right (hr w hw)
          (Real.rpow_nonneg (div_nonneg (hρ w hw s hs).1 (hR w hw).1.le) p)
      _ = D * (R w * (ρ w s / R w) ^ p) := by ring
      _ ≤ D * ((v - u) ^ (1 - p) * (w - s) ^ p) :=
        mul_le_mul_of_nonneg_left (stab_radius_power_product_le (hR w hw).1
          (hR w hw).2 (hρ w hw s hs).1 (hρ w hw s hs).2 hp0 hp1) hD
      _ = _ := by ring
  have hm := stab_integral_moment_product_le_of_variable_bound
    (I := Ioc u v) (E := fun w => Icc u w) (R := fun w => |r w|)
    (q := fun w s => (ρ w s / R w) ^ p) (P := fun w s => (w - s) ^ p)
    (y := y) (K := K) (J := J) (B := D * (v - u) ^ (1 - p)) (C := B)
    measurableSet_Ioc (fun _ _ => measurableSet_Icc)
    (mul_nonneg hD (Real.rpow_nonneg hL.le _)) hB (fun _ _ => abs_nonneg _)
    (fun w hw s hs => Real.rpow_nonneg (div_nonneg (hρ w hw s hs).1 (hR w hw).1.le) p)
    (fun w hw s hs => Real.rpow_nonneg (sub_nonneg.mpr hs.2) p) hk hmoment hpower
  have hprimitive : ‖c * ∫ w in u..v, (r w : ℂ) * starRingEnd ℂ (y w) * j w‖ₑ ≤
      ‖c‖ₑ * ∫⁻ w in Ioc u v, ENNReal.ofReal |r w| * ENNReal.ofReal ‖y w‖ * J w := by
    rw [enorm_mul, intervalIntegral.integral_of_le huv.le]
    apply mul_le_mul' le_rfl
    apply (enorm_integral_le_lintegral_enorm _).trans
    apply setLIntegral_mono' measurableSet_Ioc
    intro w hw
    rw [enorm_mul, enorm_mul, ← ofReal_norm (r w : ℂ), Complex.norm_real,
      Real.norm_eq_abs, RCLike.enorm_conj, ofReal_norm]
    exact mul_le_mul' le_rfl (hj w hw)
  apply hprimitive.trans
  apply (mul_le_mul' hc hm).trans_eq
  rw [← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg hC (pow_nonneg hL.le 3))]
  have hcoeff : (C / (v - u) ^ 3) * (B * (D * (v - u) ^ (1 - p))) =
      (C * B * D) * (v - u) ^ (-p - 2) := by
    have hh : (v - u) ^ (1 - p) / (v - u) ^ (3 : ℝ) =
        (v - u) ^ (-p - 2) := by
      rw [← Real.rpow_sub hL]
      congr 1
      ring
    norm_num at hh
    calc
      _ = (C * B * D) * ((v - u) ^ (1 - p) / (v - u) ^ 3) := by ring
      _ = _ := congrArg (fun t : ℝ => (C * B * D) * t) hh
  rw [hcoeff, ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hC hB) hD),
    stabOrderedKernel, restrict_Ioc_eq_restrict_Icc]
  ac_rfl

end EmcsfAcExtension.Local
