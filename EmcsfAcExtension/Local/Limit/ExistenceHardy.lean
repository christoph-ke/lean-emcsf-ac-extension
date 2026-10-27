module

public import EmcsfAcExtension.Local.Defs.Bounds
public import EmcsfAcExtension.Local.Defs.C1Class
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Local.Api.Finite
import EmcsfAcExtension.Local.Limit.UIAux
import EmcsfAcExtension.Infra.AC.Variation

/-! # Localized scalar variation from the smooth Hardy bounds

These are construction-side helpers only. They turn the actual smooth
Hardy conclusions into scalar variation bounds on axis-to-point intervals.
The ordinary incoming derivative retains its connection term.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

private theorem variation_eq_density {f q : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (q x) x) :
    eVariationOn f (Icc a b) = ∫⁻ x in Icc a b, ‖q x‖ₑ := by
  have hi : IntegrableOn (deriv f) (Icc a b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).1 hf.intervalIntegrable_deriv_complex
  rw [hf.eVariationOn_eq_integral_norm_deriv hab, intervalIntegral.integral_of_le hab,
    ← integral_Icc_eq_integral_Ioc, ofReal_integral_norm_eq_lintegral_enorm hi]
  apply lintegral_congr_ae
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [(hd x hx).deriv]

private theorem norm_div_eq_weight {r l : ℝ} (hr : 0 ≤ r) (hl : 0 < l) (z : ℂ) :
    ‖z / (r : ℂ)‖ = l / r * ‖z / (l : ℂ)‖ := by
  simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr, abs_of_pos hl]
  by_cases hz : r = 0
  · simp only [hz, div_zero, zero_mul]
  · field_simp [hz, hl.ne']

private theorem radius_nonneg {e T : ℝ} {S : Fields}
    (hs : IsC1Solution e S (triangle 0 T)) {p : ℝ × ℝ} (hp : p ∈ triangle 0 T) :
    0 ≤ S.r p.1 p.2 := by
  rcases hp.2.1.eq_or_lt with heq | hlt
  · simpa only [← heq, (hs.axis p.1 ⟨hp.1, le_rfl, heq ▸ hp.2.2⟩).1] using (le_rfl : (0 : ℝ) ≤ 0)
  · exact (hs.r_pos p hp hlt).le

/-- Localized outgoing scalar variation from the supplied smooth Hardy bound.
The constant `C` has exactly its original smooth a priori scope, uniformly in
the section and in every derivative supremum. -/
theorem phi_out_variation_of_bounds {C e T d M : ℝ} {S : Fields}
    (hs : IsC1Solution e S (triangle 0 T)) (hb : SmoothBounds C e T d M S)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ T) :
    eVariationOn (S.phi u) (Icc u v) ≤
      ENNReal.ofReal (C * ∫ s in u..v, (outEnv 0 (jC1 (triangle 0 T) S) s).toReal) := by
  have hac : AbsolutelyContinuousOnInterval (S.phi u) u v := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le huv]
    exact hs.c1_phi.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun x hx => ⟨hu, hx.1, hx.2.trans hv⟩)
  rw [variation_eq_density huv hac (q := S.phiV u) (by
    intro x hx
    have hp : (u, x) ∈ triangle 0 T := ⟨hu, hx.1.le, hx.2.le.trans hv⟩
    have hd := (hasDerivWithinAt_pdV hs.c1_phi hp (s := Icc u v)
      (fun y hy => ⟨hu, hy.1, hy.2.trans hv⟩)).hasDerivAt (Icc_mem_nhds hx.1 hx.2)
    rw [(hs.eq_v (u, x) hp hx.1).2.2.2.2.2.1] at hd
    exact hd)]
  apply le_trans ?_ (hb.hardyOut u v hu huv hv)
  apply setLIntegral_mono' measurableSet_Icc
  intro x hx
  have hp : (u, x) ∈ triangle 0 T := ⟨hu, hx.1, hx.2.trans hv⟩
  rw [← ofReal_norm, Fields.phiV, norm_div_eq_weight (radius_nonneg hs hp) (hs.lam_pos _ hp)]

/-- Localized ordinary incoming scalar variation from the supplied covariant
Hardy bound. `C` retains its smooth scope; the explicit connection remainder
uses the stated potential bound `B`, scalar bound `M` and actual section length. -/
theorem phi_in_variation_of_bounds {C e T d M B : ℝ} {S : Fields}
    (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hs : IsC1Solution e S (triangle 0 T)) (hb : SmoothBounds C e T d M S)
    (hA : ∀ p ∈ triangle 0 T, |S.A p.1 p.2| ≤ B)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ T) :
    eVariationOn (fun u => S.phi u v) (Icc u v) ≤
      ENNReal.ofReal (C * ∫ s in u..v, (inEnv T (kC1 e (triangle 0 T) S) s).toReal) +
      ENNReal.ofReal (|e| * B * M * (v - u)) := by
  have hac : AbsolutelyContinuousOnInterval (fun u => S.phi u v) u v := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le huv]
    exact hs.c1_phi.comp (contDiffOn_id.prodMk contDiffOn_const)
      (fun x hx => ⟨hu.trans hx.1, hx.2, hv⟩)
  rw [variation_eq_density huv hac (q := fun u => S.phiU e u v) (by
    intro x hx
    have hp : (x, v) ∈ triangle 0 T := ⟨hu.trans hx.1.le, hx.2.le, hv⟩
    have hd := (hasDerivWithinAt_pdU hs.c1_phi hp (s := Icc u v)
      (fun y hy => ⟨hu.trans hy.1, hy.2, hv⟩)).hasDerivAt (Icc_mem_nhds hx.1 hx.2)
    rw [(hs.eq_u (x, v) hp hx.2).2.2.2.2.1] at hd
    exact hd)]
  let F (x : ℝ) := ENNReal.ofReal (-S.nu x v / S.r x v * ‖S.xi x v / S.nu x v‖)
  have hpoint : ∀ x ∈ Icc u v, ‖S.phiU e x v‖ₑ ≤ F x + ENNReal.ofReal (|e| * B * M) := by
    intro x hx
    have hp : (x, v) ∈ triangle 0 T := ⟨hu.trans hx.1, hx.2, hv⟩
    have hnorm : ‖S.xi x v / (S.r x v : ℂ)‖ =
        -S.nu x v / S.r x v * ‖S.xi x v / S.nu x v‖ := by
      have hh := norm_div_eq_weight (radius_nonneg hs hp) (neg_pos.mpr (hs.nu_neg _ hp)) (S.xi x v)
      simpa only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_neg] using hh
    have hconn : ‖I * e * S.A x v * S.phi x v‖ ≤ |e| * B * M := by
      simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hA _ hp) (abs_nonneg _)) (hb.phi_le _ hp)
        (norm_nonneg _) (mul_nonneg (abs_nonneg _) hB)
    rw [← ofReal_norm, Fields.phiU]
    exact (ENNReal.ofReal_le_ofReal (norm_sub_le _ _)).trans
      ((ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)).le.trans
        (add_le_add (by rw [hnorm]) (ENNReal.ofReal_le_ofReal hconn)))
  calc
    (∫⁻ x in Icc u v, ‖S.phiU e x v‖ₑ) ≤
        ∫⁻ x in Icc u v, F x + ENNReal.ofReal (|e| * B * M) :=
      setLIntegral_mono' measurableSet_Icc hpoint
    _ = (∫⁻ x in Icc u v, F x) + ENNReal.ofReal (|e| * B * M * (v - u)) := by
      rw [lintegral_add_right F measurable_const, setLIntegral_const, Real.volume_Icc,
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ |e| * B * M)]
    _ ≤ _ := add_le_add (hb.hardyIn u v hu huv hv) le_rfl

end EmcsfAcExtension.Local
