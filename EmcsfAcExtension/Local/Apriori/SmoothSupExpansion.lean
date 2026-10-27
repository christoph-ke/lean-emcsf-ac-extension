module

public import EmcsfAcExtension.Local.Apriori.SmoothSupGeometrySource
import EmcsfAcExtension.Local.Apriori.GeometryEnvelopeTransport
import EmcsfAcExtension.Local.Apriori.GeometryEnvelopeInitial
import EmcsfAcExtension.Local.Apriori.SmoothSupRadial
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Calculus.AxisRates

/-! # Uniform first derivatives of both expansions

The two landed geometric transports give the same-direction derivatives
from their initial and matching axis values. Only scalar center decay is
needed; no second derivative bound is supplied as a premise.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem quadratic_correction {l r D : ℝ} {f : ℂ}
    (hr : 0 ≤ r) (_hD : 0 ≤ D) (hl : |l| ≤ 1) (hf : ‖f‖ ≤ D * r) :
    |l / r * ‖f‖ ^ 2| ≤ D ^ 2 * r := by
  by_cases hr0 : r = 0
  · simp [hr0]
  have hrp := lt_of_le_of_ne hr (Ne.symm hr0)
  simp only [abs_mul, abs_div, abs_pow, abs_norm, abs_of_pos hrp]
  calc
    _ ≤ 1 / r * (D * r) ^ 2 := by gcongr
    _ = _ := by field_simp

private theorem norm_le_of_enorm_le {x C : ℝ} (hC : 0 ≤ C)
    (hx : ‖x‖ₑ ≤ ENNReal.ofReal C) : |x| ≤ C := by
  simpa only [toReal_enorm, Real.norm_eq_abs, ENNReal.toReal_ofReal hC] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hx

/-- All four expansion partials have one finite bound chosen after
`e,R,M,D` and before `ε,S,h`. The only extra size information is the
displayed linear decay of both scalar ratios. Thus a datum-uniform
scalar budget gives datum-uniform expansion derivatives. -/
theorem smooth_expansion_partials_of_bound (e R M D : ℝ) (hD : 0 ≤ D) :
    ∃ B : ℝ, 0 < B ∧ ∀ (T ε : ℝ) (S : Fields) (h : ℝ → ℂ), T ≤ R →
      AprioriSetting e T ε M S h →
      (∀ q ∈ triangle 0 T,
        ‖S.theta q.1 q.2 / S.lam q.1 q.2‖ ≤ D * S.r q.1 q.2 ∧
        ‖S.xi q.1 q.2 / S.nu q.1 q.2‖ ≤ D * S.r q.1 q.2) →
      ∀ u v, (u, v) ∈ triangle 0 T →
        |pdU (triangle 0 T) S.lam u v| ≤ B ∧
        |pdV (triangle 0 T) S.lam u v| ≤ B ∧
        |pdU (triangle 0 T) S.nu u v| ≤ B ∧
        |pdV (triangle 0 T) S.nu u v| ≤ B := by
  obtain ⟨C, hC, hc⟩ := smooth_geometry_source_of_bound e R M D hD
  let B := 1 + 4 * (C + D ^ 2) * (|R| + 1)
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro T ε S h hTR hset hdecay
  have hT := hset.pos
  have hsource := hc T ε S h hTR hset hdecay
  have hrT (u v : ℝ) (hp : (u, v) ∈ triangle 0 T) : S.r u v ≤ T :=
    ((smooth_radius_bounds_aux hset hp).2).trans (by linarith only [hp.1, hp.2.2])
  have hcorr (u v : ℝ) (hp : (u, v) ∈ triangle 0 T) :
      |S.lam u v / S.r u v * ‖S.theta u v / S.lam u v‖ ^ 2| ≤ D ^ 2 * T ∧
      |S.nu u v / S.r u v * ‖S.xi u v / S.nu u v‖ ^ 2| ≤ D ^ 2 * T := by
    have hl : |S.lam u v| ≤ 1 := by
      rw [abs_of_pos (hset.c1.lam_pos _ hp)]
      exact (hset.box _ hp).2.1
    have hn : |S.nu u v| ≤ 1 := by
      rw [abs_of_neg (hset.c1.nu_neg _ hp)]
      exact (hset.box _ hp).2.2.2.1
    exact ⟨(quadratic_correction (hset.radius_nonneg hp) hD hl (hdecay _ hp).1).trans
        (mul_le_mul_of_nonneg_left (hrT u v hp) (sq_nonneg D)),
      (quadratic_correction (hset.radius_nonneg hp) hD hn (hdecay _ hp).2).trans
        (mul_le_mul_of_nonneg_left (hrT u v hp) (sq_nonneg D))⟩
  have hinitial (v : ℝ) (hv : v ∈ Icc 0 T) :
      |geomL (triangle 0 T) S 0 v| ≤ D ^ 2 * T := by
    rw [geomL, hset.initial_lam_partial hv, zero_div, zero_add]
    exact (hcorr 0 v ⟨le_rfl, hv.1, hv.2⟩).1
  have hL (u v : ℝ) (hp : (u, v) ∈ triangle 0 T) :
      |geomL (triangle 0 T) S u v| ≤ (D ^ 2 + C) * T := by
    have hb := geomL_characteristic_bound hset hp.1 hp.2.1 hp.2.2
    have hi : (∫⁻ x in Icc 0 v, ‖geomSource S x v‖ₑ) ≤ ENNReal.ofReal (C * T) := by
      calc
        _ ≤ ∫⁻ _x in Icc 0 v, ENNReal.ofReal C := by
          apply setLIntegral_mono' measurableSet_Icc
          intro x hx
          rw [← ofReal_norm, Real.norm_eq_abs]
          exact ENNReal.ofReal_le_ofReal (hsource x v ⟨hx.1, hx.2, hp.2.2⟩).1
        _ ≤ _ := by
          rw [setLIntegral_const, Real.volume_Icc, sub_zero,
            ← ENNReal.ofReal_mul hC.le]
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hp.2.2 hC.le)
    apply norm_le_of_enorm_le (by positivity)
    apply hb.trans
    have hinit : ‖geomL (triangle 0 T) S 0 v‖ₑ ≤ ENNReal.ofReal (D ^ 2 * T) := by
      rw [← ofReal_norm, Real.norm_eq_abs]
      exact ENNReal.ofReal_le_ofReal (hinitial v ⟨hp.1.trans hp.2.1, hp.2.2⟩)
    apply (add_le_add hinit hi).trans_eq
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have hN (u v : ℝ) (hp : (u, v) ∈ triangle 0 T) :
      |geomN (triangle 0 T) S u v| ≤ (D ^ 2 + 2 * C) * T := by
    have hb := geomN_characteristic_bound hset hp.1 hp.2.1 hp.2.2
    have hi : (∫⁻ x in Icc u T, ‖geomSource S u x‖ₑ) ≤ ENNReal.ofReal (C * T) := by
      calc
        _ ≤ ∫⁻ _x in Icc u T, ENNReal.ofReal C := by
          apply setLIntegral_mono' measurableSet_Icc
          intro x hx
          rw [← ofReal_norm, Real.norm_eq_abs]
          exact ENNReal.ofReal_le_ofReal (hsource u x ⟨hp.1, hx.1, hx.2⟩).1
        _ ≤ _ := by
          rw [setLIntegral_const, Real.volume_Icc, ← ENNReal.ofReal_mul hC.le]
          exact ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_left (sub_le_self T hp.1) hC.le)
    apply norm_le_of_enorm_le (by positivity)
    apply hb.trans
    have ha : ‖geomL (triangle 0 T) S u u‖ₑ ≤ ENNReal.ofReal ((D ^ 2 + C) * T) := by
      rw [← ofReal_norm, Real.norm_eq_abs]
      exact ENNReal.ofReal_le_ofReal (hL u u ⟨hp.1, le_rfl, hp.2.1.trans hp.2.2⟩)
    apply (add_le_add ha hi).trans_eq
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  intro u v hp
  change 0 ≤ u ∧ u ≤ v ∧ v ≤ T at hp
  have hl := hset.c1.lam_pos (u, v) hp
  have hn := hset.c1.nu_neg (u, v) hp
  have hLamV : |pdV (triangle 0 T) S.lam u v| ≤ (2 * D ^ 2 + C) * T := by
    have heq : pdV (triangle 0 T) S.lam u v = S.lam u v *
        (geomL (triangle 0 T) S u v - S.lam u v / S.r u v *
          ‖S.theta u v / S.lam u v‖ ^ 2) := by
      rw [geomL]
      field_simp [hl.ne']
      ring
    rw [heq, abs_mul]
    have hh := (abs_sub _ _).trans (add_le_add (hL u v hp) (hcorr u v hp).1)
    have hLam : |S.lam u v| ≤ 1 := by
      rw [abs_of_pos hl]
      exact (hset.box _ hp).2.1
    apply (mul_le_mul hLam hh (abs_nonneg _) (by norm_num)).trans_eq
    ring
  have hNuU : |pdU (triangle 0 T) S.nu u v| ≤ (2 * D ^ 2 + 2 * C) * T := by
    have heq : pdU (triangle 0 T) S.nu u v = S.nu u v *
        (geomN (triangle 0 T) S u v - S.nu u v / S.r u v *
          ‖S.xi u v / S.nu u v‖ ^ 2) := by
      rw [geomN]
      field_simp [hn.ne]
      ring
    rw [heq, abs_mul]
    have hh := (abs_sub _ _).trans (add_le_add (hN u v hp) (hcorr u v hp).2)
    have hNu : |S.nu u v| ≤ 1 := by
      rw [abs_of_neg hn]
      exact (hset.box _ hp).2.2.2.1
    apply (mul_le_mul hNu hh (abs_nonneg _) (by norm_num)).trans_eq
    ring
  have hCT : C * T ≤ B := by
    dsimp only [B]
    rw [abs_of_pos (hT.trans_le hTR)]
    have hi := mul_le_mul_of_nonneg_left hTR hC.le
    nlinarith only [hi, mul_nonneg (sq_nonneg D) (hT.le.trans hTR), hC.le, hT.le]
  have hbig : (2 * D ^ 2 + 2 * C) * T ≤ B := by
    dsimp only [B]
    rw [abs_of_pos (hT.trans_le hTR)]
    have hi := mul_le_mul_of_nonneg_left hTR (show 0 ≤ 2 * D ^ 2 + 2 * C by positivity)
    nlinarith only [hi, mul_nonneg (sq_nonneg D) (hT.le.trans hTR), hC.le, hT.le]
  have hcross : |pdU (triangle 0 T) S.lam u v| ≤ B ∧
      |pdV (triangle 0 T) S.nu u v| ≤ B := by
    rcases eq_or_lt_of_le hp.2.1 with rfl | huv
    · rw [(expansion_axis_cross_partials_aux hT hset.c1 ⟨hp.1, hp.2.2⟩).1,
        (expansion_axis_cross_partials_aux hT hset.c1 ⟨hp.1, hp.2.2⟩).2]
      simpa only [abs_zero] using And.intro hB.le hB.le
    · rw [(hset.c1.eq_u (u, v) hp huv).2.1, (hset.c1.eq_v (u, v) hp huv).2.1]
      have hh := ((hsource u v hp).2).trans
        ((mul_le_mul_of_nonneg_left (hrT u v hp) hC.le).trans hCT)
      exact ⟨hh, hh⟩
  refine ⟨hcross.1, hLamV.trans ?_, hNuU.trans hbig, hcross.2⟩
  exact (by nlinarith only [mul_nonneg hC.le hT.le] :
    (2 * D ^ 2 + C) * T ≤ (2 * D ^ 2 + 2 * C) * T).trans hbig

end EmcsfAcExtension.Local
