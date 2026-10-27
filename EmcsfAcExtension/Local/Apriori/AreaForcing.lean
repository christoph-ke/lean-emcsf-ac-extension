module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Defs.Renormalized
import EmcsfAcExtension.Local.Apriori.Area
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Apriori.ChargeSource
import EmcsfAcExtension.Local.Apriori.ChargePrimitive

/-! # Electromagnetic characteristic forcing budgets

The two integration orders are stated separately, matching the outgoing and
incoming envelope equations in `charged_SF_new_version.tex:L4665–L4668`.
-/

public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Area

/-- [node restart-sec-independent-area#electromagnetic-envelope-forcing]
Direct electromagnetic forcing in both characteristic integration orders
(`charged_SF_new_version.tex:L4665–L4666`), before homogeneous amplification.
`C` is universal, independent of `e`, `s`, `M`, and all higher data norms.
The fixed threshold `ε ≤ 1` suffices. -/
theorem electromagnetic_envelope_forcing :
    ∃ C : ℝ, 0 < C ∧ ∀ (e s ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e s ε M S h → ε ≤ 1 →
      (∫⁻ v in Icc 0 s, ∫⁻ u in Icc 0 v, ‖emSourceJ e S u v‖ₑ) ≤
        ENNReal.ofReal (C * (|e| * (s / 2) * M) ^ 2 * ε) ∧
      (∫⁻ u in Icc 0 s, ∫⁻ v in Icc u s, ‖emSourceK e S u v‖ₑ) ≤
        ENNReal.ofReal (C * (|e| * (s / 2) * M) ^ 2 * ε) := by
  obtain ⟨C, hC0, hC⟩ := bv_e_bounds
  refine ⟨4 * C, by positivity, ?_⟩
  intro e s ε M S h hset hε
  have hA : 0 ≤ C * e ^ 2 * M ^ 2 * ε := by
    have := hset.eps_nonneg
    positivity
  have hb (u v : ℝ) (hp : (u, v) ∈ triangle 0 s) :
      ‖emSourceJ e S u v‖ ≤ C * e ^ 2 * M ^ 2 * ε * (-S.nu u v) * S.lam u v ∧
      ‖emSourceK e S u v‖ ≤ C * e ^ 2 * M ^ 2 * ε * (-S.nu u v) * S.lam u v := by
    rcases eq_or_lt_of_le hp.2.1 with huv | huv
    · change u = v at huv
      subst v
      have hr := (hset.c1.axis u hp).1
      have hn := (neg_pos.mpr (hset.c1.nu_neg (u, u) hp)).le
      have hl := (hset.c1.lam_pos (u, u) hp).le
      simp only [emSourceJ, emSourceK, hr, Complex.ofReal_zero, zero_pow (by decide : 2 ≠ 0),
        div_zero, zero_mul, mul_zero, add_zero, norm_zero]
      constructor <;> positivity
    · have he := hC e s ε M S h hset hε u v hp.1 huv hp.2.2
      exact ⟨(le_add_of_nonneg_right (norm_nonneg _)).trans he,
        (le_add_of_nonneg_left (norm_nonneg _)).trans he⟩
  constructor
  · convert area_integral_in_le_of_pointwise hset hA
      (fun u v => ‖emSourceJ e S u v‖ₑ)
      (fun u v hp => by rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hb u v hp).1)
      using 1
    congr 1
    simp only [mul_pow, sq_abs]
    ring
  · convert area_integral_le_of_pointwise hset hA
      (fun u v => ‖emSourceK e S u v‖ₑ)
      (fun u v hp => by rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hb u v hp).2)
      using 1
    congr 1
    simp only [mul_pow, sq_abs]
    ring

private theorem norm_curvature_multiplier_le {c d r ε B : ℝ} {z D : ℂ}
    (hr : 0 < r) (hε : 0 ≤ ε) (hd : 0 ≤ d) (_hB : 0 ≤ B)
    (hz : ‖z‖ ≤ 4 * ε * d) (hD : ‖D‖ ≤ B * r ^ 2) :
    ‖((c : ℂ) * z / (r : ℂ) ^ 2) * (D + 2 * starRingEnd ℂ D)‖ ≤
      12 * B * ε * |c| * d := by
  have hsum : ‖D + 2 * starRingEnd ℂ D‖ ≤ 3 * ‖D‖ := by
    calc
      _ ≤ ‖D‖ + ‖(2 : ℂ)‖ * ‖starRingEnd ℂ D‖ := by
        simpa only [norm_mul] using norm_add_le D (2 * starRingEnd ℂ D)
      _ = _ := by simp; ring
  have hsum' := hsum.trans (mul_le_mul_of_nonneg_left hD (by norm_num : (0 : ℝ) ≤ 3))
  simp only [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr]
  calc
    _ ≤ (|c| * (4 * ε * d) / r ^ 2) * (3 * (B * r ^ 2)) := by gcongr
    _ = _ := by field_simp; ring

/-- [node restart-sec-independent-area#electromagnetic-curvature-forcing]
The electric curvature remainders in the `j` and `k` transports have area
cost `C (|e| R M)² ε³` (`charged_SF_new_version.tex:L4666–L4668`). `C` is universal,
independent of all solution parameters and higher data norms. The incoming
primitive is written explicitly; its overall axis-orientation sign does not
affect the estimate. No smallness hypothesis is required. -/
theorem electromagnetic_curvature_forcing :
    ∃ C : ℝ, 0 < C ∧ ∀ (e s ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e s ε M S h →
      (∫⁻ v in Icc 0 s, ∫⁻ u in Icc 0 v,
        ‖(S.nu u v * S.theta u v / S.r u v ^ 2) *
          (curvEM e S u v + 2 * starRingEnd ℂ (curvEM e S u v))‖ₑ) ≤
        ENNReal.ofReal (C * (|e| * (s / 2) * M) ^ 2 * ε ^ 3) ∧
      (∫⁻ u in Icc 0 s, ∫⁻ v in Icc u s,
        let D := (S.r u v : ℂ)⁻¹ * ∫ x in u..v,
          (((S.nu x v * S.Q x v ^ 2 / S.r x v ^ 2 : ℝ) : ℂ) +
            I * e * S.Q x v * S.xi x v * starRingEnd ℂ (S.phi x v))
        ‖(S.lam u v * S.xi u v / S.r u v ^ 2) * (D + 2 * starRingEnd ℂ D)‖ₑ) ≤
        ENNReal.ofReal (C * (|e| * (s / 2) * M) ^ 2 * ε ^ 3) := by
  obtain ⟨Co, hCo, ho⟩ := bv_c_charge
  obtain ⟨Ci, hCi, hi⟩ := incoming_curvature_charge
  refine ⟨48 * (Co + Ci), by positivity, ?_⟩
  intro e s ε M S h hset
  have hε := hset.eps_nonneg
  have hB : 0 ≤ (Co + Ci) * e ^ 2 * M ^ 2 * ε ^ 2 := by positivity
  have hA : 0 ≤ 12 * ((Co + Ci) * e ^ 2 * M ^ 2 * ε ^ 2) * ε := by positivity
  have hCo' : Co ≤ Co + Ci := le_add_of_nonneg_right hCi.le
  have hCi' : Ci ≤ Co + Ci := le_add_of_nonneg_left hCo.le
  constructor
  · have hb (u v : ℝ) (hp : (u, v) ∈ triangle 0 s) :
        ‖(S.nu u v * S.theta u v / S.r u v ^ 2) *
          (curvEM e S u v + 2 * starRingEnd ℂ (curvEM e S u v))‖ₑ ≤
          ENNReal.ofReal ((12 * ((Co + Ci) * e ^ 2 * M ^ 2 * ε ^ 2) * ε) *
            (-S.nu u v) * S.lam u v) := by
      rw [← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal
      rcases eq_or_lt_of_le hp.2.1 with huv | huv
      · change u = v at huv
        subst v
        simp only [(hset.c1.axis u hp).1, Complex.ofReal_zero, zero_pow (by decide : 2 ≠ 0),
          div_zero, zero_mul, norm_zero]
        exact mul_nonneg (mul_nonneg hA
          (neg_pos.mpr (hset.c1.nu_neg (u, u) hp)).le) (hset.c1.lam_pos (u, u) hp).le
      · have hD : ‖curvEM e S u v‖ ≤
            ((Co + Ci) * e ^ 2 * M ^ 2 * ε ^ 2) * S.r u v ^ 2 :=
          (ho e s ε M S h hset u v hp.1 huv hp.2.2).trans
          (by gcongr)
        have he := norm_curvature_multiplier_le (c := S.nu u v)
          (hset.c1.r_pos (u, v) hp huv) hε
          (hset.c1.lam_pos (u, v) hp).le hB (hset.theta_norm_le hp) hD
        simpa only [abs_of_neg (hset.c1.nu_neg (u, v) hp), Complex.ofReal_pow, mul_assoc] using he
    convert area_integral_in_le_of_pointwise hset hA _ hb using 1
    congr 1
    simp only [mul_pow, sq_abs]
    ring
  · have hb (u v : ℝ) (hp : (u, v) ∈ triangle 0 s) :
        let D := (S.r u v : ℂ)⁻¹ * ∫ x in u..v,
          (((S.nu x v * S.Q x v ^ 2 / S.r x v ^ 2 : ℝ) : ℂ) +
            I * e * S.Q x v * S.xi x v * starRingEnd ℂ (S.phi x v))
        ‖(S.lam u v * S.xi u v / S.r u v ^ 2) * (D + 2 * starRingEnd ℂ D)‖ₑ ≤
          ENNReal.ofReal ((12 * ((Co + Ci) * e ^ 2 * M ^ 2 * ε ^ 2) * ε) *
            (-S.nu u v) * S.lam u v) := by
      dsimp only
      rw [← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal
      rcases eq_or_lt_of_le hp.2.1 with huv | huv
      · change u = v at huv
        subst v
        simp only [(hset.c1.axis u hp).1, Complex.ofReal_zero, zero_pow (by decide : 2 ≠ 0),
          div_zero, zero_mul, norm_zero]
        exact mul_nonneg (mul_nonneg hA
          (neg_pos.mpr (hset.c1.nu_neg (u, u) hp)).le) (hset.c1.lam_pos (u, u) hp).le
      · have hD : ‖(S.r u v : ℂ)⁻¹ * ∫ x in u..v,
            (((S.nu x v * S.Q x v ^ 2 / S.r x v ^ 2 : ℝ) : ℂ) +
              I * e * S.Q x v * S.xi x v * starRingEnd ℂ (S.phi x v))‖ ≤
            ((Co + Ci) * e ^ 2 * M ^ 2 * ε ^ 2) * S.r u v ^ 2 :=
          (hi e s ε M S h hset u v hp.1 huv hp.2.2).trans
          (by gcongr)
        have he := norm_curvature_multiplier_le (c := S.lam u v)
          (hset.c1.r_pos (u, v) hp huv) hε
          (neg_pos.mpr (hset.c1.nu_neg (u, v) hp)).le hB (hset.xi_norm_le hp) hD
        convert he using 1
        simp only [abs_of_pos (hset.c1.lam_pos (u, v) hp)]
        ring
    convert area_integral_le_of_pointwise hset hA _ hb using 1
    congr 1
    simp only [mul_pow, sq_abs]
    ring

end EmcsfAcExtension.Local.Area
