module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Defs.Renormalized
import EmcsfAcExtension.Local.Apriori.ChargePrimitive
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Apriori.Area

/-! # Electromagnetic area cost of the geometric transport

The electric curvature primitive and the explicit charge square have a
regular area majorant. This is `charged_SF_new_version.tex:L4884–L4885` and uses no
scalar envelope closure.
-/

public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem electric_geometric_source_le {e s ε M C : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hC : 0 < C) (hset : AprioriSetting e s ε M S h) {u v : ℝ}
    (hp : (u, v) ∈ triangle 0 s)
    (hcurv : ‖curvEM e S u v‖ ≤ C * e ^ 2 * M ^ 2 * ε ^ 2 * S.r u v ^ 2) :
    |-2 * S.nu u v * S.lam u v / ((1 - S.mu u v) * S.r u v ^ 2) *
        ((curvEM e S u v).re - 2 * S.Q u v ^ 2 / S.r u v ^ 2)| ≤
      (4 * (C + 8) * e ^ 2 * M ^ 2 * ε ^ 2) * (-S.nu u v) * S.lam u v := by
  have hn := hset.c1.nu_neg (u, v) hp
  have hn0 := (neg_pos.mpr hn).le
  have hl := hset.c1.lam_pos (u, v) hp
  have hh := hset.c1.one_sub_mu_pos (u, v) hp
  by_cases hr : S.r u v = 0
  · have hz : |-2 * S.nu u v * S.lam u v / ((1 - S.mu u v) * S.r u v ^ 2) *
        ((curvEM e S u v).re - 2 * S.Q u v ^ 2 / S.r u v ^ 2)| = 0 := by simp [hr]
    rw [hz]
    positivity
  have hq := hset.charge_sq_div_le hp
  have hnum : |(curvEM e S u v).re - 2 * S.Q u v ^ 2 / S.r u v ^ 2| ≤
      (C + 8) * e ^ 2 * M ^ 2 * ε ^ 2 * S.r u v ^ 2 := by
    calc
      _ ≤ |(curvEM e S u v).re| + |2 * (S.Q u v ^ 2 / S.r u v ^ 2)| := by
        simpa only [mul_div_assoc] using abs_sub (curvEM e S u v).re
          (2 * (S.Q u v ^ 2 / S.r u v ^ 2))
      _ ≤ ‖curvEM e S u v‖ + 2 * (S.Q u v ^ 2 / S.r u v ^ 2) := by
        rw [abs_of_nonneg (by positivity : 0 ≤ 2 * (S.Q u v ^ 2 / S.r u v ^ 2))]
        exact add_le_add (Complex.abs_re_le_norm _) le_rfl
      _ ≤ C * e ^ 2 * M ^ 2 * ε ^ 2 * S.r u v ^ 2 +
          2 * (4 * e ^ 2 * M ^ 2 * ε ^ 2 * S.r u v ^ 2) := by gcongr
      _ = _ := by ring
  have hfrac := (div_le_iff₀ (sq_pos_of_ne_zero hr)).mpr hnum
  have hgap : 2 / (1 - S.mu u v) ≤ 4 := by
    apply (div_le_iff₀ hh).mpr
    linarith only [(hset.box (u, v) hp).2.2.2.2.1]
  calc
    _ = (2 / (1 - S.mu u v)) * (-S.nu u v) * S.lam u v *
        (|(curvEM e S u v).re - 2 * S.Q u v ^ 2 / S.r u v ^ 2| / S.r u v ^ 2) := by
      rw [abs_mul, abs_div, abs_mul, abs_mul, abs_of_neg hn, abs_of_pos hl,
        abs_of_pos (mul_pos hh (sq_pos_of_ne_zero hr))]
      simp only [div_eq_mul_inv, mul_inv_rev]
      norm_num
      ring
    _ ≤ 4 * (-S.nu u v) * S.lam u v * ((C + 8) * e ^ 2 * M ^ 2 * ε ^ 2) := by
      gcongr
    _ = _ := by ring

/-- [node restart-sec-independent-area#electromagnetic-geometric-area]
Both integration orders of the electric terms in the common geometric
transport source, `charged_SF_new_version.tex:L4884–L4885`. `C` is universal,
independent of `e,s,ε,M,S,h` and higher initial derivatives. The charged
scale is explicit and no smallness assumption is required. -/
theorem electromagnetic_geometric_area :
    ∃ C : ℝ, 0 < C ∧ ∀ (e s ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
      AprioriSetting e s ε M S h →
        (∫⁻ u in Icc 0 s, ∫⁻ v in Icc u s,
          ENNReal.ofReal (|-2 * S.nu u v * S.lam u v /
            ((1 - S.mu u v) * S.r u v ^ 2) *
              ((curvEM e S u v).re - 2 * S.Q u v ^ 2 / S.r u v ^ 2)|)) ≤
          ENNReal.ofReal (C * (|e| * (s / 2) * M) ^ 2 * ε ^ 2) ∧
        (∫⁻ v in Icc 0 s, ∫⁻ u in Icc 0 v,
          ENNReal.ofReal (|-2 * S.nu u v * S.lam u v /
            ((1 - S.mu u v) * S.r u v ^ 2) *
              ((curvEM e S u v).re - 2 * S.Q u v ^ 2 / S.r u v ^ 2)|)) ≤
          ENNReal.ofReal (C * (|e| * (s / 2) * M) ^ 2 * ε ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := bv_c_charge
  refine ⟨16 * (C + 8), by positivity, ?_⟩
  intro e s ε M S h hset
  let F (u v : ℝ) := ENNReal.ofReal
    (|-2 * S.nu u v * S.lam u v / ((1 - S.mu u v) * S.r u v ^ 2) *
      ((curvEM e S u v).re - 2 * S.Q u v ^ 2 / S.r u v ^ 2)|)
  have hb (u v : ℝ) (hp : (u, v) ∈ triangle 0 s) : F u v ≤
      ENNReal.ofReal ((4 * (C + 8) * e ^ 2 * M ^ 2 * ε ^ 2) *
        (-S.nu u v) * S.lam u v) := by
    apply ENNReal.ofReal_le_ofReal
    by_cases huv : u < v
    · exact electric_geometric_source_le hC hset hp
        (hbound e s ε M S h hset u v hp.1 huv hp.2.2)
    · have heq : u = v := le_antisymm hp.2.1 (le_of_not_gt huv)
      have hr : S.r u v = 0 := by
        rw [← heq]
        exact (hset.c1.axis u (by simpa only [heq] using hp)).1
      have hn := hset.c1.nu_neg (u, v) hp
      have hn0 := (neg_pos.mpr hn).le
      have hl := hset.c1.lam_pos (u, v) hp
      have hz : |-2 * S.nu u v * S.lam u v / ((1 - S.mu u v) * S.r u v ^ 2) *
          ((curvEM e S u v).re - 2 * S.Q u v ^ 2 / S.r u v ^ 2)| = 0 := by simp [hr]
      rw [hz]
      positivity
  have hA : 0 ≤ 4 * (C + 8) * e ^ 2 * M ^ 2 * ε ^ 2 := by positivity
  have hout := Area.area_integral_le_of_pointwise hset hA F hb
  have hin := Area.area_integral_in_le_of_pointwise hset hA F hb
  have heq : 4 * (4 * (C + 8) * e ^ 2 * M ^ 2 * ε ^ 2) * (s / 2) ^ 2 =
      (16 * (C + 8)) * (|e| * (s / 2) * M) ^ 2 * ε ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs]
    ring
  exact ⟨by simpa only [heq] using hout, by simpa only [heq] using hin⟩

end EmcsfAcExtension.Local
