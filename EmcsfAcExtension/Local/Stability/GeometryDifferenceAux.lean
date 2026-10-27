module

public import EmcsfAcExtension.Local.Stability.MomentsSections
public import EmcsfAcExtension.Local.Api.Finite
public import EmcsfAcExtension.Local.Stability.GeometryDifferenceAlgebra
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Finite comparison distances and geometric coefficient bounds

The literal fixed box makes radii comparable and bounds the geometric
distance before any difference estimate is absorbed. In particular its
real value is used only after finiteness is proved. No graph node is
closed by these auxiliary facts.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

variable {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}

/-- Radii at common null labels are comparable with the universal factor
`4` supplied by the literal stability box, including their zero axis values. -/
theorem stab_radius_compare (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    S₁.r u v ≤ 4 * S₂.r u v ∧ S₂.r u v ≤ 4 * S₁.r u v := by
  have hr₁ := stab_radius_bounds h₁s hu huv hvT
  have hr₂ := stab_radius_bounds h₂s hu huv hvT
  constructor <;> linarith only [hr₁.1, hr₁.2, hr₂.1, hr₂.2]

/-- The common-label geometric distance is at most `7` in the fixed box.
This universal preliminary bound is independent of all solution parameters. -/
theorem stab_geomDist_le_seven (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) : geomDist T S₁ S₂ ≤ ENNReal.ofReal 7 := by
  apply iSup₂_le
  rintro ⟨u, v⟩ hp
  have hb₁ := h₁s.box.2 (u, v) hp
  have hb₂ := h₂s.box.2 (u, v) hp
  have hl : |S₁.lam u v - S₂.lam u v| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith only [hb₁.1, hb₁.2.1, hb₂.1, hb₂.2.1]
  have hn : |S₁.nu u v - S₂.nu u v| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith only [hb₁.2.2.1, hb₁.2.2.2.1, hb₂.2.2.1, hb₂.2.2.2.1]
  have hr : |S₁.r u v - S₂.r u v| / S₁.r u v ≤ 5 := by
    rcases eq_or_lt_of_le hp.2.1 with huv | huv
    · change u = v at huv
      subst v
      rw [(h₁s.c1.axis u hp).1, (h₂s.c1.axis u hp).1]
      norm_num
    · have hr₁ := h₁s.c1.r_pos (u, v) hp huv
      have hr₂ := h₂s.c1.r_pos (u, v) hp huv
      have hc := (stab_radius_compare h₁s h₂s hp.1 huv.le hp.2.2).2
      rw [div_le_iff₀ hr₁, abs_le]
      constructor <;> linarith only [hr₁, hr₂, hc]
  apply ENNReal.ofReal_le_ofReal
  linarith only [hl, hn, hr]

/-- Finiteness of the geometric distance follows directly from the box,
before the stability or geometric difference conclusions are available. -/
theorem stab_geomDist_ne_top (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) : geomDist T S₁ S₂ ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (stab_geomDist_le_seven h₁s h₂s)

/-- Each pointwise geometric sum is bounded by the real geometric distance.
The distance is proved finite from the box before taking its real value. -/
theorem stab_geom_sum_le (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) {u v : ℝ}
    (hp : (u, v) ∈ triangle 0 T) :
    |S₁.lam u v - S₂.lam u v| + |S₁.nu u v - S₂.nu u v| +
      |S₁.r u v - S₂.r u v| / S₁.r u v ≤ (geomDist T S₁ S₂).toReal := by
  have hr : 0 ≤ S₁.r u v := by
    rcases eq_or_lt_of_le hp.2.1 with heq | hlt
    · change u = v at heq
      subst v
      simpa only [(h₁s.c1.axis u hp).1] using (le_refl (0 : ℝ))
    · exact (h₁s.c1.r_pos (u, v) hp hlt).le
  have hnonneg : 0 ≤ |S₁.lam u v - S₂.lam u v| + |S₁.nu u v - S₂.nu u v| +
      |S₁.r u v - S₂.r u v| / S₁.r u v :=
    add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
      (div_nonneg (abs_nonneg _) hr)
  have hle : ENNReal.ofReal
      (|S₁.lam u v - S₂.lam u v| + |S₁.nu u v - S₂.nu u v| +
        |S₁.r u v - S₂.r u v| / S₁.r u v) ≤ geomDist T S₁ S₂ :=
    le_iSup₂_of_le (u, v) hp le_rfl
  simpa only [ENNReal.toReal_ofReal hnonneg] using
    ENNReal.toReal_mono (stab_geomDist_ne_top h₁s h₂s) hle

/-- The outgoing moving radial weight obeys the relative `20G` bound.
The coefficient `20` is universal; the geometric distance is finite
before its real value is used. -/
theorem stab_out_weight_sub_le (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    |S₁.lam u v / S₁.r u v - S₂.lam u v / S₂.r u v| ≤
      20 * (geomDist T S₁ S₂).toReal * (S₁.lam u v / S₁.r u v) := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hb₁ := h₁s.box.2 (u, v) hp
  have hb₂ := h₂s.box.2 (u, v) hp
  have hr₁ := h₁s.c1.r_pos (u, v) hp huv
  have hr₂ := h₂s.c1.r_pos (u, v) hp huv
  have hc := stab_geom_sum_le h₁s h₂s hp
  have hnonneg := div_nonneg (abs_nonneg (S₁.r u v - S₂.r u v)) hr₁.le
  apply stab_radial_weight_sub_le hb₁.1 (h₂s.c1.lam_pos (u, v) hp).le hb₂.2.1
    hr₁ hr₂ (stab_radius_compare h₁s h₂s hu huv.le hvT).1
  · linarith only [hc, hnonneg, abs_nonneg (S₁.nu u v - S₂.nu u v)]
  · linarith only [hc, abs_nonneg (S₁.lam u v - S₂.lam u v),
      abs_nonneg (S₁.nu u v - S₂.nu u v)]

/-- The incoming positively oriented radial weight has the same
universal `20G` relative difference bound at common labels. -/
theorem stab_in_weight_sub_le (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    |(-S₁.nu u v) / S₁.r u v - (-S₂.nu u v) / S₂.r u v| ≤
      20 * (geomDist T S₁ S₂).toReal * ((-S₁.nu u v) / S₁.r u v) := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hb₁ := h₁s.box.2 (u, v) hp
  have hb₂ := h₂s.box.2 (u, v) hp
  have hr₁ := h₁s.c1.r_pos (u, v) hp huv
  have hr₂ := h₂s.c1.r_pos (u, v) hp huv
  have hc := stab_geom_sum_le h₁s h₂s hp
  have hnonneg := div_nonneg (abs_nonneg (S₁.r u v - S₂.r u v)) hr₁.le
  apply stab_radial_weight_sub_le hb₁.2.2.1 (neg_nonneg.mpr
    (h₂s.c1.nu_neg (u, v) hp).le) hb₂.2.2.2.1
    hr₁ hr₂ (stab_radius_compare h₁s h₂s hu huv.le hvT).1
  · simp only [neg_sub_neg, abs_sub_comm]
    linarith only [hc, hnonneg, abs_nonneg (S₁.lam u v - S₂.lam u v)]
  · linarith only [hc, abs_nonneg (S₁.lam u v - S₂.lam u v),
      abs_nonneg (S₁.nu u v - S₂.nu u v)]

/-- The mass-ratio distance is finite by classical continuity at the axis.
This conclusion uses no mass difference estimate. -/
theorem stab_muDist_ne_top (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) : supDist T S₁.mu S₂.mu ≠ ⊤ :=
  supDist_ne_top_of_continuousOn (continuousOn_mu_aux h₁s.pos h₁s.c1)
    (continuousOn_mu_aux h₂s.pos h₂s.c1)

/-- A pointwise mass-ratio difference is bounded by its finite uniform
distance, without assuming any smallness or mass comparison conclusion. -/
theorem stab_mu_sub_le (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) {u v : ℝ}
    (hp : (u, v) ∈ triangle 0 T) :
    |S₁.mu u v - S₂.mu u v| ≤ (supDist T S₁.mu S₂.mu).toReal := by
  have hh : ‖S₁.mu u v - S₂.mu u v‖ₑ ≤ supDist T S₁.mu S₂.mu :=
    le_iSup₂_of_le (u, v) hp le_rfl
  rw [← ofReal_norm, Real.norm_eq_abs] at hh
  have hreal := ENNReal.toReal_mono (stab_muDist_ne_top h₁s h₂s) hh
  rw [ENNReal.toReal_ofReal (abs_nonneg _)] at hreal
  exact hreal

/-- The outgoing derivative distance is finite on the classical triangle.
This is a regularity fact and uses no difference conclusion. -/
theorem stab_jDist_ne_top (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) : jDist T S₁ S₂ ≠ ⊤ := by
  exact outEnv_lintegral_ne_top_of_continuousOn
    ((continuousOn_jC1_aux h₁s.pos h₁s.c1).sub (continuousOn_jC1_aux h₂s.pos h₂s.c1))

/-- The incoming derivative distance is finite on the classical triangle,
with the same coupling in both covariant derivatives. -/
theorem stab_kDist_ne_top (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) : kDist e T S₁ S₂ ≠ ⊤ := by
  exact inEnv_lintegral_ne_top_of_continuousOn
    ((continuousOn_kC1_aux h₁s.pos h₁s.c1).sub (continuousOn_kC1_aux h₂s.pos h₂s.c1))

end EmcsfAcExtension.Local
