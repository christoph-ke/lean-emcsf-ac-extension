module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.MomentsFieldMeasurable
import EmcsfAcExtension.Local.Stability.MomentsSections

/-! # Finite derivative comparison distances

The independent envelope assumptions control both difference envelopes.
No continuity of j or k on the axis is required.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

/-- The outgoing derivative distance is finite for a pair in the standing
stability setting. This justifies subsequent real-valued comparison algebra. -/
theorem jDist_ne_top_of_settings {e T ε M A : ℝ} {S₁ S₂ : Fields}
    {h₁ h₂ : ℝ → ℂ} (hset₁ : StabSetting e T ε M A S₁ h₁)
    (hset₂ : StabSetting e T ε M A S₂ h₂) : jDist T S₁ S₂ ≠ ⊤ := by
  have hb : jDist T S₁ S₂ ≤
      (∫⁻ v in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S₁) v) +
        ∫⁻ v in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S₂) v := by
    calc
      _ ≤ ∫⁻ v in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S₁) v +
          outEnv 0 (jC1 (triangle 0 T) S₂) v := by
        apply lintegral_mono
        intro v
        apply iSup₂_le
        intro u hu
        exact (enorm_sub_le).trans (add_le_add
          (le_iSup₂_of_le u hu le_rfl) (le_iSup₂_of_le u hu le_rfl))
      _ = _ := lintegral_add_left' (stab_outEnv_aemeasurable hset₁) _
  have hfinite₁ : (∫⁻ v in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S₁) v) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((le_add_right le_rfl).trans hset₁.env)
  have hfinite₂ : (∫⁻ v in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S₂) v) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((le_add_right le_rfl).trans hset₂.env)
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hfinite₁, hfinite₂⟩) hb

/-- The incoming derivative distance is finite for a pair in the standing
stability setting. The two covariant derivatives use the same fixed gauge. -/
theorem kDist_ne_top_of_settings {e T ε M A : ℝ} {S₁ S₂ : Fields}
    {h₁ h₂ : ℝ → ℂ} (hset₁ : StabSetting e T ε M A S₁ h₁)
    (hset₂ : StabSetting e T ε M A S₂ h₂) : kDist e T S₁ S₂ ≠ ⊤ := by
  have hb : kDist e T S₁ S₂ ≤
      (∫⁻ u in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S₁) u) +
        ∫⁻ u in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S₂) u := by
    calc
      _ ≤ ∫⁻ u in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S₁) u +
          inEnv T (kC1 e (triangle 0 T) S₂) u := by
        apply lintegral_mono
        intro u
        apply iSup₂_le
        intro v hv
        exact (enorm_sub_le).trans (add_le_add
          (le_iSup₂_of_le v hv le_rfl) (le_iSup₂_of_le v hv le_rfl))
      _ = _ := lintegral_add_left' (stab_inEnv_aemeasurable hset₁) _
  have hfinite₁ : (∫⁻ u in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S₁) u) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((le_add_left le_rfl).trans hset₁.env)
  have hfinite₂ : (∫⁻ u in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S₂) u) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((le_add_left le_rfl).trans hset₂.env)
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hfinite₁, hfinite₂⟩) hb

/-- The geometric distance is finite for a pair in the fixed stability box.
The regular-axis radius identities control the apparent inverse-radius term. -/
theorem geomDist_ne_top_of_settings {e T ε M A : ℝ} {S₁ S₂ : Fields}
    {h₁ h₂ : ℝ → ℂ} (hset₁ : StabSetting e T ε M A S₁ h₁)
    (hset₂ : StabSetting e T ε M A S₂ h₂) : geomDist T S₁ S₂ ≠ ⊤ := by
  apply ne_top_of_le_ne_top (show ENNReal.ofReal 7 ≠ ⊤ from ENNReal.ofReal_ne_top)
  apply iSup₂_le
  intro p hp
  apply ENNReal.ofReal_le_ofReal
  have hb₁ := hset₁.box.2 p hp
  have hb₂ := hset₂.box.2 p hp
  have hl : |S₁.lam p.1 p.2 - S₂.lam p.1 p.2| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith only [hb₁.1, hb₁.2.1, hb₂.1, hb₂.2.1]
  have hn : |S₁.nu p.1 p.2 - S₂.nu p.1 p.2| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith only [hb₁.2.2.1, hb₁.2.2.2.1, hb₂.2.2.1, hb₂.2.2.2.1]
  have hr : |S₁.r p.1 p.2 - S₂.r p.1 p.2| / S₁.r p.1 p.2 ≤ 5 := by
    rcases hp.2.1.eq_or_lt with heq | hlt
    · have hr₁ := (hset₁.c1.axis p.1 ⟨hp.1, le_rfl, heq.trans_le hp.2.2⟩).1
      simp only [← heq, hr₁, div_zero]
      norm_num
    · have hr₁ := hset₁.c1.r_pos p hp hlt
      have hrb₁ := stab_radius_bounds hset₁ hp.1 hp.2.1 hp.2.2
      have hrb₂ := stab_radius_bounds hset₂ hp.1 hp.2.1 hp.2.2
      have hdelta : 0 ≤ p.2 - p.1 := sub_nonneg.mpr hp.2.1
      have hr₂ : 0 ≤ S₂.r p.1 p.2 :=
        (by positivity : 0 ≤ (p.2 - p.1) / 4).trans hrb₂.1
      apply (div_le_iff₀ hr₁).2
      have hdiff : |S₁.r p.1 p.2 - S₂.r p.1 p.2| ≤
          S₁.r p.1 p.2 + S₂.r p.1 p.2 := by
        simpa only [sub_zero, zero_sub, abs_neg, abs_of_pos hr₁, abs_of_nonneg hr₂] using
          (abs_sub_le (S₁.r p.1 p.2) 0 (S₂.r p.1 p.2))
      linarith only [hdiff, hrb₁.1, hrb₂.2]
  linarith only [hl, hn, hr]

/-- Each pointwise geometric component is bounded by the real geometric
comparison distance. Finiteness is proved from the two settings first. -/
theorem geomDist_pointwise_le_of_settings {e T ε M A : ℝ} {S₁ S₂ : Fields}
    {h₁ h₂ : ℝ → ℂ} (hset₁ : StabSetting e T ε M A S₁ h₁)
    (hset₂ : StabSetting e T ε M A S₂ h₂) {p : ℝ × ℝ} (hp : p ∈ triangle 0 T) :
    |S₁.lam p.1 p.2 - S₂.lam p.1 p.2| + |S₁.nu p.1 p.2 - S₂.nu p.1 p.2| +
      |S₁.r p.1 p.2 - S₂.r p.1 p.2| / S₁.r p.1 p.2 ≤ (geomDist T S₁ S₂).toReal := by
  apply (ENNReal.ofReal_le_iff_le_toReal (geomDist_ne_top_of_settings hset₁ hset₂)).mp
  exact le_iSup₂_of_le p hp le_rfl

/-- Relative radius comparison, including the axis. The real geometric
distance is used only after its finiteness has been proved from the settings. -/
theorem radius_difference_le_geomDist {e T ε M A : ℝ} {S₁ S₂ : Fields}
    {h₁ h₂ : ℝ → ℂ} (hset₁ : StabSetting e T ε M A S₁ h₁)
    (hset₂ : StabSetting e T ε M A S₂ h₂) {p : ℝ × ℝ} (hp : p ∈ triangle 0 T) :
    |S₁.r p.1 p.2 - S₂.r p.1 p.2| ≤ (geomDist T S₁ S₂).toReal * S₁.r p.1 p.2 := by
  rcases hp.2.1.eq_or_lt with heq | hlt
  · have hr₁ := (hset₁.c1.axis p.1 ⟨hp.1, le_rfl, heq.trans_le hp.2.2⟩).1
    have hr₂ := (hset₂.c1.axis p.1 ⟨hp.1, le_rfl, heq.trans_le hp.2.2⟩).1
    simp only [← heq, hr₁, hr₂, sub_self, abs_zero, mul_zero, le_refl]
  · have hr := hset₁.c1.r_pos p hp hlt
    have hg := geomDist_pointwise_le_of_settings hset₁ hset₂ hp
    apply (div_le_iff₀ hr).mp
    linarith only [hg, abs_nonneg (S₁.lam p.1 p.2 - S₂.lam p.1 p.2),
      abs_nonneg (S₁.nu p.1 p.2 - S₂.nu p.1 p.2)]

end EmcsfAcExtension.Local.Stab
