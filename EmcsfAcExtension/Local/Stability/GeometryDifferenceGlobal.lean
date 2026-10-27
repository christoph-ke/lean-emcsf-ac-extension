module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeometryDifferenceOpticalBounds
import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux

/-! # Geometry comparison after the ordered optical integrations

The first optical integration controls `λ`, including its axis trace.
The second then controls `ν`. Integrating `λ` controls the relative
radius difference with no loss at the axis.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- Four raw optical budgets control the full geometric distance with
universal coefficient `100`. This conditional assembly assumes only
the displayed mass, initial optical and two exponent bounds, and
does not assume a geometric or stability conclusion bundle. -/
theorem stab_geometry_le_of_optical_bounds
    {e T ε M A U I Fo Fi : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂)
    (hU : 0 ≤ U) (hI : 0 ≤ I) (hFo : 0 ≤ Fo) (hFi : 0 ≤ Fi)
    (hMass : ∀ u v, 0 ≤ u → u ≤ v → v ≤ T → |S₁.mu u v - S₂.mu u v| ≤ U)
    (hInitial : ∀ v ∈ Icc 0 T,
      |S₁.lam 0 v / (1 - S₁.mu 0 v) - S₂.lam 0 v / (1 - S₂.mu 0 v)| ≤ I)
    (hOut : ∀ u v, 0 ≤ u → u ≤ v → v ≤ T →
      |(∫ s in u..v, S₁.lam u s / S₁.r u s * ‖S₁.theta u s / (S₁.lam u s : ℂ)‖ ^ 2) -
        ∫ s in u..v, S₂.lam u s / S₂.r u s * ‖S₂.theta u s / (S₂.lam u s : ℂ)‖ ^ 2| ≤ Fo)
    (hIn : ∀ u v, 0 ≤ u → u ≤ v → v ≤ T →
      |(∫ s in 0..u, -S₁.nu s v / S₁.r s v * ‖S₁.xi s v / (S₁.nu s v : ℂ)‖ ^ 2) -
        ∫ s in 0..u, -S₂.nu s v / S₂.r s v * ‖S₂.xi s v / (S₂.nu s v : ℂ)‖ ^ 2| ≤ Fi) :
    (geomDist T S₁ S₂).toReal ≤ 100 * (U + I + Fo + Fi) := by
  let L := 4 * U + I + 4 * Fi
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hLam : ∀ u v, 0 ≤ u → u ≤ v → v ≤ T → |S₁.lam u v - S₂.lam u v| ≤ L := by
    intro u v hu huv hvT
    have hh := stab_lam_sub_le_of_optical_integrals h₁s h₂s hu huv hvT
    have hm := hMass u v hu huv hvT
    have hi := hInitial v ⟨hu.trans huv, hvT⟩
    have hf := hIn u v hu huv hvT
    dsimp only [L]
    linarith only [hh, hm, hi, hf]
  have hNu : ∀ u v, 0 ≤ u → u ≤ v → v ≤ T →
      |S₁.nu u v - S₂.nu u v| ≤ 16 * U + 16 * L + 16 * Fo := by
    intro u v hu huv hvT
    have hh := stab_nu_sub_le_of_optical_integrals h₁s h₂s hu huv hvT
    have hm := hMass u v hu huv hvT
    have hl := hLam u u hu le_rfl (huv.trans hvT)
    have hf := hOut u v hu huv hvT
    linarith only [hh, hm, hl, hf]
  have hRadius : ∀ u v, 0 ≤ u → u ≤ v → v ≤ T →
      |S₁.r u v - S₂.r u v| / S₁.r u v ≤ 4 * L := by
    intro u v hu huv hvT
    rcases huv.eq_or_lt with rfl | huv
    · simp only [(h₁s.c1.axis u ⟨hu, le_rfl, hvT⟩).1, div_zero]
      positivity
    · have cL₁ : ContinuousOn (S₁.lam u) (Icc u v) := h₁s.c1.c1_lam.continuousOn.comp
        (continuous_const.prodMk continuous_id).continuousOn
        (fun s hs => ⟨hu, hs.1, hs.2.trans hvT⟩)
      have cL₂ : ContinuousOn (S₂.lam u) (Icc u v) := h₂s.c1.c1_lam.continuousOn.comp
        (continuous_const.prodMk continuous_id).continuousOn
        (fun s hs => ⟨hu, hs.1, hs.2.trans hvT⟩)
      have hi₁ := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv.le cL₁
      have hi₂ := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv.le cL₂
      have heq : S₁.r u v - S₂.r u v = ∫ s in u..v, S₁.lam u s - S₂.lam u s := by
        rw [intervalIntegral.integral_sub hi₁ hi₂,
          stab_radius_out_integral h₁s hu huv.le hvT, stab_radius_out_integral h₂s hu huv.le hvT]
      have hb : |S₁.r u v - S₂.r u v| ≤ L * (v - u) := by
        rw [heq, ← Real.norm_eq_abs]
        have hh := intervalIntegral.norm_integral_le_of_norm_le_const
          (a := u) (b := v) (C := L) (f := fun s => S₁.lam u s - S₂.lam u s) (fun s hs => by
          have hs' : s ∈ Icc u v := by
            simpa only [uIcc_of_le huv.le] using uIoc_subset_uIcc hs
          simpa only [Real.norm_eq_abs] using hLam u s hu hs'.1 (hs'.2.trans hvT))
        simpa only [abs_of_nonneg (sub_nonneg.mpr huv.le)] using hh
      have hr := h₁s.c1.r_pos (u, v) ⟨hu, huv.le, hvT⟩ huv
      rw [div_le_iff₀ hr]
      have hs := mul_le_mul_of_nonneg_left (stab_radius_bounds h₁s hu huv.le hvT).1
        (show 0 ≤ 4 * L by positivity)
      nlinarith only [hb, hs]
  have hGeom : geomDist T S₁ S₂ ≤ ENNReal.ofReal (100 * (U + I + Fo + Fi)) := by
    apply iSup₂_le
    rintro ⟨u, v⟩ hp
    apply ENNReal.ofReal_le_ofReal
    have hl := hLam u v hp.1 hp.2.1 hp.2.2
    have hn := hNu u v hp.1 hp.2.1 hp.2.2
    have hr := hRadius u v hp.1 hp.2.1 hp.2.2
    dsimp only [L] at hl hn hr
    linarith only [hl, hn, hr, hI, hFo, hFi]
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hGeom
  simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 100 * (U + I + Fo + Fi))] using hh

end EmcsfAcExtension.Local
