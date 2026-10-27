module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.DifferenceMomentsCloseOut
import EmcsfAcExtension.Local.Stability.FieldDifferenceRaw
import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux

/-! # Closed outgoing scalar field comparison

The axis comparison and radial scalar reconstruction give the field
estimate without multiplying the geometric difference by the scalar
background. Constants precede the pair and every solution parameter.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [node restart-stab-field-difference]
The outgoing normalized scalar and scalar field difference estimate,
charged_SF_new_version.tex:L5256–5284 and approved internal project record. The threshold and
constant
depend only on the fixed box and `A`, before the pair and all other
parameters, uniformly in the background and minimum radius. -/
theorem stab_field_difference (A : ℝ) (hA : 0 < A) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        supDist T S₁.a S₂.a + supDist T S₁.phi S₂.phi ≤
          ENNReal.ofReal (C * (dataDist h₁ h₂ T + (jDist T S₁ S₂).toReal +
            ε * (geomDist T S₁ S₂).toReal)) := by
  obtain ⟨η, C₀, hη, hC₀, hOut⟩ := stab_out_difference A hA
  let F := 2 + C₀ + 5120 * A
  have hF : 0 < F := by dsimp only [F]; positivity
  refine ⟨min η (1 / 12), 2 * F + C₀, lt_min hη (by norm_num), by positivity, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall
  let G := (geomDist T S₁ S₂).toReal
  let J := (jDist T S₁ S₂).toReal
  let H := J + ε * G
  let L := dataDist h₁ h₂ T + H
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hJ : 0 ≤ J := ENNReal.toReal_nonneg
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hΔ : ‖h₁ 0 - h₂ 0‖ ≤ dataDist h₁ h₂ T := by
    exact le_add_of_nonneg_right ENNReal.toReal_nonneg
  have hΔ0 : 0 ≤ dataDist h₁ h₂ T := (norm_nonneg _).trans hΔ
  have hH : 0 ≤ H := add_nonneg hJ (mul_nonneg hε0 hG)
  have hL : 0 ≤ L := add_nonneg hΔ0 hH
  have hHL : H ≤ L := le_add_of_nonneg_left hΔ0
  have heGL : ε * G ≤ L := (le_add_of_nonneg_left hJ).trans hHL
  have hbase : dataDist h₁ h₂ T + J ≤ L := by
    dsimp only [L, H]
    linarith only [mul_nonneg hε0 hG]
  have hσ : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hε : ε ^ 2 ≤ 1 / 4 := by
    have hb := ((le_add_of_nonneg_right hσ).trans hsmall).trans (min_le_right _ _)
    linarith only [hb]
  have hclosed := hOut T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hsmall.trans (min_le_left _ _))
  have hclosedSup := (le_add_of_nonneg_right bot_le).trans hclosed
  have hclosedHardy := (le_add_of_nonneg_left bot_le).trans hclosed
  have hJval : jDist T S₁ S₂ = ENNReal.ofReal J :=
    (ENNReal.ofReal_toReal (stab_jDist_ne_top h₁s h₂s)).symm
  have hPhi : ∀ u v : ℝ, (u, v) ∈ triangle 0 T →
      ENNReal.ofReal ‖S₁.phi u v - S₂.phi u v‖ ≤ ENNReal.ofReal (F * L) := by
    intro u v hp
    have hraw := stab_field_difference_raw h₁s h₂s hε hp.1 hp.2.1 hp.2.2
    have hh : (∫⁻ s in Icc u T, ENNReal.ofReal (S₁.lam u s / S₁.r u s *
        ‖S₁.theta u s / (S₁.lam u s : ℂ) - S₂.theta u s / (S₂.lam u s : ℂ)‖)) ≤
        ENNReal.ofReal (C₀ * H) :=
      (le_iSup₂_of_le u ⟨hp.1, hp.2.1.trans hp.2.2⟩ le_rfl).trans hclosedHardy
    apply (hraw.trans (add_le_add (add_le_add
      (add_le_add (ENNReal.ofReal_le_ofReal hΔ) (le_of_eq hJval)) hh) le_rfl)).trans
    repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hcH := mul_le_mul_of_nonneg_left hHL hC₀.le
    have hgL := mul_le_mul_of_nonneg_left heGL (show 0 ≤ 5120 * A by positivity)
    dsimp only [F]
    nlinarith only [hbase, hcH, hgL, hL]
  have hNorm : ∀ u v : ℝ, (u, v) ∈ triangle 0 T →
      ENNReal.ofReal ‖S₁.a u v - S₂.a u v‖ ≤ ENNReal.ofReal ((F + C₀) * L) := by
    intro u v hp
    have hx : ENNReal.ofReal ‖S₁.theta u v / (S₁.lam u v : ℂ) -
        S₂.theta u v / (S₂.lam u v : ℂ)‖ ≤ ENNReal.ofReal (C₀ * L) := by
      have hsup : ENNReal.ofReal ‖S₁.theta u v / (S₁.lam u v : ℂ) -
          S₂.theta u v / (S₂.lam u v : ℂ)‖ ≤
          supDist T (fun u v => S₁.theta u v / (S₁.lam u v : ℂ))
            (fun u v => S₂.theta u v / (S₂.lam u v : ℂ)) := by
        rw [ofReal_norm]
        exact le_iSup₂_of_le (u, v) hp le_rfl
      exact (hsup.trans hclosedSup).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hHL hC₀.le))
    have heq : S₁.a u v - S₂.a u v = (S₁.phi u v - S₂.phi u v) +
        (S₁.theta u v / (S₁.lam u v : ℂ) - S₂.theta u v / (S₂.lam u v : ℂ)) := by
      simp only [Fields.a]
      abel
    rw [heq]
    calc
      _ ≤ ENNReal.ofReal ‖S₁.phi u v - S₂.phi u v‖ +
          ENNReal.ofReal ‖S₁.theta u v / (S₁.lam u v : ℂ) -
            S₂.theta u v / (S₂.lam u v : ℂ)‖ := by
        rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (norm_add_le _ _)
      _ ≤ ENNReal.ofReal (F * L) + ENNReal.ofReal (C₀ * L) := add_le_add (hPhi u v hp) hx
      _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
  have hSupPhi : supDist T S₁.phi S₂.phi ≤ ENNReal.ofReal (F * L) := by
    apply iSup₂_le
    rintro ⟨u, v⟩ hp
    rw [← ofReal_norm]
    exact hPhi u v hp
  have hSupNorm : supDist T S₁.a S₂.a ≤ ENNReal.ofReal ((F + C₀) * L) := by
    apply iSup₂_le
    rintro ⟨u, v⟩ hp
    rw [← ofReal_norm]
    exact hNorm u v hp
  apply (add_le_add hSupNorm hSupPhi).trans_eq
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  dsimp only [L, H, J, G]
  ring

end EmcsfAcExtension.Local
