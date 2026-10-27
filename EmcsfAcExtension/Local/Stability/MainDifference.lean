module

public import EmcsfAcExtension.Local.Stability.MainIncomingClosed
import EmcsfAcExtension.Local.Stability.MainIncoming
import EmcsfAcExtension.Local.Stability.MainFinite

/-! # Main Lipschitz comparison from the first-half difference records

The derivative and geometry norms are proved closed before the uniform
field estimates are recovered. No second-half closure conclusion is assumed.
-/

public section

open Set Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [internal]
 Conditional helper for `restart-stab-main-lipschitz`, charged_SF_new_version.tex:L5358–5370.
The threshold and constant depend only on fixed `A,D`, chosen before all
triangle, coupling, background, data and solution parameters. Inputs are
exactly the listed conclusions belonging to internal project record. Both approved datum
repairs are retained in the preceding estimates and absorbed in this proof. -/
theorem stab_main_lipschitz_of_differences (A D : ℝ) (hA : 0 < A) (hD : 0 < D) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
    ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      ε ^ 2 + sigma e M T ≤ η →
      Stab.RatioDifferences D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      Stab.FieldDifference D T ε (dataDist h₁ h₂ T) S₁ S₂ →
      Stab.ChargeDifference D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      Stab.PotentialDifference D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      Stab.IncomingFluxDifference D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      Stab.OutgoingFluxDifference D T ε S₁ S₂ →
      Stab.GeometryDifference D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      jDist T S₁ S₂ + kDist e T S₁ S₂ + geomDist T S₁ S₂ + supDist T S₁.a S₂.a +
        supDist T S₁.b S₂.b + supDist T S₁.phi S₂.phi ≤
          ENNReal.ofReal (C * dataDist h₁ h₂ T) := by
  obtain ⟨η₀, L, hη₀, hL, hclose⟩ := Stab.comparison_norms_of_differences A D hA hD
  obtain ⟨Cᵦ, hCᵦ, hb⟩ := Stab.incoming_normalized_field_comparison_of_closed_distances D L hD hL
  refine ⟨min η₀ 1, L + 2 * D * (L + 1) + Cᵦ, lt_min hη₀ zero_lt_one,
    by positivity, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ hset₁ hset₂ hsmall hratio hfield hcharge hpot hfi hfo hgeom
  have hε0 : 0 ≤ ε := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans
    (hset₂.box.2 (0, 0) ⟨le_rfl, le_rfl, hset₂.pos.le⟩).2.2.2.2.2.1
  have hσ0 : 0 ≤ sigma e M T := by unfold sigma; positivity
  have hq1 := hsmall.trans (min_le_right η₀ 1)
  have hε1 : ε ≤ 1 := by nlinarith only [hq1, hσ0, hε0]
  have hσ1 : sigma e M T ≤ 1 := by nlinarith only [hq1, sq_nonneg ε]
  let δ := dataDist h₁ h₂ T
  let J := (jDist T S₁ S₂).toReal
  let K := (kDist e T S₁ S₂).toReal
  let G := (geomDist T S₁ S₂).toReal
  have hδ : 0 ≤ δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hJ : 0 ≤ J := ENNReal.toReal_nonneg
  have hK : 0 ≤ K := ENNReal.toReal_nonneg
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hclosed : J + K + G ≤ L * δ :=
    hclose T e ε M S₁ S₂ h₁ h₂ hset₁ hset₂ (hsmall.trans (min_le_left η₀ 1))
      hratio hfield hcharge hpot hfi hfo hgeom
  have hscalar : δ + J + ε * G ≤ (L + 1) * δ := by
    have hεG := mul_le_mul_of_nonneg_right hε1 hG
    linarith only [hclosed, hεG, hK]
  have hpoint (p : ℝ × ℝ) (hp : p ∈ triangle 0 T) :
      ‖S₁.a p.1 p.2 - S₂.a p.1 p.2‖ + ‖S₁.phi p.1 p.2 - S₂.phi p.1 p.2‖ ≤
        D * (L + 1) * δ := by
    calc
      _ ≤ D * (δ + J + ε * G) := hfield.bound p hp
      _ ≤ D * ((L + 1) * δ) := mul_le_mul_of_nonneg_left hscalar hD.le
      _ = _ := by ring
  have ha : supDist T S₁.a S₂.a ≤ ENNReal.ofReal (D * (L + 1) * δ) := by
    apply iSup₂_le
    intro p hp
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal
      ((le_add_of_nonneg_right (norm_nonneg _)).trans (hpoint p hp))
  have hφ : supDist T S₁.phi S₂.phi ≤ ENNReal.ofReal (D * (L + 1) * δ) := by
    apply iSup₂_le
    intro p hp
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal
      ((le_add_of_nonneg_left (norm_nonneg _)).trans (hpoint p hp))
  have hb' := hb T e ε M A S₁ S₂ h₁ h₂ hset₁ hset₂ hε1 hσ1 hfield hratio hclosed
  have hjfin := Stab.jDist_ne_top_of_settings hset₁ hset₂
  have hkfin := Stab.kDist_ne_top_of_settings hset₁ hset₂
  have hgfin := Stab.geomDist_ne_top_of_settings hset₁ hset₂
  have hjkfin := ENNReal.add_ne_top.mpr ⟨hjfin, hkfin⟩
  have hsumfin := ENNReal.add_ne_top.mpr ⟨hjkfin, hgfin⟩
  have hsum : jDist T S₁ S₂ + kDist e T S₁ S₂ + geomDist T S₁ S₂ ≤
      ENNReal.ofReal (L * δ) := by
    apply (ENNReal.toReal_le_toReal hsumfin ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_add hjkfin hgfin, ENNReal.toReal_add hjfin hkfin,
      ENNReal.toReal_ofReal (mul_nonneg hL.le hδ)]
    exact hclosed
  calc
    _ ≤ ENNReal.ofReal (L * δ) + ENNReal.ofReal (D * (L + 1) * δ) +
        ENNReal.ofReal (Cᵦ * δ) + ENNReal.ofReal (D * (L + 1) * δ) :=
      add_le_add (add_le_add (add_le_add hsum ha) hb') hφ
    _ = ENNReal.ofReal (((L * δ + D * (L + 1) * δ) + Cᵦ * δ) + D * (L + 1) * δ) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity)]
    _ = _ := by congr 1; ring

end EmcsfAcExtension.Local
