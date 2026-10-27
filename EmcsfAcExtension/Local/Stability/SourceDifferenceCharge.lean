module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Calculus.RelativeCharge
import EmcsfAcExtension.Local.Calculus.C1ToSolution2
import EmcsfAcExtension.Local.Stability.MainFinite
import EmcsfAcExtension.Local.Stability.MomentsSections

/-! # Charge factors used by the electromagnetic source comparison

The individual bound is radial integration of the oscillatory current.
The elementary normalized comparison separates the charge difference
from the relative radius difference, preserving the radius-square scale.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local.Stab

/-- Individual charge bound in the stability box. The coefficient `1/2`
is universal, independent of the coupling, domain, background and envelopes. -/
theorem em_charge_bound_from_setting {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) {u v : ℝ} (hp : (u, v) ∈ triangle 0 T) :
    |S.Q u v| ≤ |e| * M * ε * S.r u v ^ 2 / 2 := by
  apply oscillatory_charge_bound (hset.c1.toIsSolution hset.pos) hp.2.1
    (fun p hq => by
      rcases hq with ⟨rfl, hq⟩
      exact ⟨hp.1, hq.1, hq.2.trans hp.2.2⟩)
  · intro w hw
    exact (hset.box.2 (u, w) ⟨hp.1, hw.1, hw.2.trans hp.2.2⟩).2.2.2.2.2.2
  · intro w hw
    exact (le_add_of_nonneg_right (norm_nonneg _)).trans
      (hset.box.2 (u, w) ⟨hp.1, hw.1, hw.2.trans hp.2.2⟩).2.2.2.2.2.1

/-- Normalized charge comparison from charge and relative-radius bounds.
The constants are the explicit `D+3`, uniformly in all real parameters;
no division by a coupling, variation parameter, or comparison distance occurs. -/
theorem normalized_charge_difference_le {r₁ r₂ Q₁ Q₂ D E ε G H : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hE : 0 ≤ E) (hε : 0 ≤ ε) (hG : 0 ≤ G)
    (_hH : 0 ≤ H) (hδQ : |Q₁ - Q₂| / r₁ ^ 2 ≤ D * E * H)
    (hQ₂ : |Q₂| / r₂ ^ 2 ≤ E * ε / 2)
    (hδr : |r₁ - r₂| ≤ G * r₁) (hratio : r₂ ≤ 4 * r₁) (hεG : ε * G ≤ H) :
    |Q₁ / r₁ ^ 2 - Q₂ / r₂ ^ 2| ≤ (D + 3) * E * H := by
  have hr₁sq : 0 < r₁ ^ 2 := pow_pos hr₁ 2
  have hr₂sq : 0 < r₂ ^ 2 := pow_pos hr₂ 2
  have hdiffsq : |r₂ ^ 2 - r₁ ^ 2| ≤ 5 * G * r₁ ^ 2 := by
    calc
      _ = |r₁ - r₂| * (r₁ + r₂) := by
        rw [show r₂ ^ 2 - r₁ ^ 2 = -(r₁ - r₂) * (r₁ + r₂) by ring,
          abs_mul, abs_neg, abs_of_pos (add_pos hr₁ hr₂)]
      _ ≤ (G * r₁) * (5 * r₁) := by gcongr; linarith only [hratio]
      _ = _ := by ring
  have hrel : |r₂ ^ 2 / r₁ ^ 2 - 1| ≤ 5 * G := by
    rw [div_sub_one hr₁sq.ne', abs_div, abs_of_pos hr₁sq]
    exact (div_le_iff₀ hr₁sq).2 hdiffsq
  have heq : Q₁ / r₁ ^ 2 - Q₂ / r₂ ^ 2 =
      (Q₁ - Q₂) / r₁ ^ 2 + Q₂ / r₂ ^ 2 * (r₂ ^ 2 / r₁ ^ 2 - 1) := by
    field_simp
    ; ring
  rw [heq]
  calc
    _ ≤ |(Q₁ - Q₂) / r₁ ^ 2| + |Q₂ / r₂ ^ 2 * (r₂ ^ 2 / r₁ ^ 2 - 1)| := abs_add_le _ _
    _ ≤ D * E * H + (E * ε / 2) * (5 * G) := by
      rw [abs_mul, abs_div, abs_div, abs_of_pos hr₁sq, abs_of_pos hr₂sq]
      exact add_le_add hδQ (mul_le_mul hQ₂ hrel (abs_nonneg _) (by positivity))
    _ = D * E * H + (5 / 2 : ℝ) * E * (ε * G) := by ring
    _ ≤ D * E * H + 3 * E * H := by gcongr; norm_num
    _ = _ := by ring

/-- Radius-weighted charge-difference conclusion consumed from internal project record.
The fixed constant `C` precedes every pair parameter and the radius-square
weight is retained exactly as in charged_SF_new_version.tex:L5117–5119. -/
structure ChargeDifference (C e T ε M Δ₀ : ℝ) (S₁ S₂ : Fields) : Prop where
  /-- Off-axis charge difference in the common first radius. -/
  bound : ∀ p ∈ triangle 0 T, p.1 < p.2 →
    |S₁.Q p.1 p.2 - S₂.Q p.1 p.2| / S₁.r p.1 p.2 ^ 2 ≤
      C * |e| * (M * (jDist T S₁ S₂).toReal + ε * Δ₀ +
        M * ε * (geomDist T S₁ S₂).toReal)

/-- [internal]
 Normalized charge factors for the electromagnetic source comparison.
`C` depends only on the fixed charge comparison constant `D`, uniformly
in both solutions, coupling, triangle, background and derivative suprema. -/
theorem normalized_charge_factors_of_differences (D : ℝ) (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (T e ε M A : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      ChargeDifference D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      ∀ p ∈ triangle 0 T, p.1 < p.2 →
        |S₁.Q p.1 p.2 / S₁.r p.1 p.2 ^ 2| ≤ |e| * M * ε / 2 ∧
        |S₂.Q p.1 p.2 / S₂.r p.1 p.2 ^ 2| ≤ |e| * M * ε / 2 ∧
        |S₁.Q p.1 p.2 / S₁.r p.1 p.2 ^ 2 - S₂.Q p.1 p.2 / S₂.r p.1 p.2 ^ 2| ≤
          C * |e| * M * ((jDist T S₁ S₂).toReal + ε * (geomDist T S₁ S₂).toReal +
            ε * dataDist h₁ h₂ T / M) := by
  refine ⟨D + 3, by linarith only [hD], ?_⟩
  intro T e ε M A S₁ S₂ h₁ h₂ hset₁ hset₂ hcharge p hp hlt
  have hr₁ := hset₁.c1.r_pos p hp hlt
  have hr₂ := hset₂.c1.r_pos p hp hlt
  have hM : 0 < M := zero_lt_one.trans_le hset₂.box.1
  have hMne := hM.ne'
  have hε : 0 ≤ ε := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans
    (hset₂.box.2 p hp).2.2.2.2.2.1
  let E := |e| * M
  let G := (geomDist T S₁ S₂).toReal
  let H := (jDist T S₁ S₂).toReal + ε * G + ε * dataDist h₁ h₂ T / M
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hδ : 0 ≤ dataDist h₁ h₂ T := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hQ₁ : |S₁.Q p.1 p.2| / S₁.r p.1 p.2 ^ 2 ≤ E * ε / 2 := by
    apply (div_le_iff₀ (pow_pos hr₁ 2)).2
    convert em_charge_bound_from_setting hset₁ hp using 1; dsimp [E]; ring
  have hQ₂ : |S₂.Q p.1 p.2| / S₂.r p.1 p.2 ^ 2 ≤ E * ε / 2 := by
    apply (div_le_iff₀ (pow_pos hr₂ 2)).2
    convert em_charge_bound_from_setting hset₂ hp using 1; dsimp [E]; ring
  have hδQ : |S₁.Q p.1 p.2 - S₂.Q p.1 p.2| / S₁.r p.1 p.2 ^ 2 ≤ D * E * H := by
    apply (hcharge.bound p hp hlt).trans_eq
    dsimp [E, H, G]
    field_simp
    ; ring
  have hratio : S₂.r p.1 p.2 ≤ 4 * S₁.r p.1 p.2 := by
    have h₁ := (stab_radius_bounds hset₁ hp.1 hp.2.1 hp.2.2).1
    have h₂ := (stab_radius_bounds hset₂ hp.1 hp.2.1 hp.2.2).2
    linarith only [h₁, h₂]
  have hεG : ε * G ≤ H := by
    have hJ : 0 ≤ (jDist T S₁ S₂).toReal := ENNReal.toReal_nonneg
    have hterm : 0 ≤ ε * dataDist h₁ h₂ T / M := by positivity
    dsimp only [H]
    linarith only [hJ, hterm]
  constructor
  · simpa only [abs_div, abs_of_pos (pow_pos hr₁ 2), E] using hQ₁
  constructor
  · simpa only [abs_div, abs_of_pos (pow_pos hr₂ 2), E] using hQ₂
  · have hbound := normalized_charge_difference_le hr₁ hr₂ hE hε hG hH hδQ hQ₂
      (radius_difference_le_geomDist hset₁ hset₂ hp) hratio hεG
    simpa only [E, H, G, mul_assoc] using hbound

end EmcsfAcExtension.Local.Stab
