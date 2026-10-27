module

public import EmcsfAcExtension.Local.Broad.ContractionOutgoing
public import EmcsfAcExtension.Local.Broad.ContractionIncoming
public import EmcsfAcExtension.Local.Broad.GeometryAbsorbed

/-! # The broad normalized-distance contraction

The incoming axis term is supplied by the outgoing comparison. The
geometric feedback is absorbed at the same fixed finite variation size.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Broad

/-- [node restart-stab-broad-uniqueness#D-contraction-inequality]
The normalized distance satisfies the strict-contraction inequality of
charged_SF_new_version.tex:L5902–5904 and internal project record (C). For each fixed `c,C`, the
constant is at least one and precedes all triangle, coupling, scalar,
variation and solution parameters. Only the displayed oscillation and
charged-scale conditions are smallness assumptions. -/
theorem normalized_distance_contraction (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (s t e M ε L : ℝ) (S₁ S₂ : Fields), s < t →
      IsSolution e S₁ (triangle s t) → IsSolution e S₂ (triangle s t) →
      1 ≤ M → 0 ≤ ε → ε ≤ 1 → ε ^ 2 ≤ 1 / 2 → 0 ≤ L →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s t,
        c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C ∧ c ≤ -S.nu p.1 p.2 ∧
        -S.nu p.1 p.2 ≤ C ∧ c ≤ 1 - S.mu p.1 p.2 ∧ ‖S.phi p.1 p.2‖ ≤ M ∧
        ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ ε ∧ ‖S.xi p.1 p.2 / S.nu p.1 p.2‖ ≤ ε) →
      (∀ u v, (u, v) ∈ triangle s t → ∀ x ∈ Icc u v, ∀ y ∈ Icc u v,
        ‖S₂.a u x - S₂.a u y‖ ≤ ε) →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ u v, (u, v) ∈ triangle s t →
        eVariationOn (S.a u) (Icc u v) ≤ ENNReal.ofReal L) →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ v ∈ Icc s t,
        eVariationOn (fun x => S.b x v) (Icc s v) ≤ ENNReal.ofReal L) →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ u ∈ Icc s t, S.A u u = 0) →
      (∀ v ∈ Icc s t, S₁.r s v = S₂.r s v ∧ S₁.a s v = S₂.a s v) →
      e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2 ≤ 1 →
      K * ε * (L + 1) ≤ 1 / 2 →
      (normalized_field_distance s t S₁ S₂).toReal ≤
        K * (ε * L + e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2) *
          (1 + K * ε * (L + 1)) * (normalized_field_distance s t S₁ S₂).toReal := by
  obtain ⟨Ka, hKa, hout⟩ := outgoing_scalar_contraction c C hc hC
  obtain ⟨Kb, hKb, hin⟩ := incoming_scalar_contraction c C hc hC
  obtain ⟨Kg, hKg, hgeom⟩ := Local.stab_broad_geometry_absorbed c C hc hC
  let K := 2 * Ka + Kb + Kg + 1
  have hKaK : 2 * Ka + Kb ≤ K := by dsimp [K]; linarith
  have hKgK : Kg ≤ K := by dsimp [K]; linarith
  refine ⟨K, by dsimp [K]; linarith, ?_⟩
  intro s t e M ε L S₁ S₂ hst hS₁ hS₂ hM hε hε1 hsmall hL hbox hosc hvo hvi haxis hdata hσ habs
  let d := (normalized_field_distance s t S₁ S₂).toReal
  let g := (geometry_distance s t S₁ S₂).toReal
  let E := d + ε * g
  let σ := e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2
  let B := (ε * L + σ) * E
  have hE : 0 ≤ E := by dsimp [E, d, g]; positivity
  have hB : 0 ≤ B := by dsimp [B, σ]; positivity
  have ha := hout s t e M ε L S₁ S₂ hS₁ hS₂ hM hε hε1 hsmall hL hbox hosc
    hvo hvi haxis hdata hσ
  have hb := hin s t e M ε L S₁ S₂ hS₁ hS₂ hM hε hε1 hsmall hL hbox hosc
    hvo hvi haxis hσ
  have hAsup : (⨆ p ∈ triangle s t, ‖S₁.a p.1 p.2 - S₂.a p.1 p.2‖ₑ) ≤
      ENNReal.ofReal (Ka * B) := by
    apply iSup₂_le
    intro p hp
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal ((ha p.1 p.2 hp).trans_eq (by dsimp [B, E, d, g, σ]; ring))
  have hBsup : (⨆ p ∈ triangle s t, ‖S₁.b p.1 p.2 - S₂.b p.1 p.2‖ₑ) ≤
      ENNReal.ofReal ((Ka + Kb) * B) := by
    apply iSup₂_le
    intro p hp
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    apply (hb p.1 p.2 hp).trans
    have hh := ha p.1 p.1 ⟨hp.1, le_rfl, hp.2.1.trans hp.2.2⟩
    apply (add_le_add hh le_rfl).trans_eq
    dsimp [B, E, d, g, σ]
    ring
  have hsum : normalized_field_distance s t S₁ S₂ ≤ ENNReal.ofReal ((2 * Ka + Kb) * B) := by
    apply (add_le_add hAsup hBsup).trans_eq
    rw [← ENNReal.ofReal_add (mul_nonneg hKa.le hB) (by positivity)]
    congr 1
    ring
  have hraw := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsum
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ (2 * Ka + Kb) * B)] at hraw
  have habs' : Kg * ε * (L + 1) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKgK hε) (by positivity)).trans habs
  have hg := hgeom s t e M ε L S₁ S₂ hst hS₁ hS₂ hM hε hε1 hsmall hL hbox hosc
    hvo hvi haxis hdata hσ habs'
  calc
    d ≤ (2 * Ka + Kb) * B := hraw
    _ ≤ K * B := mul_le_mul_of_nonneg_right hKaK hB
    _ = K * (ε * L + σ) * (d + ε * g) := by dsimp [B, E]; ring
    _ ≤ K * (ε * L + σ) * (d + ε * (Kg * (L + 1) * d)) := by gcongr
    _ ≤ K * (ε * L + σ) * (d + ε * (K * (L + 1) * d)) := by gcongr
    _ = _ := by dsimp [d, σ]; ring

end EmcsfAcExtension.Local.Broad
