module

public import EmcsfAcExtension.Local.Broad.Contraction
public import EmcsfAcExtension.Local.Broad.AxisUniquenessBox
public import EmcsfAcExtension.Local.Broad.AxisUniquenessFields
public import EmcsfAcExtension.Local.Broad.AxisUniquenessSmallness
public import EmcsfAcExtension.Local.Api.Mono

/-! # Axis uniqueness with the parent compact domain fixed first

The finite characteristic BV budget and geometric box are fixed on the
parent compact domain before the contraction neighborhood is reduced.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

open Broad

/-- Local axis uniqueness relative to a fixed compact parent domain.
The neighborhood depends on the two solutions and that parent, including
its finite BV budget. No quantitative constant is asserted uniformly in
that budget, and neither derivative envelopes nor incoming AC are used. -/
theorem broad_local_axis_uniqueness_of_compact {e q : ℝ} {S₁ S₂ : Fields}
    {D : Set (ℝ × ℝ)} (hS₁ : IsSolution e S₁ D) (hS₂ : IsSolution e S₂ D)
    (hD : IsCompact D) (hq : (q, q) ∈ D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ s : ℝ, q - η ≤ s → s ≤ q → triangle s (q + η) ⊆ D →
      (∀ v ∈ Icc s (q + η), S₁.r s v = S₂.r s v ∧ S₁.a s v = S₂.a s v) →
      (∀ u ∈ Icc s (q + η), S₁.A u u = 0 ∧ S₂.A u u = 0) →
      S₁.EqOn S₂ (triangle s (q + η)) := by
  obtain ⟨c, C, M, hc, hC, hM, hbox⟩ := compact_solution_box hS₁ hS₂ hD ⟨(q, q), hq⟩
  obtain ⟨L, hL, hvar⟩ := fixed_characteristic_bv_bound hS₁ hS₂ (Subset.refl D) hD
  have hLfin : L ≠ ⊤ := hL.ne
  have hLreal : 0 ≤ L.toReal := ENNReal.toReal_nonneg
  obtain ⟨KD, hKD, hcontr⟩ := normalized_distance_contraction c C hc hC
  obtain ⟨KG, hKG, hgeom⟩ := stab_broad_geometry_absorbed c C hc hC
  let K := KD + KG + 1
  have hKD0 : 0 < KD := zero_lt_one.trans_le hKD
  have hK : 1 ≤ K := by dsimp [K]; linarith
  have hDK : KD ≤ K := by dsimp [K]; linarith
  have hGK : KG ≤ K := by dsimp [K]; linarith
  obtain ⟨ε, δ, hε, hδ, hε1, hε2, habs, hσ, hstrict, hsmall⟩ :=
    axis_contraction_smallness_choice hS₁ hS₂ hq hK hLreal (zero_le_one.trans hM)
  refine ⟨δ, hδ, ?_⟩
  intro η hη hηδ s hs hsq hsub hdata haxis
  have hst : s < q + η := by linarith
  have ht₁ := isSolution_mono hS₁ hsub
  have ht₂ := isSolution_mono hS₂ hsub
  have hsmallsub : triangle s (q + η) ⊆ D ∩ triangle (q - δ) (q + δ) := by
    intro p hp
    exact ⟨hsub hp, by linarith [hp.1], hp.2.1, by linarith [hp.2.2]⟩
  have hbox' : ∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s (q + η),
      c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C ∧ c ≤ -S.nu p.1 p.2 ∧
      -S.nu p.1 p.2 ≤ C ∧ c ≤ 1 - S.mu p.1 p.2 ∧ ‖S.phi p.1 p.2‖ ≤ M ∧
      ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ ε ∧ ‖S.xi p.1 p.2 / S.nu p.1 p.2‖ ≤ ε := by
    intro S hm p hp
    rcases hbox S hm p (hsub hp) with ⟨hl, hl', hn, hn', hg, hφ⟩
    exact ⟨hl, hl', hn, hn', hg, hφ, (hsmall S hm).1 p (hsmallsub hp)⟩
  have hosc u v (hp : (u, v) ∈ triangle s (q + η)) (x : ℝ) (hx : x ∈ Icc u v)
      (y : ℝ) (hy : y ∈ Icc u v) : ‖S₂.a u x - S₂.a u y‖ ≤ ε :=
    ((hsmall S₂ (by simp)).2 (u, x)
      (hsmallsub ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩) (u, y)
      (hsmallsub ⟨hp.1, hy.1, hy.2.trans hp.2.2⟩)).1
  have hvo S (hm : S ∈ ({S₁, S₂} : Set Fields)) u v
      (hp : (u, v) ∈ triangle s (q + η)) :
      eVariationOn (S.a u) (Icc u v) ≤ ENNReal.ofReal L.toReal := by
    rw [ENNReal.ofReal_toReal hLfin]
    apply (hvar S hm).1 u u v
    rintro p ⟨rfl, hx⟩
    exact hsub ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩
  have hvi S (hm : S ∈ ({S₁, S₂} : Set Fields)) v (hv : v ∈ Icc s (q + η)) :
      eVariationOn (fun x => S.b x v) (Icc s v) ≤ ENNReal.ofReal L.toReal := by
    rw [ENNReal.ofReal_toReal hLfin]
    apply (hvar S hm).2 s v v
    rintro p ⟨hx, hy, rfl⟩
    exact hsub ⟨hx, hy, hv.2⟩
  have hA S (hm : S ∈ ({S₁, S₂} : Set Fields)) u (hu : u ∈ Icc s (q + η)) : S.A u u = 0 := by
    rcases Set.mem_insert_iff.mp hm with rfl | hm
    · exact (haxis u hu).1
    · have he : S = S₂ := Set.mem_singleton_iff.mp hm
      subst S
      exact (haxis u hu).2
  let σ := e ^ 2 * M ^ 2 * (((q + η) - s) / 2) ^ 2
  have hhalf0 : 0 ≤ ((q + η) - s) / 2 := by linarith
  have hhalf : ((q + η) - s) / 2 ≤ δ := by linarith
  have hσle : σ ≤ e ^ 2 * M ^ 2 * δ ^ 2 := by
    dsimp [σ]
    gcongr
  have hσ0 : 0 ≤ σ := by dsimp [σ]; positivity
  have habsD : KD * ε * (L.toReal + 1) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDK hε.le) (by positivity)).trans habs
  have hd := hcontr s (q + η) e M ε L.toReal S₁ S₂ hst ht₁ ht₂ hM hε.le hε1 hε2
    hLreal hbox' hosc hvo hvi hA hdata (hσle.trans hσ) habsD
  have hcoef : KD * (ε * L.toReal + σ) * (1 + KD * ε * (L.toReal + 1)) < 1 := by
    apply lt_of_le_of_lt _ hstrict
    gcongr
  have hdreal : (normalized_field_distance s (q + η) S₁ S₂).toReal = 0 :=
    eq_zero_of_strict_self_contraction ENNReal.toReal_nonneg hcoef hd
  have hd0 : normalized_field_distance s (q + η) S₁ S₂ = 0 := by
    rw [← ENNReal.ofReal_toReal (normalized_field_distance_ne_top ht₁ ht₂), hdreal,
      ENNReal.ofReal_zero]
  have habsG : KG * ε * (L.toReal + 1) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hGK hε.le) (by positivity)).trans habs
  have hg := hgeom s (q + η) e M ε L.toReal S₁ S₂ hst ht₁ ht₂ hM hε.le hε1 hε2
    hLreal hbox' hosc hvo hvi hA hdata (hσle.trans hσ) habsG
  rw [hdreal, mul_zero] at hg
  have hgreal : (geometry_distance s (q + η) S₁ S₂).toReal = 0 :=
    le_antisymm hg ENNReal.toReal_nonneg
  have hg0 : geometry_distance s (q + η) S₁ S₂ = 0 := by
    rw [← ENNReal.ofReal_toReal (geometry_distance_ne_top ht₁ ht₂ hc
      (fun p hp => (hbox' S₁ (by simp) p hp).1)), hgreal, ENNReal.ofReal_zero]
  exact remaining_fields_agree ht₁ ht₂ haxis hd0 hg0

end EmcsfAcExtension.Local
