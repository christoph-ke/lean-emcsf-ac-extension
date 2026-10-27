module

public import EmcsfAcExtension.Frozen.IsSolution
public import EmcsfAcExtension.Local.Defs.Envelope

/-! # Distances for broad AC/BV comparison

The normalized distance in charged_SF_new_version.tex:L5611–5616 is taken on a complete
closed triangle. Its finiteness uses continuity, without derivative envelopes.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The outgoing scalar ratio is continuous in the frozen broad class,
because the outgoing expansion is strictly positive. -/
theorem IsSolution.cont_outgoing_ratio {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) : ContinuousOn
      (fun p : ℝ × ℝ => S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ)) D :=
  hS.cont_theta.div (continuous_ofReal.comp_continuousOn hS.cont_lam)
    (fun p hp => by exact_mod_cast (hS.lam_pos p hp).ne')

/-- The incoming scalar ratio is continuous in the frozen broad class,
because the incoming expansion is strictly negative. No incoming AC
regularity of the normalized trace is asserted. -/
theorem IsSolution.cont_incoming_ratio {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) : ContinuousOn
      (fun p : ℝ × ℝ => S.xi p.1 p.2 / (S.nu p.1 p.2 : ℂ)) D :=
  hS.cont_xi.div (continuous_ofReal.comp_continuousOn hS.cont_nu)
    (fun p hp => by exact_mod_cast (hS.nu_neg p hp).ne)

/-- The frozen normalized outgoing scalar is continuous wherever the frozen
solution is defined, since its real expansion is positive there. -/
theorem IsSolution.cont_a {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) : ContinuousOn (Function.uncurry S.a) D :=
  hS.cont_phi.add (hS.cont_theta.div
    (continuous_ofReal.comp_continuousOn hS.cont_lam) (fun p hp => by
      exact_mod_cast (hS.lam_pos p hp).ne'))

/-- The frozen normalized incoming scalar is continuous wherever the frozen
solution is defined, since its real expansion is negative there. -/
theorem IsSolution.cont_b {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) : ContinuousOn (Function.uncurry S.b) D :=
  hS.cont_phi.add (hS.cont_xi.div
    (continuous_ofReal.comp_continuousOn hS.cont_nu) (fun p hp => by
      exact_mod_cast (hS.nu_neg p hp).ne))

namespace Broad

/-- [def-node restart-stab-broad-uniqueness#normalized-field-distance]
`D = ‖δa‖∞ + ‖δb‖∞` on the complete triangle with arbitrary initial label.
The extended nonnegative codomain avoids assigning a finite value to an
unbounded supremum. No constants or regularity hypotheses enter the definition. -/
@[expose] noncomputable def normalized_field_distance (s t : ℝ) (S₁ S₂ : Fields) : ℝ≥0∞ :=
  (⨆ p ∈ triangle s t, ‖S₁.a p.1 p.2 - S₂.a p.1 p.2‖ₑ) +
    ⨆ p ∈ triangle s t, ‖S₁.b p.1 p.2 - S₂.b p.1 p.2‖ₑ

/-- The geometric distance of internal project record on a complete triangle with arbitrary
initial label. The radius quotient has the frozen zero-denominator convention
at the axis. This extends `geomDist` by allowing a translated initial label. -/
@[expose] noncomputable def geometry_distance (s t : ℝ) (S₁ S₂ : Fields) : ℝ≥0∞ :=
  ⨆ p ∈ triangle s t, ENNReal.ofReal (|S₁.lam p.1 p.2 - S₂.lam p.1 p.2| +
    |S₁.nu p.1 p.2 - S₂.nu p.1 p.2| + |S₁.r p.1 p.2 - S₂.r p.1 p.2| / S₁.r p.1 p.2)

private theorem uniform_distance_ne_top {E : Type*} [NormedAddCommGroup E]
    {s t : ℝ} {f g : ℝ → ℝ → E}
    (hf : ContinuousOn (Function.uncurry f) (triangle s t))
    (hg : ContinuousOn (Function.uncurry g) (triangle s t)) :
    (⨆ p ∈ triangle s t, ‖f p.1 p.2 - g p.1 p.2‖ₑ) ≠ ⊤ := by
  obtain ⟨C, hC⟩ := (isCompact_triangle s t).bddAbove_image (hf.sub hg).norm
  apply ne_top_of_le_ne_top (show ENNReal.ofReal C ≠ ⊤ from ENNReal.ofReal_ne_top)
  apply iSup₂_le
  intro p hp
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hC (mem_image_of_mem _ hp))

/-- The normalized distance is finite for two frozen solutions on a compact
triangle. In particular all later real-valued absorptions use finite numbers. -/
theorem normalized_field_distance_ne_top {s t e : ℝ} {S₁ S₂ : Fields}
    (hS₁ : IsSolution e S₁ (triangle s t)) (hS₂ : IsSolution e S₂ (triangle s t)) :
    normalized_field_distance s t S₁ S₂ ≠ ⊤ :=
  ENNReal.add_ne_top.mpr ⟨uniform_distance_ne_top (IsSolution.cont_a hS₁) (IsSolution.cont_a hS₂),
    uniform_distance_ne_top (IsSolution.cont_b hS₁) (IsSolution.cont_b hS₂)⟩

/-- Each outgoing normalized difference is bounded by the finite real distance. -/
theorem norm_a_sub_le_distance {s t e u v : ℝ} {S₁ S₂ : Fields}
    (hS₁ : IsSolution e S₁ (triangle s t)) (hS₂ : IsSolution e S₂ (triangle s t))
    (hp : (u, v) ∈ triangle s t) :
    ‖S₁.a u v - S₂.a u v‖ ≤ (normalized_field_distance s t S₁ S₂).toReal := by
  apply (ENNReal.ofReal_le_iff_le_toReal (normalized_field_distance_ne_top hS₁ hS₂)).mp
  rw [ofReal_norm]
  calc
    _ ≤ ⨆ p ∈ triangle s t, ‖S₁.a p.1 p.2 - S₂.a p.1 p.2‖ₑ :=
      le_iSup₂_of_le (u, v) hp le_rfl
    _ ≤ _ := le_self_add

/-- Each incoming normalized difference is bounded by the finite real distance. -/
theorem norm_b_sub_le_distance {s t e u v : ℝ} {S₁ S₂ : Fields}
    (hS₁ : IsSolution e S₁ (triangle s t)) (hS₂ : IsSolution e S₂ (triangle s t))
    (hp : (u, v) ∈ triangle s t) :
    ‖S₁.b u v - S₂.b u v‖ ≤ (normalized_field_distance s t S₁ S₂).toReal := by
  apply (ENNReal.ofReal_le_iff_le_toReal (normalized_field_distance_ne_top hS₁ hS₂)).mp
  rw [ofReal_norm]
  calc
    _ ≤ ⨆ p ∈ triangle s t, ‖S₁.b p.1 p.2 - S₂.b p.1 p.2‖ₑ :=
      le_iSup₂_of_le (u, v) hp le_rfl
    _ ≤ _ := le_add_self

private theorem small_axis_triangle {E : Type*} [NormedAddCommGroup E]
    {D : Set (ℝ × ℝ)} {f : ℝ × ℝ → E} {q ε : ℝ}
    (hf : ContinuousOn f D) (hq : (q, q) ∈ D) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ D ∩ triangle (q - δ) (q + δ),
      ‖f p - f (q, q)‖ ≤ ε := by
  obtain ⟨r, hr, hbound⟩ := Metric.continuousWithinAt_iff.mp (hf _ hq) ε hε
  refine ⟨r / 2, half_pos hr, ?_⟩
  rintro ⟨x, y⟩ ⟨hp, hlo, hxy, hhi⟩
  apply le_of_lt
  rw [← dist_eq_norm]
  apply hbound hp
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff]
  constructor <;> rw [abs_lt] <;> constructor <;> linarith

private theorem norm_sub_le_center (x y z : ℂ) :
    ‖x - y‖ ≤ ‖x - z‖ + ‖y - z‖ := by
  simpa only [norm_sub_rev z y] using norm_sub_le_norm_sub_add_norm_sub x z y

/-- Fix the finite characteristic BV budget on a parent compact set before
choosing any smaller axis neighborhood. The single bound controls both
solutions and all outgoing `a` and incoming `b` sections in that set, and hence
in every subset. Its scope is the pair of solutions and the fixed compact set;
it is independent of the later smallness parameter and neighborhood. -/
theorem fixed_characteristic_bv_bound {e : ℝ} {S₁ S₂ : Fields} {D K : Set (ℝ × ℝ)}
    (hS₁ : IsSolution e S₁ D) (hS₂ : IsSolution e S₂ D)
    (hKD : K ⊆ D) (hK : IsCompact K) :
    ∃ L : ℝ≥0∞, L < ⊤ ∧ ∀ S ∈ ({S₁, S₂} : Set Fields),
      (∀ u a b, outSeg u a b ⊆ K → eVariationOn (S.a u) (Icc a b) ≤ L) ∧
      (∀ a b v, inSeg a b v ⊆ K → eVariationOn (fun u => S.b u v) (Icc a b) ≤ L) := by
  obtain ⟨B₁, hB₁, ho₁, hi₁⟩ := hS₁.bv_loc K hKD hK
  obtain ⟨B₂, hB₂, ho₂, hi₂⟩ := hS₂.bv_loc K hKD hK
  refine ⟨max B₁ B₂, max_lt hB₁ hB₂, ?_⟩
  intro S hS
  rcases Set.mem_insert_iff.mp hS with rfl | hS
  · exact ⟨fun u a b hs => ((ho₁ u a b hs).2.2.1).trans (le_max_left _ _),
      fun a b v hs => ((hi₁ a b v hs).2.2.2).trans (le_max_left _ _)⟩
  · have : S = S₂ := Set.mem_singleton_iff.mp hS
    subst S
    exact ⟨fun u a b hs => ((ho₂ u a b hs).2.2.1).trans (le_max_right _ _),
      fun a b v hs => ((hi₂ a b v hs).2.2.2).trans (le_max_right _ _)⟩

/-- [node restart-stab-broad-uniqueness#axis-neighborhood-smallness-choice]
Continuity at an existing regular axis point permits arbitrarily small ratios
and normalized-field oscillations for both frozen solutions. The neighborhood
is relative to the common domain; no domain-shape or extension assumption is
introduced. A characteristic BV bound fixed on a parent compact set is unchanged
by this restriction. There is no estimate constant. -/
theorem axis_neighborhood_smallness_choice {e q : ℝ} {S₁ S₂ : Fields}
    {D : Set (ℝ × ℝ)} (hS₁ : IsSolution e S₁ D) (hS₂ : IsSolution e S₂ D)
    (hq : (q, q) ∈ D) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ S ∈ ({S₁, S₂} : Set Fields),
      (∀ p ∈ D ∩ triangle (q - δ) (q + δ),
        ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ ε ∧
        ‖S.xi p.1 p.2 / S.nu p.1 p.2‖ ≤ ε) ∧
      (∀ p ∈ D ∩ triangle (q - δ) (q + δ),
        ∀ p' ∈ D ∩ triangle (q - δ) (q + δ),
          ‖S.a p.1 p.2 - S.a p'.1 p'.2‖ ≤ ε ∧
          ‖S.b p.1 p.2 - S.b p'.1 p'.2‖ ≤ ε) := by
  have one {S : Fields} (hS : IsSolution e S D) :
      ∃ δ : ℝ, 0 < δ ∧
        (∀ p ∈ D ∩ triangle (q - δ) (q + δ),
          ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ ε ∧
          ‖S.xi p.1 p.2 / S.nu p.1 p.2‖ ≤ ε) ∧
        (∀ p ∈ D ∩ triangle (q - δ) (q + δ),
          ∀ p' ∈ D ∩ triangle (q - δ) (q + δ),
            ‖S.a p.1 p.2 - S.a p'.1 p'.2‖ ≤ ε ∧
            ‖S.b p.1 p.2 - S.b p'.1 p'.2‖ ≤ ε) := by
    obtain ⟨da, hda, ha⟩ := small_axis_triangle (IsSolution.cont_a hS) hq (half_pos hε)
    obtain ⟨db, hdb, hb⟩ := small_axis_triangle (IsSolution.cont_b hS) hq (half_pos hε)
    obtain ⟨df, hdf, hf⟩ := small_axis_triangle hS.cont_phi hq (half_pos hε)
    simp only [Function.uncurry_def] at ha hb hf
    let δ := min da (min db df)
    have sub (d : ℝ) (hd : δ ≤ d) :
        D ∩ triangle (q - δ) (q + δ) ⊆ D ∩ triangle (q - d) (q + d) := by
      rintro p ⟨hp, hlo, hmid, hhi⟩
      exact ⟨hp, by linarith, hmid, by linarith⟩
    have ha' p hp := ha p (sub da (min_le_left _ _) hp)
    have hb' p hp := hb p (sub db ((min_le_right _ _).trans (min_le_left _ _)) hp)
    have hf' p hp := hf p (sub df ((min_le_right _ _).trans (min_le_right _ _)) hp)
    have haxis := hS.axis q hq
    refine ⟨δ, lt_min hda (lt_min hdb hdf), ?_, ?_⟩
    · intro p hp
      have hfa := hf' p hp
      have hpa := ha' p hp
      have hpb := hb' p hp
      rw [haxis.2.2.2.2.1] at hpa
      rw [haxis.2.2.2.2.2] at hpb
      constructor
      · calc
          ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ = ‖S.a p.1 p.2 - S.phi p.1 p.2‖ := by
            simp only [Fields.a, add_sub_cancel_left]
          _ ≤ ‖S.a p.1 p.2 - S.phi q q‖ + ‖S.phi p.1 p.2 - S.phi q q‖ :=
            norm_sub_le_center _ _ _
          _ ≤ ε := by linarith
      · calc
          ‖S.xi p.1 p.2 / S.nu p.1 p.2‖ = ‖S.b p.1 p.2 - S.phi p.1 p.2‖ := by
            simp only [Fields.b, add_sub_cancel_left]
          _ ≤ ‖S.b p.1 p.2 - S.phi q q‖ + ‖S.phi p.1 p.2 - S.phi q q‖ :=
            norm_sub_le_center _ _ _
          _ ≤ ε := by linarith
    · intro p hp p' hp'
      constructor
      · exact (norm_sub_le_center _ _ (S.a q q)).trans
          (by linarith [ha' p hp, ha' p' hp'])
      · exact (norm_sub_le_center _ _ (S.b q q)).trans
          (by linarith [hb' p hp, hb' p' hp'])
  obtain ⟨d₁, hd₁, h₁, ho₁⟩ := one hS₁
  obtain ⟨d₂, hd₂, h₂, ho₂⟩ := one hS₂
  have sub (d : ℝ) (hd : min d₁ d₂ ≤ d) :
      D ∩ triangle (q - min d₁ d₂) (q + min d₁ d₂) ⊆
        D ∩ triangle (q - d) (q + d) := by
    rintro p ⟨hp, hlo, hmid, hhi⟩
    exact ⟨hp, by linarith, hmid, by linarith⟩
  refine ⟨min d₁ d₂, lt_min hd₁ hd₂, ?_⟩
  intro S hS
  rcases Set.mem_insert_iff.mp hS with rfl | hS
  · exact ⟨fun p hp => h₁ p (sub _ (min_le_left _ _) hp),
      fun p hp p' hp' => ho₁ p (sub _ (min_le_left _ _) hp) p' (sub _ (min_le_left _ _) hp')⟩
  · have : S = S₂ := Set.mem_singleton_iff.mp hS
    subst S
    exact ⟨fun p hp => h₂ p (sub _ (min_le_right _ _) hp),
      fun p hp p' hp' => ho₂ p (sub _ (min_le_right _ _) hp) p' (sub _ (min_le_right _ _) hp')⟩

end Broad
end EmcsfAcExtension.Local
