module

public import EmcsfAcExtension.Local.Broad.Setup

/-! # Explicit smallness at fixed finite characteristic variation

The numerical choices in internal project record (SMALL) are made after the geometric
box constants and the finite BV budget. Continuity then realizes these
choices on an axis neighborhood. No variation smallness is imposed.
-/

public section

open Set

namespace EmcsfAcExtension.Local.Broad

/-- Explicit numerical parameters for the local contraction. The universal
numbers are fixed; `K,L,e,M` are retained as parameters. In particular the
radius and scalar threshold may decrease when the finite budget grows. -/
theorem axis_contraction_parameters (K L e M : ℝ) (hK : 1 ≤ K) (hL : 0 ≤ L)
    (hM : 0 ≤ M) :
    ∃ ε R : ℝ, 0 < ε ∧ 0 < R ∧ ε ≤ 1 ∧ ε ^ 2 ≤ 1 / 2 ∧
      K * ε * (L + 1) ≤ 1 / 2 ∧ e ^ 2 * M ^ 2 * R ^ 2 ≤ 1 ∧
      K * (ε * L + e ^ 2 * M ^ 2 * R ^ 2) * (1 + K * ε * (L + 1)) < 1 := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hLp : 0 < L + 1 := by linarith
  let ε := 1 / (32 * K ^ 2 * (L + 1))
  let R := 1 / (32 * K * (1 + |e| * M))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hεeq : K * ε * (L + 1) = 1 / (32 * K) := by
    dsimp [ε]
    field_simp
  have hεK : K * ε * (L + 1) ≤ 1 / 32 := by
    rw [hεeq]
    apply (div_le_iff₀ (by positivity : 0 < 32 * K)).mpr
    linarith
  have hε1 : ε ≤ 1 / 32 := by
    calc
      ε = 1 * ε * 1 := by ring
      _ ≤ K * ε * (L + 1) := by gcongr; linarith
      _ ≤ _ := hεK
  have hεL : K * ε * L ≤ 1 / 32 :=
    (mul_le_mul_of_nonneg_left (show L ≤ L + 1 by linarith) (mul_nonneg hK0.le hε.le)).trans hεK
  have hReq : (32 * K * (1 + |e| * M)) * R = 1 := by
    dsimp [R]
    field_simp
  have hcharge : |e| * M * R ≤ 1 / (32 * K) := by
    apply (le_div_iff₀ (by positivity : 0 < 32 * K)).mpr
    have hh := mul_nonneg (by positivity : 0 ≤ 32 * K) hR.le
    nlinarith only [hReq, hh]
  have hKcharge : K * (e ^ 2 * M ^ 2 * R ^ 2) ≤ 1 / 32 := by
    have hcharge' : (|e| * M * R) * (32 * K) ≤ 1 :=
      (le_div_iff₀ (by positivity : 0 < 32 * K)).mp hcharge
    have hn : 0 ≤ |e| * M * R := by positivity
    have hmult := mul_nonneg hn (sub_nonneg.mpr hK)
    have hsmall : |e| * M * R ≤ 1 := by nlinarith only [hcharge', hmult]
    have hsq : (|e| * M * R) ^ 2 ≤ |e| * M * R := by nlinarith only [hn, hsmall]
    have hm := mul_le_mul_of_nonneg_left hsq hK0.le
    have hc : K * (|e| * M * R) ≤ 1 / 32 := by nlinarith only [hcharge']
    calc
      _ = K * (|e| * M * R) ^ 2 := by rw [mul_pow, mul_pow, sq_abs]
      _ ≤ K * (|e| * M * R) := hm
      _ ≤ _ := hc
  have hσ : 0 ≤ e ^ 2 * M ^ 2 * R ^ 2 := by positivity
  have hσmult := mul_nonneg hσ (sub_nonneg.mpr hK)
  have hσ1 : e ^ 2 * M ^ 2 * R ^ 2 ≤ 1 := by nlinarith only [hKcharge, hσmult]
  have hbase : K * (ε * L + e ^ 2 * M ^ 2 * R ^ 2) ≤ 1 / 16 := by
    nlinarith only [hεL, hKcharge]
  refine ⟨ε, R, hε, hR, hε1.trans (by norm_num), ?_, hεK.trans (by norm_num), hσ1, ?_⟩
  · have hsq := (sq_le_sq₀ hε.le (by norm_num : (0 : ℝ) ≤ 1 / 32)).mpr hε1
    norm_num at hsq
    linarith
  · have hbase0 : 0 ≤ K * (ε * L + e ^ 2 * M ^ 2 * R ^ 2) := by positivity
    have hp := mul_le_mul hbase (show 1 + K * ε * (L + 1) ≤ 33 / 32 by linarith)
      (by positivity : 0 ≤ 1 + K * ε * (L + 1)) (by norm_num : (0 : ℝ) ≤ 1 / 16)
    exact hp.trans_lt (by norm_num)

/-- [node restart-stab-broad-uniqueness#axis-contraction-smallness-choice]
At an existing axis point, every fixed finite nonnegative variation budget
admits a scalar threshold and a neighborhood satisfying all contraction
smallness conditions. The coefficient `K ≥ 1` is fixed first and can
dominate the finitely many box constants. The choice is uniform over the
two solutions on the chosen neighborhood, with their ordinary normalized
oscillations and both scalar ratios bounded by the same `ε`. -/
theorem axis_contraction_smallness_choice {e q K L M : ℝ} {S₁ S₂ : Fields}
    {D : Set (ℝ × ℝ)} (hS₁ : IsSolution e S₁ D) (hS₂ : IsSolution e S₂ D)
    (hq : (q, q) ∈ D) (hK : 1 ≤ K) (hL : 0 ≤ L) (hM : 0 ≤ M) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧ ε ≤ 1 ∧ ε ^ 2 ≤ 1 / 2 ∧
      K * ε * (L + 1) ≤ 1 / 2 ∧ e ^ 2 * M ^ 2 * δ ^ 2 ≤ 1 ∧
      K * (ε * L + e ^ 2 * M ^ 2 * δ ^ 2) * (1 + K * ε * (L + 1)) < 1 ∧
      ∀ S ∈ ({S₁, S₂} : Set Fields),
        (∀ p ∈ D ∩ triangle (q - δ) (q + δ),
          ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ ε ∧ ‖S.xi p.1 p.2 / S.nu p.1 p.2‖ ≤ ε) ∧
        (∀ p ∈ D ∩ triangle (q - δ) (q + δ),
          ∀ p' ∈ D ∩ triangle (q - δ) (q + δ),
            ‖S.a p.1 p.2 - S.a p'.1 p'.2‖ ≤ ε ∧ ‖S.b p.1 p.2 - S.b p'.1 p'.2‖ ≤ ε) := by
  obtain ⟨ε, R, hε, hR, hε1, hε2, hgeom, hσ, hcontr⟩ :=
    axis_contraction_parameters K L e M hK hL hM
  obtain ⟨δ₀, hδ₀, hsmall⟩ := axis_neighborhood_smallness_choice hS₁ hS₂ hq hε
  let δ := min δ₀ R
  have hδ : 0 < δ := lt_min hδ₀ hR
  have hδR : δ ≤ R := min_le_right _ _
  have hδ₀' : δ ≤ δ₀ := min_le_left _ _
  have hσle : e ^ 2 * M ^ 2 * δ ^ 2 ≤ e ^ 2 * M ^ 2 * R ^ 2 := by gcongr
  refine ⟨ε, δ, hε, hδ, hε1, hε2, hgeom, hσle.trans hσ, ?_, ?_⟩
  · apply lt_of_le_of_lt _ hcontr
    gcongr
  · intro S hS
    have hsub : D ∩ triangle (q - δ) (q + δ) ⊆ D ∩ triangle (q - δ₀) (q + δ₀) := by
      rintro p ⟨hpD, hp⟩
      exact ⟨hpD, by
        refine ⟨?_, hp.2.1, ?_⟩ <;> linarith [hp.1, hp.2.2]⟩
    exact ⟨fun p hp => (hsmall S hS).1 p (hsub hp),
      fun p hp p' hp' => (hsmall S hS).2 p (hsub hp) p' (hsub hp')⟩

/-- A finite nonnegative distance with a strict self-contraction is zero.
The coefficient is an explicit parameter, with no hidden choice. -/
theorem eq_zero_of_strict_self_contraction {d q : ℝ} (hd : 0 ≤ d) (hq : q < 1)
    (h : d ≤ q * d) : d = 0 := by
  by_contra hne
  have hp := mul_pos (sub_pos.mpr hq) (lt_of_le_of_ne hd (Ne.symm hne))
  nlinarith only [hp, h]

end EmcsfAcExtension.Local.Broad
