module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Defs.C1Bound
public import EmcsfAcExtension.Local.Apriori.SmoothSupJetFields
import EmcsfAcExtension.Local.Apriori.SmoothSupJetIdentity
import EmcsfAcExtension.Local.Apriori.SmoothSupJetFieldProjection
import EmcsfAcExtension.Local.Apriori.SmoothSupC1
import EmcsfAcExtension.Local.Apriori.SmoothSupRadial
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Apriori.Mass

/-! # Closing the full first-jet bound

A fixed ball of regular numerical inputs bounds the first jets uniformly
before the solution and apex are chosen. The field identities identify
these numerical formulas off axis, and continuity supplies the axis.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local

/-- The regular numerical inputs have a common radius-dependent bound.
`L` depends only on the displayed budgets `R,M,D,G,H,P,Q,U`, before the
solution, datum, variation parameter and constructed apex. This conditional
helper is used by both the field and geometric-coefficient jet estimates. -/
theorem smooth_jet_input_bound_of_bounds {e s ε M R D G H P Q U L : ℝ}
    {S : Fields} {h : ℝ → ℂ} (hset : AprioriSetting e s ε M S h) (hsR : s ≤ R)
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hD : 0 ≤ D) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hU : 0 ≤ U)
    (hL : L = 1 + R + M + D + G + H + P + Q + U + 4)
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 s) (huv : u < v)
    (hscalar : ‖pdV (triangle 0 s) S.a u v‖ ≤ D ∧
      ‖pdU (triangle 0 s) S.b u v + I * e * S.A u v * S.b u v‖ ≤ D ∧
      ‖S.theta u v / S.lam u v‖ ≤ D * S.r u v ∧
      ‖S.xi u v / S.nu u v‖ ≤ D * S.r u v)
    (hexp : |pdU (triangle 0 s) S.lam u v| ≤ G ∧
      |pdV (triangle 0 s) S.lam u v| ≤ G ∧
      |pdU (triangle 0 s) S.nu u v| ≤ G ∧ |pdV (triangle 0 s) S.nu u v| ≤ G)
    (hpot : |S.A u v| ≤ P ∧ |pdU (triangle 0 s) S.A u v| ≤ H)
    (hcenter : |S.Q u v| ≤ Q * S.r u v ^ 3 ∧ S.mu u v ≤ U * S.r u v ^ 2) :
    ‖smoothJetInput e s S u v‖ ≤ L := by
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  have domR : R ≤ L := by rw [hL]; linarith only [hR, hM, hD, hG, hH, hP, hQ, hU]
  have domM : M ≤ L := by rw [hL]; linarith only [hR, hM, hD, hG, hH, hP, hQ, hU]
  have domD : D ≤ L := by rw [hL]; linarith only [hR, hM, hD, hG, hH, hP, hQ, hU]
  have domG : G ≤ L := by rw [hL]; linarith only [hR, hM, hD, hG, hH, hP, hQ, hU]
  have domH : H ≤ L := by rw [hL]; linarith only [hR, hM, hD, hG, hH, hP, hQ, hU]
  have domP : P ≤ L := by rw [hL]; linarith only [hR, hM, hD, hG, hH, hP, hQ, hU]
  have domQ : Q ≤ L := by rw [hL]; linarith only [hR, hM, hD, hG, hH, hP, hQ, hU]
  have domU : U ≤ L := by rw [hL]; linarith only [hR, hM, hD, hG, hH, hP, hQ, hU]
  have domfour : 4 ≤ L := by rw [hL]; linarith only [hR, hM, hD, hG, hH, hP, hQ, hU]
  have dom1 : (1 : ℝ) ≤ L := (by norm_num : (1 : ℝ) ≤ 4).trans domfour
  have hr := hset.c1.r_pos (u, v) hp huv
  have hrR : |S.r u v| ≤ R := by
    rw [abs_of_pos hr]
    exact ((smooth_radius_bounds_aux hset hp).2).trans
      (by linarith only [hp.1, hp.2.2, hsR])
  have hl := hset.c1.lam_pos (u, v) hp
  have hn := hset.c1.nu_neg (u, v) hp
  have hb := hset.box (u, v) hp
  have hl1 : |S.lam u v| ≤ 1 := by rw [abs_of_pos hl]; exact hb.2.1
  have hn1 : |S.nu u v| ≤ 1 := by rw [abs_of_neg hn]; exact hb.2.2.2.1
  have hμ0 := hset.mu_nonneg hp
  have hd0 := hset.c1.one_sub_mu_pos (u, v) hp
  have hd1 : |1 - S.mu u v| ≤ 1 := by
    rw [abs_of_pos hd0]
    linarith only [hμ0]
  have hqr : |S.Q u v / S.r u v ^ 3| ≤ Q := by
    rw [abs_div, abs_of_pos (pow_pos hr 3)]
    exact (div_le_iff₀ (pow_pos hr 3)).mpr hcenter.1
  have hmr : |S.mu u v / S.r u v ^ 2| ≤ U := by
    rw [abs_of_nonneg (div_nonneg hμ0 (sq_nonneg _))]
    exact (div_le_iff₀ (sq_pos_of_pos hr)).mpr hcenter.2
  have hinv {x : ℝ} (hx : 1 / 4 ≤ |x|) : |x⁻¹| ≤ 4 := by
    rw [abs_inv]
    have hh := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 4) hx
    norm_num at hh
    exact hh
  have hli : |(S.lam u v)⁻¹| ≤ 4 := hinv (by rw [abs_of_pos hl]; exact hb.1)
  have hni : |(S.nu u v)⁻¹| ≤ 4 := hinv (by rw [abs_of_neg hn]; exact hb.2.2.1)
  have hdi : |(1 - S.mu u v)⁻¹| ≤ 4 := hinv (by
    rw [abs_of_pos hd0]
    exact (by norm_num : (1 : ℝ) / 4 ≤ 1 / 2).trans hb.2.2.2.2.1)
  have hfr : ‖S.theta u v / S.lam u v / S.r u v‖ ≤ D := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact (div_le_iff₀ hr).mpr hscalar.2.2.1
  have hgr : ‖S.xi u v / S.nu u v / S.r u v‖ ≤ D := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact (div_le_iff₀ hr).mpr hscalar.2.2.2
  rw [Prod.norm_def]
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg hL0).mpr
    intro i
    fin_cases i <;>
      dsimp only [smoothJetInput, Matrix.cons_val_zero, Matrix.cons_val_succ]
    all_goals simp only [Real.norm_eq_abs]
    · exact hrR.trans domR
    · exact hl1.trans dom1
    · exact hn1.trans dom1
    · exact hd1.trans dom1
    · exact hqr.trans domQ
    · exact hmr.trans domU
    · exact hpot.1.trans domP
    · exact hexp.1.trans domG
    · exact hexp.2.1.trans domG
    · exact hexp.2.2.1.trans domG
    · exact hexp.2.2.2.trans domG
    · exact hpot.2.trans domH
    · exact hli.trans domfour
    · exact hni.trans domfour
    · exact hdi.trans domfour
  · apply (pi_norm_le_iff_of_nonneg hL0).mpr
    intro i
    fin_cases i <;>
      dsimp only [smoothJetInput, Matrix.cons_val_zero, Matrix.cons_val_succ]
    · exact hb.2.2.2.2.2.1.trans domM
    · exact hfr.trans domD
    · exact hgr.trans domD
    · exact hscalar.1.trans domD
    · exact hscalar.2.1.trans domD

/-- Assemble the full internal project record continuation bound from regular scalar,
expansion, potential and center budgets. The positive bound is chosen
after the displayed numerical controls and before the constructed apex,
variation parameter, solution and datum. The argument bounds a fixed
numerical ball; no per-solution compactness constant enters the result. -/
theorem smooth_c1_recovery_of_bounds (e R M D G H P Q U : ℝ)
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hD : 0 ≤ D) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hU : 0 ≤ U) :
    ∃ B : ℝ, 0 < B ∧ ∀ (s ε : ℝ) (S : Fields) (h : ℝ → ℂ), s ≤ R →
      AprioriSetting e s ε M S h →
      (∀ q ∈ triangle 0 s,
        ‖pdV (triangle 0 s) S.a q.1 q.2‖ ≤ D ∧
        ‖pdU (triangle 0 s) S.b q.1 q.2 + I * e * S.A q.1 q.2 * S.b q.1 q.2‖ ≤ D ∧
        ‖S.theta q.1 q.2 / S.lam q.1 q.2‖ ≤ D * S.r q.1 q.2 ∧
        ‖S.xi q.1 q.2 / S.nu q.1 q.2‖ ≤ D * S.r q.1 q.2) →
      (∀ q ∈ triangle 0 s,
        |pdU (triangle 0 s) S.lam q.1 q.2| ≤ G ∧
        |pdV (triangle 0 s) S.lam q.1 q.2| ≤ G ∧
        |pdU (triangle 0 s) S.nu q.1 q.2| ≤ G ∧
        |pdV (triangle 0 s) S.nu q.1 q.2| ≤ G) →
      (∀ q ∈ triangle 0 s, |S.A q.1 q.2| ≤ P ∧
        |pdU (triangle 0 s) S.A q.1 q.2| ≤ H) →
      (∀ q ∈ triangle 0 s, |S.Q q.1 q.2| ≤ Q * S.r q.1 q.2 ^ 3 ∧
        S.mu q.1 q.2 ≤ U * S.r q.1 q.2 ^ 2) → C1BoundOn S (triangle 0 s) B := by
  let L := 1 + R + M + D + G + H + P + Q + U + 4
  obtain ⟨A, hA, hformula⟩ := smooth_jet_formula_bound_aux e L
  refine ⟨4 + 2 * A, by positivity, ?_⟩
  intro s ε S h hsR hset hscalar hexp hpot hcenter
  have hoff (q : ℝ × ℝ) (hq : q ∈ triangle 0 s) (huv : q.1 < q.2) :
      ‖smoothActualJet e s S q.1 q.2‖ ≤ A := by
    rw [← smooth_jet_fields_aux hset.c1 hq.1 huv hq.2.2]
    apply (pi_norm_le_iff_of_nonneg hA.le).mpr
    apply hformula
    exact smooth_jet_input_bound_of_bounds hset hsR hR hM hD hG hH hP hQ hU rfl hq huv
      (hscalar q hq) (hexp q hq) (hpot q hq) (hcenter q hq)
  have hwhole := smooth_norm_bound_of_off_axis_aux hset.pos
    (continuousOn_smoothActualJet_aux hset.pos hset.c1) hoff
  have hcoord (q : ℝ × ℝ) (hq : q ∈ triangle 0 s) (i : Fin 33) :
      ‖smoothActualJet e s S q.1 q.2 i‖ ≤ A :=
    (norm_le_pi_norm (smoothActualJet e s S q.1 q.2) i).trans (hwhole q hq)
  apply (smooth_c1_bound_of_bound hset hA.le ?_ ?_).2
  · intro q hq f hf
    simp only [mem_insert_iff, mem_singleton_iff] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    · constructor
      · simpa only [smooth_actual_jet_0_aux, Complex.norm_real] using hcoord q hq 0
      · constructor
        · simpa only [smooth_actual_jet_1_aux, Complex.norm_real] using hcoord q hq 1
        · simpa only [smooth_actual_jet_2_aux, Complex.norm_real] using hcoord q hq 2
    · constructor
      · simpa only [smooth_actual_jet_3_aux, Complex.norm_real] using hcoord q hq 3
      · constructor
        · simpa only [smooth_actual_jet_4_aux, Complex.norm_real] using hcoord q hq 4
        · simpa only [smooth_actual_jet_5_aux, Complex.norm_real] using hcoord q hq 5
    · constructor
      · simpa only [smooth_actual_jet_6_aux, Complex.norm_real] using hcoord q hq 6
      · constructor
        · simpa only [smooth_actual_jet_7_aux, Complex.norm_real] using hcoord q hq 7
        · simpa only [smooth_actual_jet_8_aux, Complex.norm_real] using hcoord q hq 8
    · constructor
      · simpa only [smooth_actual_jet_9_aux, Complex.norm_real] using hcoord q hq 9
      · constructor
        · simpa only [smooth_actual_jet_10_aux, Complex.norm_real] using hcoord q hq 10
        · simpa only [smooth_actual_jet_11_aux, Complex.norm_real] using hcoord q hq 11
    · constructor
      · simpa only [smooth_actual_jet_12_aux, Complex.norm_real] using hcoord q hq 12
      · constructor
        · simpa only [smooth_actual_jet_13_aux, Complex.norm_real] using hcoord q hq 13
        · simpa only [smooth_actual_jet_14_aux, Complex.norm_real] using hcoord q hq 14
    · constructor
      · simpa only [smooth_actual_jet_15_aux, Complex.norm_real] using hcoord q hq 15
      · constructor
        · simpa only [smooth_actual_jet_16_aux, Complex.norm_real] using hcoord q hq 16
        · simpa only [smooth_actual_jet_17_aux, Complex.norm_real] using hcoord q hq 17
  · intro q hq f hf
    simp only [mem_insert_iff, mem_singleton_iff] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · constructor
      · simpa only [smooth_actual_jet_18_aux]
          using hcoord q hq 18
      · constructor
        · simpa only [smooth_actual_jet_19_aux]
            using hcoord q hq 19
        · simpa only [smooth_actual_jet_20_aux]
            using hcoord q hq 20
    · constructor
      · simpa only [smooth_actual_jet_21_aux]
          using hcoord q hq 21
      · constructor
        · simpa only [smooth_actual_jet_22_aux]
            using hcoord q hq 22
        · simpa only [smooth_actual_jet_23_aux]
            using hcoord q hq 23
    · constructor
      · simpa only [smooth_actual_jet_24_aux]
          using hcoord q hq 24
      · constructor
        · simpa only [smooth_actual_jet_25_aux]
            using hcoord q hq 25
        · simpa only [smooth_actual_jet_26_aux]
            using hcoord q hq 26
    · constructor
      · simpa only [smooth_actual_jet_27_aux]
          using hcoord q hq 27
      · constructor
        · simpa only [smooth_actual_jet_28_aux]
            using hcoord q hq 28
        · simpa only [smooth_actual_jet_29_aux]
            using hcoord q hq 29
    · constructor
      · simpa only [smooth_actual_jet_30_aux]
          using hcoord q hq 30
      · constructor
        · simpa only [smooth_actual_jet_31_aux]
            using hcoord q hq 31
        · simpa only [smooth_actual_jet_32_aux]
            using hcoord q hq 32

end EmcsfAcExtension.Local
