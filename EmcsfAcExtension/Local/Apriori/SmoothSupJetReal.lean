module

public import EmcsfAcExtension.Local.Apriori.SmoothSupJetFields
import EmcsfAcExtension.Local.Calculus.AxisCross
import EmcsfAcExtension.Local.Apriori.SmoothSupJetProjection
import EmcsfAcExtension.Local.Apriori.SmoothSupJetFieldProjection

/-! # First-jet identities by field

Each field is checked separately so the algebraic identities stay below
Lean's fixed heartbeat limit. Only classical field equations are used.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local

/-- The three regular numerical jet entries for `r` equal the
actual value and characteristic partials off axis. No size hypothesis
or additional differential identity is assumed. -/
theorem smooth_jet_r_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    smoothJetFormula e (smoothJetInput e T S u v) 0 =
      smoothActualJet e T S u v 0 ∧
    smoothJetFormula e (smoothJetInput e T S u v) 1 =
      smoothActualJet e T S u v 1 ∧
    smoothJetFormula e (smoothJetInput e T S u v) 2 =
      smoothActualJet e T S u v 2 := by
  refine ⟨?_, ?_, ?_⟩
  all_goals simp only [
    smooth_jet_formula_0_aux, smooth_actual_jet_0_aux, smooth_jet_formula_1_aux,
    smooth_actual_jet_1_aux, smooth_jet_formula_2_aux, smooth_actual_jet_2_aux,
    smooth_jet_input_1_0_aux, smooth_jet_input_1_1_aux, smooth_jet_input_1_2_aux]
  · exact congrArg Complex.ofReal (hS.eq_u (u, v) ⟨hu, huv.le, hvT⟩ huv).1.symm
  · exact congrArg Complex.ofReal (hS.eq_v (u, v) ⟨hu, huv.le, hvT⟩ huv).1.symm

/-- The three regular numerical jet entries for `lam` equal the
actual value and characteristic partials off axis. No size hypothesis
or additional differential identity is assumed. -/
theorem smooth_jet_lam_aux {e T : ℝ} {S : Fields}
    (_hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (_hu : 0 ≤ u) (_huv : u < v) (_hvT : v ≤ T) :
    smoothJetFormula e (smoothJetInput e T S u v) 3 =
      smoothActualJet e T S u v 3 ∧
    smoothJetFormula e (smoothJetInput e T S u v) 4 =
      smoothActualJet e T S u v 4 ∧
    smoothJetFormula e (smoothJetInput e T S u v) 5 =
      smoothActualJet e T S u v 5 := by
  refine ⟨?_, ?_, ?_⟩
  all_goals simp only [
    smooth_jet_formula_3_aux, smooth_actual_jet_3_aux, smooth_jet_formula_4_aux,
    smooth_actual_jet_4_aux, smooth_jet_formula_5_aux, smooth_actual_jet_5_aux,
    smooth_jet_input_1_1_aux, smooth_jet_input_1_7_aux, smooth_jet_input_1_8_aux]

/-- The three regular numerical jet entries for `nu` equal the
actual value and characteristic partials off axis. No size hypothesis
or additional differential identity is assumed. -/
theorem smooth_jet_nu_aux {e T : ℝ} {S : Fields}
    (_hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (_hu : 0 ≤ u) (_huv : u < v) (_hvT : v ≤ T) :
    smoothJetFormula e (smoothJetInput e T S u v) 6 =
      smoothActualJet e T S u v 6 ∧
    smoothJetFormula e (smoothJetInput e T S u v) 7 =
      smoothActualJet e T S u v 7 ∧
    smoothJetFormula e (smoothJetInput e T S u v) 8 =
      smoothActualJet e T S u v 8 := by
  refine ⟨?_, ?_, ?_⟩
  all_goals simp only [
    smooth_jet_formula_6_aux, smooth_actual_jet_6_aux, smooth_jet_formula_7_aux,
    smooth_actual_jet_7_aux, smooth_jet_formula_8_aux, smooth_actual_jet_8_aux,
    smooth_jet_input_1_2_aux, smooth_jet_input_1_9_aux, smooth_jet_input_1_10_aux]

/-- The three regular numerical jet entries for `m` equal the
actual value and characteristic partials off axis. No size hypothesis
or additional differential identity is assumed. -/
theorem smooth_jet_m_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    smoothJetFormula e (smoothJetInput e T S u v) 9 =
      smoothActualJet e T S u v 9 ∧
    smoothJetFormula e (smoothJetInput e T S u v) 10 =
      smoothActualJet e T S u v 10 ∧
    smoothJetFormula e (smoothJetInput e T S u v) 11 =
      smoothActualJet e T S u v 11 := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hr := (hS.r_pos (u, v) hp huv).ne'
  have hl := (hS.lam_pos (u, v) hp).ne'
  have hn := (hS.nu_neg (u, v) hp).ne
  have hd := (hS.one_sub_mu_pos (u, v) hp).ne'
  have hrC : (S.r u v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have hlC : (S.lam u v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl
  have hnC : (S.nu u v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  have hdC : 1 - (S.mu u v : ℂ) ≠ 0 := by exact_mod_cast hd
  have hU := hS.eq_u (u, v) hp huv
  have hV := hS.eq_v (u, v) hp huv
  refine ⟨?_, ?_, ?_⟩
  all_goals simp only [
    smooth_jet_formula_9_aux, smooth_actual_jet_9_aux, smooth_jet_formula_10_aux,
    smooth_actual_jet_10_aux, smooth_jet_formula_11_aux, smooth_actual_jet_11_aux,
    smooth_jet_input_1_0_aux, smooth_jet_input_1_1_aux, smooth_jet_input_1_2_aux,
    smooth_jet_input_1_3_aux, smooth_jet_input_1_4_aux, smooth_jet_input_1_5_aux,
    smooth_jet_input_2_1_aux, smooth_jet_input_2_2_aux]
  all_goals try simp only [hU.2.2.1, hV.2.2.1, Fields.mU, Fields.mV, Fields.mu]
  all_goals try simp only [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (hS.r_pos (u, v) hp huv), abs_of_pos (hS.lam_pos (u, v) hp),
    abs_of_neg (hS.nu_neg (u, v) hp)]
  all_goals push_cast
  all_goals field_simp [hr, hl, hn, hd, hrC, hlC, hnC, hdC]

/-- The three regular numerical jet entries for `Q` equal the
actual value and characteristic partials off axis. No size hypothesis
or additional differential identity is assumed. -/
theorem smooth_jet_q_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    smoothJetFormula e (smoothJetInput e T S u v) 12 =
      smoothActualJet e T S u v 12 ∧
    smoothJetFormula e (smoothJetInput e T S u v) 13 =
      smoothActualJet e T S u v 13 ∧
    smoothJetFormula e (smoothJetInput e T S u v) 14 =
      smoothActualJet e T S u v 14 := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hr := (hS.r_pos (u, v) hp huv).ne'
  have hl := (hS.lam_pos (u, v) hp).ne'
  have hn := (hS.nu_neg (u, v) hp).ne
  have hd := (hS.one_sub_mu_pos (u, v) hp).ne'
  have hrC : (S.r u v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have hlC : (S.lam u v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl
  have hnC : (S.nu u v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  have hdC : 1 - (S.mu u v : ℂ) ≠ 0 := by exact_mod_cast hd
  have hU := hS.eq_u (u, v) hp huv
  have hV := hS.eq_v (u, v) hp huv
  refine ⟨?_, ?_, ?_⟩
  all_goals simp only [
    smooth_jet_formula_12_aux, smooth_actual_jet_12_aux, smooth_jet_formula_13_aux,
    smooth_actual_jet_13_aux, smooth_jet_formula_14_aux, smooth_actual_jet_14_aux,
    smooth_jet_input_1_0_aux, smooth_jet_input_1_1_aux, smooth_jet_input_1_2_aux,
    smooth_jet_input_1_4_aux, smooth_jet_input_2_0_aux, smooth_jet_input_2_1_aux,
    smooth_jet_input_2_2_aux]
  all_goals try simp only [hU.2.2.2.1, hV.2.2.2.1, Fields.QU, Fields.QV]
  all_goals try simp only [← mul_div_assoc, Complex.div_ofReal_im]
  all_goals push_cast
  all_goals field_simp [hr, hl, hn, hd, hrC, hlC, hnC, hdC]

/-- The three regular numerical jet entries for `A` equal the
actual value and characteristic partials off axis. No size hypothesis
or additional differential identity is assumed. -/
theorem smooth_jet_potential_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    smoothJetFormula e (smoothJetInput e T S u v) 15 =
      smoothActualJet e T S u v 15 ∧
    smoothJetFormula e (smoothJetInput e T S u v) 16 =
      smoothActualJet e T S u v 16 ∧
    smoothJetFormula e (smoothJetInput e T S u v) 17 =
      smoothActualJet e T S u v 17 := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hr := (hS.r_pos (u, v) hp huv).ne'
  have hl := (hS.lam_pos (u, v) hp).ne'
  have hn := (hS.nu_neg (u, v) hp).ne
  have hd := (hS.one_sub_mu_pos (u, v) hp).ne'
  have hrC : (S.r u v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have hlC : (S.lam u v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl
  have hnC : (S.nu u v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  have hdC : 1 - (S.mu u v : ℂ) ≠ 0 := by exact_mod_cast hd
  have hU := hS.eq_u (u, v) hp huv
  have hV := hS.eq_v (u, v) hp huv
  refine ⟨?_, ?_, ?_⟩
  all_goals simp only [
    smooth_jet_formula_15_aux, smooth_actual_jet_15_aux, smooth_jet_formula_16_aux,
    smooth_actual_jet_16_aux, smooth_jet_formula_17_aux, smooth_actual_jet_17_aux,
    smooth_jet_input_1_0_aux, smooth_jet_input_1_1_aux, smooth_jet_input_1_2_aux,
    smooth_jet_input_1_4_aux, smooth_jet_input_1_6_aux, smooth_jet_input_1_11_aux,
    smooth_jet_input_1_14_aux]
  all_goals try simp only [hV.2.2.2.2.1, Fields.AV]
  all_goals push_cast
  all_goals field_simp [hr, hl, hn, hd, hrC, hlC, hnC, hdC]

end EmcsfAcExtension.Local
