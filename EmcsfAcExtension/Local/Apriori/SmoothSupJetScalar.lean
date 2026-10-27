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

/-- The three regular numerical jet entries for `phi` equal the
actual value and characteristic partials off axis. No size hypothesis
or additional differential identity is assumed. -/
theorem smooth_jet_phi_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    smoothJetFormula e (smoothJetInput e T S u v) 18 =
      smoothActualJet e T S u v 18 ∧
    smoothJetFormula e (smoothJetInput e T S u v) 19 =
      smoothActualJet e T S u v 19 ∧
    smoothJetFormula e (smoothJetInput e T S u v) 20 =
      smoothActualJet e T S u v 20 := by
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
    smooth_jet_formula_18_aux, smooth_actual_jet_18_aux, smooth_jet_formula_19_aux,
    smooth_actual_jet_19_aux, smooth_jet_formula_20_aux, smooth_actual_jet_20_aux,
    smooth_jet_input_1_1_aux, smooth_jet_input_1_2_aux, smooth_jet_input_1_6_aux,
    smooth_jet_input_2_0_aux, smooth_jet_input_2_1_aux, smooth_jet_input_2_2_aux]
  all_goals try simp only [hU.2.2.2.2.1, hV.2.2.2.2.2.1, Fields.phiU, Fields.phiV]
  all_goals field_simp [hr, hl, hn, hd, hrC, hlC, hnC, hdC]

/-- The three regular numerical jet entries for `theta` equal the
actual value and characteristic partials off axis. No size hypothesis
or additional differential identity is assumed. -/
theorem smooth_jet_theta_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    smoothJetFormula e (smoothJetInput e T S u v) 21 =
      smoothActualJet e T S u v 21 ∧
    smoothJetFormula e (smoothJetInput e T S u v) 22 =
      smoothActualJet e T S u v 22 ∧
    smoothJetFormula e (smoothJetInput e T S u v) 23 =
      smoothActualJet e T S u v 23 := by
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
  have hθ := smooth_theta_v_recovery_aux hS hu huv hvT
  refine ⟨?_, ?_, ?_⟩
  all_goals simp only [
    smooth_jet_formula_21_aux, smooth_actual_jet_21_aux, smooth_jet_formula_22_aux,
    smooth_actual_jet_22_aux, smooth_jet_formula_23_aux, smooth_actual_jet_23_aux,
    smooth_jet_input_1_0_aux, smooth_jet_input_1_1_aux, smooth_jet_input_1_2_aux,
    smooth_jet_input_1_4_aux, smooth_jet_input_1_6_aux, smooth_jet_input_1_8_aux,
    smooth_jet_input_1_14_aux, smooth_jet_input_2_0_aux, smooth_jet_input_2_1_aux,
    smooth_jet_input_2_2_aux, smooth_jet_input_2_3_aux]
  all_goals try simp only [hU.2.2.2.2.2, hV.2.2.2.2.2.1, hθ,
    Fields.thetaU, Fields.phiV, Fields.waveSource]
  all_goals push_cast
  all_goals field_simp [hr, hl, hn, hd, hrC, hlC, hnC, hdC]

/-- The three regular numerical jet entries for `xi` equal the
actual value and characteristic partials off axis. No size hypothesis
or additional differential identity is assumed. -/
theorem smooth_jet_xi_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    smoothJetFormula e (smoothJetInput e T S u v) 24 =
      smoothActualJet e T S u v 24 ∧
    smoothJetFormula e (smoothJetInput e T S u v) 25 =
      smoothActualJet e T S u v 25 ∧
    smoothJetFormula e (smoothJetInput e T S u v) 26 =
      smoothActualJet e T S u v 26 := by
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
  have hξ := smooth_xi_u_recovery_aux hS hu huv hvT
  refine ⟨?_, ?_, ?_⟩
  all_goals simp only [
    smooth_jet_formula_24_aux, smooth_actual_jet_24_aux, smooth_jet_formula_25_aux,
    smooth_actual_jet_25_aux, smooth_jet_formula_26_aux, smooth_actual_jet_26_aux,
    smooth_jet_input_1_0_aux, smooth_jet_input_1_1_aux, smooth_jet_input_1_2_aux,
    smooth_jet_input_1_4_aux, smooth_jet_input_1_6_aux, smooth_jet_input_1_9_aux,
    smooth_jet_input_1_14_aux, smooth_jet_input_2_0_aux, smooth_jet_input_2_1_aux,
    smooth_jet_input_2_2_aux, smooth_jet_input_2_4_aux]
  all_goals try simp only [hV.2.2.2.2.2.2, hU.2.2.2.2.1, hξ,
    Fields.xiV, Fields.phiU, Fields.waveSource, Fields.b]
  all_goals push_cast
  all_goals (try field_simp [hr, hl, hn, hd, hrC, hlC, hnC, hdC]) <;> ring

/-- The three regular numerical jet entries for `a` equal the
actual value and characteristic partials off axis. No size hypothesis
or additional differential identity is assumed. -/
theorem smooth_jet_a_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    smoothJetFormula e (smoothJetInput e T S u v) 27 =
      smoothActualJet e T S u v 27 ∧
    smoothJetFormula e (smoothJetInput e T S u v) 28 =
      smoothActualJet e T S u v 28 ∧
    smoothJetFormula e (smoothJetInput e T S u v) 29 =
      smoothActualJet e T S u v 29 := by
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
  have ha := pdU_a_transport_aux hS hu huv hvT
  refine ⟨?_, ?_, ?_⟩
  all_goals simp only [
    smooth_jet_formula_27_aux, smooth_actual_jet_27_aux, smooth_jet_formula_28_aux,
    smooth_actual_jet_28_aux, smooth_jet_formula_29_aux, smooth_actual_jet_29_aux,
    smooth_jet_input_1_0_aux, smooth_jet_input_1_2_aux, smooth_jet_input_1_4_aux,
    smooth_jet_input_1_6_aux, smooth_jet_input_1_7_aux, smooth_jet_input_1_12_aux,
    smooth_jet_input_1_14_aux, smooth_jet_input_2_0_aux, smooth_jet_input_2_1_aux,
    smooth_jet_input_2_3_aux]
  all_goals try simp only [ha, Fields.a]
  all_goals push_cast
  all_goals field_simp [hr, hl, hn, hd, hrC, hlC, hnC, hdC]

/-- The three regular numerical jet entries for `b` equal the
actual value and characteristic partials off axis. No size hypothesis
or additional differential identity is assumed. -/
theorem smooth_jet_b_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    smoothJetFormula e (smoothJetInput e T S u v) 30 =
      smoothActualJet e T S u v 30 ∧
    smoothJetFormula e (smoothJetInput e T S u v) 31 =
      smoothActualJet e T S u v 31 ∧
    smoothJetFormula e (smoothJetInput e T S u v) 32 =
      smoothActualJet e T S u v 32 := by
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
  have hb := pdV_b_transport_aux hS hu huv hvT
  refine ⟨?_, ?_, ?_⟩
  all_goals simp only [
    smooth_jet_formula_30_aux, smooth_actual_jet_30_aux, smooth_jet_formula_31_aux,
    smooth_actual_jet_31_aux, smooth_jet_formula_32_aux, smooth_actual_jet_32_aux,
    smooth_jet_input_1_0_aux, smooth_jet_input_1_1_aux, smooth_jet_input_1_4_aux,
    smooth_jet_input_1_6_aux, smooth_jet_input_1_10_aux, smooth_jet_input_1_13_aux,
    smooth_jet_input_1_14_aux, smooth_jet_input_2_0_aux, smooth_jet_input_2_2_aux,
    smooth_jet_input_2_4_aux]
  all_goals try simp only [hb, Fields.b]
  all_goals push_cast
  all_goals (try field_simp [hr, hl, hn, hd, hrC, hlC, hnC, hdC]) <;> ring

end EmcsfAcExtension.Local
