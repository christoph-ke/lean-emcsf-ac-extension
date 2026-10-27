module

public import EmcsfAcExtension.Local.Apriori.SmoothSupJetFields

/-! # Coordinate projections for the regular first-jet formulas

Abstract coordinate lemmas keep reduction independent of the complexity
of the substituted classical fields.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local

/-- Coordinate 0 of the numerical jet formula. -/
theorem smooth_jet_formula_0_aux (e : ℝ) (x : (Fin 15 → ℝ) × (Fin 5 → ℂ)) :
    smoothJetFormula e x 0 =
      ((x.1 0) : ℂ) := by rfl

/-- Coordinate 1 of the numerical jet formula. -/
theorem smooth_jet_formula_1_aux (e : ℝ) (x : (Fin 15 → ℝ) × (Fin 5 → ℂ)) :
    smoothJetFormula e x 1 =
      (x.1 2) := by rfl

/-- Coordinate 2 of the numerical jet formula. -/
theorem smooth_jet_formula_2_aux (e : ℝ) (x : (Fin 15 → ℝ) × (Fin 5 → ℂ)) :
    smoothJetFormula e x 2 =
      (x.1 1) := by rfl

/-- Coordinate 3 of the numerical jet formula. -/
theorem smooth_jet_formula_3_aux (e : ℝ) (x : (Fin 15 → ℝ) × (Fin 5 → ℂ)) :
    smoothJetFormula e x 3 =
      (x.1 1) := by rfl

/-- Coordinate 4 of the numerical jet formula. -/
theorem smooth_jet_formula_4_aux (e : ℝ) (x : (Fin 15 → ℝ) × (Fin 5 → ℂ)) :
    smoothJetFormula e x 4 =
      (x.1 7) := by rfl

/-- Coordinate 5 of the numerical jet formula. -/
theorem smooth_jet_formula_5_aux (e : ℝ) (x : (Fin 15 → ℝ) × (Fin 5 → ℂ)) :
    smoothJetFormula e x 5 =
      (x.1 8) := by rfl

/-- Coordinate 6 of the numerical jet formula. -/
theorem smooth_jet_formula_6_aux (e : ℝ) (x : (Fin 15 → ℝ) × (Fin 5 → ℂ)) :
    smoothJetFormula e x 6 =
      (x.1 2) := by rfl

/-- Coordinate 7 of the numerical jet formula. -/
theorem smooth_jet_formula_7_aux (e : ℝ) (x : (Fin 15 → ℝ) × (Fin 5 → ℂ)) :
    smoothJetFormula e x 7 =
      (x.1 9) := by rfl

/-- Coordinate 8 of the numerical jet formula. -/
theorem smooth_jet_formula_8_aux (e : ℝ) (x : (Fin 15 → ℝ) × (Fin 5 → ℂ)) :
    smoothJetFormula e x 8 =
      (x.1 10) := by rfl

/-- Coordinate 9 of the numerical jet formula. -/
theorem smooth_jet_formula_9_aux (e : ℝ) (x : (Fin 15 → ℝ) × (Fin 5 → ℂ)) :
    smoothJetFormula e x 9 =
      (x.1 5) * (x.1 0) ^ 3 / 2 := by rfl

/-- Coordinate 10 of the numerical jet formula. -/
theorem smooth_jet_formula_10_aux (e : ℝ) (x : (Fin 15 → ℝ) × (Fin 5 → ℂ)) :
    smoothJetFormula e x 10 =
      (x.1 2) / 2 * ((x.1 3) * (x.1 0) ^ 2 * ‖(x.2 2)‖ ^ 2 + (x.1 4) ^ 2 * (x.1 0) ^ 4) := by rfl

/-- Coordinate 11 of the numerical jet formula. -/
theorem smooth_jet_formula_11_aux (e : ℝ) (x : (Fin 15 → ℝ) × (Fin 5 → ℂ)) :
    smoothJetFormula e x 11 =
      (x.1 1) / 2 * ((x.1 3) * (x.1 0) ^ 2 * ‖(x.2 1)‖ ^ 2 + (x.1 4) ^ 2 * (x.1 0) ^ 4) := by rfl

/-- Coordinate 12 of the numerical jet formula. -/
theorem smooth_jet_formula_12_aux (e : ℝ) (x : (Fin 15 → ℝ) × (Fin 5 → ℂ)) :
    smoothJetFormula e x 12 =
      (x.1 4) * (x.1 0) ^ 3 := by rfl

/-- Coordinate 13 of the numerical jet formula. -/
theorem smooth_jet_formula_13_aux (e : ℝ) (x : (Fin 15 → ℝ) × (Fin 5 → ℂ)) :
    smoothJetFormula e x 13 =
      e * (x.1 2) * (x.1 0) ^ 2 * (starRingEnd ℂ (x.2 0) * (x.2 2)).im := by rfl

/-- Coordinate 14 of the numerical jet formula. -/
theorem smooth_jet_formula_14_aux (e : ℝ) (x : (Fin 15 → ℝ) × (Fin 5 → ℂ)) :
    smoothJetFormula e x 14 =
      -(e * (x.1 1) * (x.1 0) ^ 2 * (starRingEnd ℂ (x.2 0) * (x.2 1)).im) := by rfl

/-- Coordinate 15 of the numerical jet formula. -/
theorem smooth_jet_formula_15_aux (e : ℝ) (x : (Fin 15 → ℝ) × (Fin 5 → ℂ)) :
    smoothJetFormula e x 15 =
      (x.1 6) := by rfl

/-- Coordinate 16 of the numerical jet formula. -/
theorem smooth_jet_formula_16_aux (e : ℝ) (x : (Fin 15 → ℝ) × (Fin 5 → ℂ)) :
    smoothJetFormula e x 16 =
      (x.1 11) := by rfl

/-- Coordinate 17 of the numerical jet formula. -/
theorem smooth_jet_formula_17_aux (e : ℝ) (x : (Fin 15 → ℝ) × (Fin 5 → ℂ)) :
    smoothJetFormula e x 17 =
      2 * (x.1 2) * (x.1 1) * (x.1 4) * (x.1 0) * (x.1 14) := by rfl

/-- Coordinate 18 of the numerical jet formula. -/
theorem smooth_jet_formula_18_aux (e : ℝ) (x : (Fin 15 → ℝ) × (Fin 5 → ℂ)) :
    smoothJetFormula e x 18 =
      (x.2 0) := by rfl

/-- Coordinate 19 of the numerical jet formula. -/
theorem smooth_jet_formula_19_aux (e : ℝ) (x : (Fin 15 → ℝ) × (Fin 5 → ℂ)) :
    smoothJetFormula e x 19 =
      ((x.1 2) * (x.2 2) - I * e * (x.1 6) * (x.2 0)) := by rfl

/-- Coordinate 20 of the numerical jet formula. -/
theorem smooth_jet_formula_20_aux (e : ℝ) (x : (Fin 15 → ℝ) × (Fin 5 → ℂ)) :
    smoothJetFormula e x 20 =
      ((x.1 1) * (x.2 1)) := by rfl

/-- Coordinate 21 of the numerical jet formula. -/
theorem smooth_jet_formula_21_aux (e : ℝ) (x : (Fin 15 → ℝ) × (Fin 5 → ℂ)) :
    smoothJetFormula e x 21 =
      ((x.1 1) * (x.1 0) * (x.2 1)) := by rfl

/-- Coordinate 22 of the numerical jet formula. -/
theorem smooth_jet_formula_22_aux (e : ℝ) (x : (Fin 15 → ℝ) × (Fin 5 → ℂ)) :
    smoothJetFormula e x 22 =
      -(I * e * (x.1 6) * ((x.1 1) * (x.1 0) * (x.2 1))) - (x.1 1) * (x.1 2) * (x.2 2) - I * e *
      (x.1 4) * (x.1 0) ^ 2 * (x.2 0) * (x.1 2) * (x.1 1) * (x.1 14) := by rfl

/-- Coordinate 23 of the numerical jet formula. -/
theorem smooth_jet_formula_23_aux (e : ℝ) (x : (Fin 15 → ℝ) × (Fin 5 → ℂ)) :
    smoothJetFormula e x 23 =
      (x.1 8) * (x.1 0) * (x.2 1) + (x.1 1) * ((x.2 3) - ((x.1 1) * (x.2 1))) := by rfl

/-- Coordinate 24 of the numerical jet formula. -/
theorem smooth_jet_formula_24_aux (e : ℝ) (x : (Fin 15 → ℝ) × (Fin 5 → ℂ)) :
    smoothJetFormula e x 24 =
      ((x.1 2) * (x.1 0) * (x.2 2)) := by rfl

/-- Coordinate 25 of the numerical jet formula. -/
theorem smooth_jet_formula_25_aux (e : ℝ) (x : (Fin 15 → ℝ) × (Fin 5 → ℂ)) :
    smoothJetFormula e x 25 =
      (x.1 9) * (x.1 0) * (x.2 2) + (x.1 2) * (((x.2 4) - I * e * (x.1 6) * ((x.2 0) + (x.1 0) *
      (x.2 2))) - ((x.1 2) * (x.2 2) - I * e * (x.1 6) * (x.2 0))) := by rfl

/-- Coordinate 26 of the numerical jet formula. -/
theorem smooth_jet_formula_26_aux (e : ℝ) (x : (Fin 15 → ℝ) × (Fin 5 → ℂ)) :
    smoothJetFormula e x 26 =
      -((x.1 2) * (x.1 1) * (x.2 1)) + I * e * (x.1 4) * (x.1 0) ^ 2 * (x.2 0) * (x.1 2) * (x.1
      1) * (x.1 14) := by rfl

/-- Coordinate 27 of the numerical jet formula. -/
theorem smooth_jet_formula_27_aux (e : ℝ) (x : (Fin 15 → ℝ) × (Fin 5 → ℂ)) :
    smoothJetFormula e x 27 =
      ((x.2 0) + (x.1 0) * (x.2 1)) := by rfl

/-- Coordinate 28 of the numerical jet formula. -/
theorem smooth_jet_formula_28_aux (e : ℝ) (x : (Fin 15 → ℝ) × (Fin 5 → ℂ)) :
    smoothJetFormula e x 28 =
      -(I * e * (x.1 6) * ((x.2 0) + (x.1 0) * (x.2 1))) - (x.1 7) * (x.1 12) * (x.1 0) * (x.2
      1) - I * e * (x.1 2) * (x.1 4) * (x.1 0) ^ 2 * (x.2 0) * (x.1 14) := by rfl

/-- Coordinate 29 of the numerical jet formula. -/
theorem smooth_jet_formula_29_aux (e : ℝ) (x : (Fin 15 → ℝ) × (Fin 5 → ℂ)) :
    smoothJetFormula e x 29 =
      (x.2 3) := by rfl

/-- Coordinate 30 of the numerical jet formula. -/
theorem smooth_jet_formula_30_aux (e : ℝ) (x : (Fin 15 → ℝ) × (Fin 5 → ℂ)) :
    smoothJetFormula e x 30 =
      ((x.2 0) + (x.1 0) * (x.2 2)) := by rfl

/-- Coordinate 31 of the numerical jet formula. -/
theorem smooth_jet_formula_31_aux (e : ℝ) (x : (Fin 15 → ℝ) × (Fin 5 → ℂ)) :
    smoothJetFormula e x 31 =
      ((x.2 4) - I * e * (x.1 6) * ((x.2 0) + (x.1 0) * (x.2 2))) := by rfl

/-- Coordinate 32 of the numerical jet formula. -/
theorem smooth_jet_formula_32_aux (e : ℝ) (x : (Fin 15 → ℝ) × (Fin 5 → ℂ)) :
    smoothJetFormula e x 32 =
      -((x.1 10) * (x.1 13) * (x.1 0) * (x.2 2)) + I * e * (x.1 1) * (x.1 4) * (x.1 0) ^ 2 *
      (x.2 0) * (x.1 14) := by rfl

end EmcsfAcExtension.Local
