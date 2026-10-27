module

public import EmcsfAcExtension.Local.Apriori.SmoothSupJetFields

/-! # Coordinate projections for the regular first-jet formulas

Abstract coordinate lemmas keep reduction independent of the complexity
of the substituted classical fields.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local

/-- Coordinate 0 of the actual field jet. -/
theorem smooth_actual_jet_0_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    smoothActualJet e T S u v 0 =
      (S.r u v : ℂ) := by rfl

/-- Coordinate 1 of the actual field jet. -/
theorem smooth_actual_jet_1_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    smoothActualJet e T S u v 1 =
      ((pdU (triangle 0 T) S.r u v : ℝ) : ℂ) := by rfl

/-- Coordinate 2 of the actual field jet. -/
theorem smooth_actual_jet_2_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    smoothActualJet e T S u v 2 =
      ((pdV (triangle 0 T) S.r u v : ℝ) : ℂ) := by rfl

/-- Coordinate 3 of the actual field jet. -/
theorem smooth_actual_jet_3_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    smoothActualJet e T S u v 3 =
      S.lam u v := by rfl

/-- Coordinate 4 of the actual field jet. -/
theorem smooth_actual_jet_4_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    smoothActualJet e T S u v 4 =
      ((pdU (triangle 0 T) S.lam u v : ℝ) : ℂ) := by rfl

/-- Coordinate 5 of the actual field jet. -/
theorem smooth_actual_jet_5_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    smoothActualJet e T S u v 5 =
      ((pdV (triangle 0 T) S.lam u v : ℝ) : ℂ) := by rfl

/-- Coordinate 6 of the actual field jet. -/
theorem smooth_actual_jet_6_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    smoothActualJet e T S u v 6 =
      S.nu u v := by rfl

/-- Coordinate 7 of the actual field jet. -/
theorem smooth_actual_jet_7_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    smoothActualJet e T S u v 7 =
      ((pdU (triangle 0 T) S.nu u v : ℝ) : ℂ) := by rfl

/-- Coordinate 8 of the actual field jet. -/
theorem smooth_actual_jet_8_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    smoothActualJet e T S u v 8 =
      ((pdV (triangle 0 T) S.nu u v : ℝ) : ℂ) := by rfl

/-- Coordinate 9 of the actual field jet. -/
theorem smooth_actual_jet_9_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    smoothActualJet e T S u v 9 =
      S.m u v := by rfl

/-- Coordinate 10 of the actual field jet. -/
theorem smooth_actual_jet_10_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    smoothActualJet e T S u v 10 =
      ((pdU (triangle 0 T) S.m u v : ℝ) : ℂ) := by rfl

/-- Coordinate 11 of the actual field jet. -/
theorem smooth_actual_jet_11_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    smoothActualJet e T S u v 11 =
      ((pdV (triangle 0 T) S.m u v : ℝ) : ℂ) := by rfl

/-- Coordinate 12 of the actual field jet. -/
theorem smooth_actual_jet_12_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    smoothActualJet e T S u v 12 =
      S.Q u v := by rfl

/-- Coordinate 13 of the actual field jet. -/
theorem smooth_actual_jet_13_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    smoothActualJet e T S u v 13 =
      ((pdU (triangle 0 T) S.Q u v : ℝ) : ℂ) := by rfl

/-- Coordinate 14 of the actual field jet. -/
theorem smooth_actual_jet_14_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    smoothActualJet e T S u v 14 =
      ((pdV (triangle 0 T) S.Q u v : ℝ) : ℂ) := by rfl

/-- Coordinate 15 of the actual field jet. -/
theorem smooth_actual_jet_15_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    smoothActualJet e T S u v 15 =
      S.A u v := by rfl

/-- Coordinate 16 of the actual field jet. -/
theorem smooth_actual_jet_16_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    smoothActualJet e T S u v 16 =
      ((pdU (triangle 0 T) S.A u v : ℝ) : ℂ) := by rfl

/-- Coordinate 17 of the actual field jet. -/
theorem smooth_actual_jet_17_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    smoothActualJet e T S u v 17 =
      ((pdV (triangle 0 T) S.A u v : ℝ) : ℂ) := by rfl

/-- Coordinate 18 of the actual field jet. -/
theorem smooth_actual_jet_18_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    smoothActualJet e T S u v 18 =
      S.phi u v := by rfl

/-- Coordinate 19 of the actual field jet. -/
theorem smooth_actual_jet_19_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    smoothActualJet e T S u v 19 =
      pdU (triangle 0 T) S.phi u v := by rfl

/-- Coordinate 20 of the actual field jet. -/
theorem smooth_actual_jet_20_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    smoothActualJet e T S u v 20 =
      pdV (triangle 0 T) S.phi u v := by rfl

/-- Coordinate 21 of the actual field jet. -/
theorem smooth_actual_jet_21_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    smoothActualJet e T S u v 21 =
      S.theta u v := by rfl

/-- Coordinate 22 of the actual field jet. -/
theorem smooth_actual_jet_22_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    smoothActualJet e T S u v 22 =
      pdU (triangle 0 T) S.theta u v := by rfl

/-- Coordinate 23 of the actual field jet. -/
theorem smooth_actual_jet_23_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    smoothActualJet e T S u v 23 =
      pdV (triangle 0 T) S.theta u v := by rfl

/-- Coordinate 24 of the actual field jet. -/
theorem smooth_actual_jet_24_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    smoothActualJet e T S u v 24 =
      S.xi u v := by rfl

/-- Coordinate 25 of the actual field jet. -/
theorem smooth_actual_jet_25_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    smoothActualJet e T S u v 25 =
      pdU (triangle 0 T) S.xi u v := by rfl

/-- Coordinate 26 of the actual field jet. -/
theorem smooth_actual_jet_26_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    smoothActualJet e T S u v 26 =
      pdV (triangle 0 T) S.xi u v := by rfl

/-- Coordinate 27 of the actual field jet. -/
theorem smooth_actual_jet_27_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    smoothActualJet e T S u v 27 =
      S.a u v := by rfl

/-- Coordinate 28 of the actual field jet. -/
theorem smooth_actual_jet_28_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    smoothActualJet e T S u v 28 =
      pdU (triangle 0 T) S.a u v := by rfl

/-- Coordinate 29 of the actual field jet. -/
theorem smooth_actual_jet_29_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    smoothActualJet e T S u v 29 =
      pdV (triangle 0 T) S.a u v := by rfl

/-- Coordinate 30 of the actual field jet. -/
theorem smooth_actual_jet_30_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    smoothActualJet e T S u v 30 =
      S.b u v := by rfl

/-- Coordinate 31 of the actual field jet. -/
theorem smooth_actual_jet_31_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    smoothActualJet e T S u v 31 =
      pdU (triangle 0 T) S.b u v := by rfl

/-- Coordinate 32 of the actual field jet. -/
theorem smooth_actual_jet_32_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    smoothActualJet e T S u v 32 =
      pdV (triangle 0 T) S.b u v := by rfl

/-- Coordinate 0 of the real regularized field inputs. -/
theorem smooth_jet_input_1_0_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    (smoothJetInput e T S u v).1 0 =
      S.r u v := by rfl

/-- Coordinate 1 of the real regularized field inputs. -/
theorem smooth_jet_input_1_1_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    (smoothJetInput e T S u v).1 1 =
      S.lam u v := by rfl

/-- Coordinate 2 of the real regularized field inputs. -/
theorem smooth_jet_input_1_2_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    (smoothJetInput e T S u v).1 2 =
      S.nu u v := by rfl

/-- Coordinate 3 of the real regularized field inputs. -/
theorem smooth_jet_input_1_3_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    (smoothJetInput e T S u v).1 3 =
      1 - S.mu u v := by rfl

/-- Coordinate 4 of the real regularized field inputs. -/
theorem smooth_jet_input_1_4_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    (smoothJetInput e T S u v).1 4 =
      S.Q u v / S.r u v ^ 3 := by rfl

/-- Coordinate 5 of the real regularized field inputs. -/
theorem smooth_jet_input_1_5_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    (smoothJetInput e T S u v).1 5 =
      S.mu u v / S.r u v ^ 2 := by rfl

/-- Coordinate 6 of the real regularized field inputs. -/
theorem smooth_jet_input_1_6_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    (smoothJetInput e T S u v).1 6 =
      S.A u v := by rfl

/-- Coordinate 7 of the real regularized field inputs. -/
theorem smooth_jet_input_1_7_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    (smoothJetInput e T S u v).1 7 =
      pdU (triangle 0 T) S.lam u v := by rfl

/-- Coordinate 8 of the real regularized field inputs. -/
theorem smooth_jet_input_1_8_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    (smoothJetInput e T S u v).1 8 =
      pdV (triangle 0 T) S.lam u v := by rfl

/-- Coordinate 9 of the real regularized field inputs. -/
theorem smooth_jet_input_1_9_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    (smoothJetInput e T S u v).1 9 =
      pdU (triangle 0 T) S.nu u v := by rfl

/-- Coordinate 10 of the real regularized field inputs. -/
theorem smooth_jet_input_1_10_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    (smoothJetInput e T S u v).1 10 =
      pdV (triangle 0 T) S.nu u v := by rfl

/-- Coordinate 11 of the real regularized field inputs. -/
theorem smooth_jet_input_1_11_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    (smoothJetInput e T S u v).1 11 =
      pdU (triangle 0 T) S.A u v := by rfl

/-- Coordinate 12 of the real regularized field inputs. -/
theorem smooth_jet_input_1_12_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    (smoothJetInput e T S u v).1 12 =
      (S.lam u v)⁻¹ := by rfl

/-- Coordinate 13 of the real regularized field inputs. -/
theorem smooth_jet_input_1_13_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    (smoothJetInput e T S u v).1 13 =
      (S.nu u v)⁻¹ := by rfl

/-- Coordinate 14 of the real regularized field inputs. -/
theorem smooth_jet_input_1_14_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    (smoothJetInput e T S u v).1 14 =
      (1 - S.mu u v)⁻¹ := by rfl

/-- Coordinate 0 of the complex regularized field inputs. -/
theorem smooth_jet_input_2_0_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    (smoothJetInput e T S u v).2 0 =
      S.phi u v := by rfl

/-- Coordinate 1 of the complex regularized field inputs. -/
theorem smooth_jet_input_2_1_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    (smoothJetInput e T S u v).2 1 =
      S.theta u v / S.lam u v / S.r u v := by rfl

/-- Coordinate 2 of the complex regularized field inputs. -/
theorem smooth_jet_input_2_2_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    (smoothJetInput e T S u v).2 2 =
      S.xi u v / S.nu u v / S.r u v := by rfl

/-- Coordinate 3 of the complex regularized field inputs. -/
theorem smooth_jet_input_2_3_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    (smoothJetInput e T S u v).2 3 =
      pdV (triangle 0 T) S.a u v := by rfl

/-- Coordinate 4 of the complex regularized field inputs. -/
theorem smooth_jet_input_2_4_aux (e T : ℝ) (S : Fields) (u v : ℝ) :
    (smoothJetInput e T S u v).2 4 =
      pdU (triangle 0 T) S.b u v + I * e * S.A u v * S.b u v := by rfl

end EmcsfAcExtension.Local
