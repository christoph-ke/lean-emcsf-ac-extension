module

public import EmcsfAcExtension.Local.Apriori.SmoothSupJetFields
import EmcsfAcExtension.Local.Apriori.SmoothSupJetReal
import EmcsfAcExtension.Local.Apriori.SmoothSupJetScalar

/-! # The full regular first-jet identity

The fieldwise identities are assembled without another algebraic expansion.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local

/-- All regular numerical first-jet formulas equal the actual eleven
fields and both characteristic partials off axis. The theorem uses only
the classical field class, without additional regularity or size premises. -/
theorem smooth_jet_fields_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    smoothJetFormula e (smoothJetInput e T S u v) = smoothActualJet e T S u v := by
  have h0 := smooth_jet_r_aux hS hu huv hvT
  have h3 := smooth_jet_lam_aux hS hu huv hvT
  have h6 := smooth_jet_nu_aux hS hu huv hvT
  have h9 := smooth_jet_m_aux hS hu huv hvT
  have h12 := smooth_jet_q_aux hS hu huv hvT
  have h15 := smooth_jet_potential_aux hS hu huv hvT
  have h18 := smooth_jet_phi_aux hS hu huv hvT
  have h21 := smooth_jet_theta_aux hS hu huv hvT
  have h24 := smooth_jet_xi_aux hS hu huv hvT
  have h27 := smooth_jet_a_aux hS hu huv hvT
  have h30 := smooth_jet_b_aux hS hu huv hvT
  funext i
  fin_cases i
  · exact h0.1
  · exact h0.2.1
  · exact h0.2.2
  · exact h3.1
  · exact h3.2.1
  · exact h3.2.2
  · exact h6.1
  · exact h6.2.1
  · exact h6.2.2
  · exact h9.1
  · exact h9.2.1
  · exact h9.2.2
  · exact h12.1
  · exact h12.2.1
  · exact h12.2.2
  · exact h15.1
  · exact h15.2.1
  · exact h15.2.2
  · exact h18.1
  · exact h18.2.1
  · exact h18.2.2
  · exact h21.1
  · exact h21.2.1
  · exact h21.2.2
  · exact h24.1
  · exact h24.2.1
  · exact h24.2.2
  · exact h27.1
  · exact h27.2.1
  · exact h27.2.2
  · exact h30.1
  · exact h30.2.1
  · exact h30.2.2

end EmcsfAcExtension.Local
