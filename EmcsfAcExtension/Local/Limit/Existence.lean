module

public import EmcsfAcExtension.Local.Limit.Inputs
public import EmcsfAcExtension.Local.Defs.Limit
public import EmcsfAcExtension.Local.Assembly.Inputs
import EmcsfAcExtension.Local.Limit.ExistencePointwise
import EmcsfAcExtension.Local.Limit.ExistenceGeometryAC
import EmcsfAcExtension.Local.Limit.UIAux
import EmcsfAcExtension.Local.Calculus.Sections
import EmcsfAcExtension.Local.Limit.ExistenceConstruct
import EmcsfAcExtension.Local.Limit.ExistenceSolution
import EmcsfAcExtension.Local.Limit.ExistenceScalarAC
import EmcsfAcExtension.Local.Limit.ExistenceRadiusCharge
import EmcsfAcExtension.Local.Limit.ExistenceMass
import EmcsfAcExtension.Local.Limit.ExistencePhiModulus
import EmcsfAcExtension.Local.Limit.ExistenceVariation
import EmcsfAcExtension.Local.Limit.ExistenceScalarVariation

/-! # AC integral solutions constructed from the two producer contracts

The constructed strong approximation discharges every clause of the frozen
solution class and existence-bound bundle. The final output is definitionally
the assembly proposition `AcDataExistenceStmt`.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

/-- [internal]
Construct the frozen AC integral solution, its exact restart data, strong
approximation witness and every frozen existence bound. All three positive
constants are universal, before time, coupling and datum. Only the two approved
producer propositions are pending, and the output is the exact assembly contract. -/
theorem ac_data_existence_of_inputs (hex : WholeTriangleExistenceStmt) (hstab : StabExtendedStmt) :
    AcDataExistenceStmt := by
  obtain ⟨ε, δ, C, hε, hδ, hC, hconstruct⟩ := Null.controlled_strong_approximants_of_inputs hex
      hstab
  let C₃ := 2 * C ^ 2 + C + 1
  have hC₃ : 0 < C₃ := by dsimp [C₃]; positivity
  have hCC : C ≤ C₃ := by dsimp [C₃]; nlinarith only [sq_nonneg C]
  have hCV : 2 * C ^ 2 ≤ C₃ := by dsimp [C₃]; linarith only [hC]
  refine ⟨ε, δ, C₃, hε, hδ, hC₃, ?_⟩
  intro T e h hT hac hsmall hscale
  obtain ⟨Sn, hn, S, _, hv, herr, hevar, hvar, hc, hb, hlim, hMu, hgeom, hao, hbi, hAxisAC, hUIj,
      hUIk, hlamAC, hnuAC⟩ :=
    hconstruct T e h hT hac hsmall hscale
  have hc1 n := (hc n).1
  have hdata n := (hc n).2
  have hL p (hp : p ∈ triangle 0 T) : 0 < S.lam p.1 p.2 := by
    have hh := (hgeom p hp).1
    linarith only [hh]
  have hN p (hp : p ∈ triangle 0 T) : S.nu p.1 p.2 < 0 := by
    have hh := (hgeom p hp).2.1
    linarith only [hh]
  have hR p (hp : p ∈ triangle 0 T) (hlt : p.1 < p.2) : 0 < S.r p.1 p.2 :=
    (div_pos (sub_pos.mpr hlt) (by norm_num)).trans_le (hgeom p hp).2.2.1
  have hG p (hp : p ∈ triangle 0 T) : 0 < 1 - S.mu p.1 p.2 := by
    have hh := (hgeom p hp).2.2.2
    linarith only [hh]
  have hM : 0 ≤ datumM h T := by
    have hd0 : 0 ≤ datumVar h T := ENNReal.toReal_nonneg
    unfold datumM
    positivity
  have hMn n : 0 ≤ datumM (hn n) T := by
    have hd0 : 0 ≤ datumVar (hn n) T := ENNReal.toReal_nonneg
    unfold datumM
    positivity
  have hMl : Tendsto (fun n => datumM (hn n) T) atTop (𝓝 (datumM h T)) := by
    unfold datumM
    simpa only [hv] using tendsto_const_nhds.add (hvar.const_mul 10)
  have haxis := hlim.axis_small_var_of_smoothBounds hT hC.le hM hMn hc1 hMl hb hUIj hUIk
  obtain ⟨hpo, hpi⟩ := hlim.scalar_ac_of_axis_variation hT hc1 hR hL hN hG (by
    intro t ht
    simpa only [ENNReal.ofReal_one] using haxis t ht 1 zero_lt_one)
  obtain ⟨hrQo, hrQi⟩ := hlim.radius_charge_ac_of_c1 hT hc1 hR hL hN hG
  obtain ⟨hmo, hmi⟩ := hlim.mass_ac_of_c1 hT hc1 hMu hR hL hN hG
  obtain ⟨hgo, hgi⟩ := hlim.geometry_variation_of_smoothBounds
    (fun _ hp => hMu.tendsto_at hp) (fun p hp => (hG p hp).ne') hvar hb
  obtain ⟨hbin, hain, hbout⟩ := hlim.scalar_variation_of_smoothBounds
    (fun p hp => (hL p hp).ne') (fun p hp => (hN p hp).ne) hvar hb
  have hscalar := hlim.natural_covariant_variation_of_smoothBounds hT hC.le ENNReal.toReal_nonneg
    (fun _ => ENNReal.toReal_nonneg) hc1 (fun p hp => (hL p hp).ne')
    (fun p hp => (hN p hp).ne) hvar hb
  let G := ENNReal.ofReal (C * datumVar h T ^ 2)
  let V := ENNReal.ofReal (2 * C ^ 2 * datumVar h T)
  let I := ENNReal.ofReal (C * datumVar h T)
  let X := ENNReal.ofReal C
  let B := G + V + I + X
  have hGB : G ≤ B := le_self_add.trans (le_self_add.trans le_self_add)
  have hVB : V ≤ B := le_add_self.trans (le_self_add.trans le_self_add)
  have hIB : I ≤ B := le_add_self.trans le_self_add
  have hXB : X ≤ B := le_add_self
  have hsol : IsSolution e S (triangle 0 T) :=
    hlim.isSolution_of_characteristic_regularity hT hc1 hMu hR hL hN hG
      (fun u hu => (hrQo u hu).1) (fun v hv => (hrQi v hv).1) hmo hmi
      (fun u hu => (hrQo u hu).2) (fun v hv => (hrQi v hv).2) hpo hpi hao
      (by simp [B, G, V, I, X])
      (fun u hu => ⟨((hgo u hu).1).trans hGB, ((hgo u hu).2.1).trans hGB,
        ((le_iSup₂ u hu).trans (le_self_add.trans hscalar)).trans hVB,
        (hbout u hu).trans hXB⟩)
      (fun v hv => ⟨((hgi v hv).1).trans hGB, ((hgi v hv).2.1).trans hGB,
        (hain v hv).trans hXB, (hbin v hv).trans hIB⟩) haxis
  have cMu := hMu.continuousOn (Eventually.of_forall fun n => (hc1 n).continuousOn_mu hT).frequently
  obtain ⟨hgeoACo, hgeoACi⟩ := IsSolution.geometry_ac_of_bounds hsol cMu
    (fun p hp => (hgeom p hp).2.2.2) hlamAC hnuAC ENNReal.ofReal_ne_top
    (fun u hu => ⟨(hgo u hu).2.1, (hgo u hu).2.2.1⟩)
    (fun v hv => ⟨(hgi v hv).1, (hgi v hv).2.2.1⟩)
  have hpoint := hlim.pointwise_bounds_of_smoothBounds hc1 hR
    (fun p hp => (hL p hp).ne') (fun p hp => (hN p hp).ne) hv hvar hb
  have hd0 : 0 ≤ datumVar h T := ENNReal.toReal_nonneg
  have hCd : C * datumVar h T ≤ C₃ * datumVar h T := mul_le_mul_of_nonneg_right hCC hd0
  have hCd2 : C * datumVar h T ^ 2 ≤ C₃ * datumVar h T ^ 2 :=
    mul_le_mul_of_nonneg_right hCC (sq_nonneg _)
  have hbounds : ExistenceBounds C₃ e T h S := by
    refine ⟨hao, hbi, hAxisAC,
      hscalar.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCV hd0)),
      ?_, ?_, ?_, hgeoACo, hgeoACi, IsSolution.contDiffOn_r hsol hT, ?_⟩
    · intro p hp
      obtain ⟨_, hphi, hratio, hgeometry, hcharge⟩ := hpoint p hp
      refine ⟨hphi, hratio.trans hCd, hgeometry.trans hCd2, hcharge.trans ?_⟩
      gcongr
      exact le_rfl
    · intro u hu
      obtain ⟨h1, h2, h3, h4⟩ := hgo u hu
      exact ⟨h1.trans (ENNReal.ofReal_le_ofReal hCd2), h2.trans (ENNReal.ofReal_le_ofReal hCd2),
        h3.trans (ENNReal.ofReal_le_ofReal hCd2), h4.trans (ENNReal.ofReal_le_ofReal hCd2)⟩
    · intro v hv
      obtain ⟨h1, h2, h3, h4⟩ := hgi v hv
      exact ⟨h1.trans (ENNReal.ofReal_le_ofReal hCd2), h2.trans (ENNReal.ofReal_le_ofReal hCd2),
        h3.trans (ENNReal.ofReal_le_ofReal hCd2), h4.trans (ENNReal.ofReal_le_ofReal hCd2)⟩
    · exact iSup₂_le fun v hv => (hbin v hv).trans (ENNReal.ofReal_le_ofReal hCd)
  exact ⟨S, hsol, restart_data_of_strongLimit hT hc1 hdata hac hv herr hlim
    (fun p hp => (hL p hp).ne'),
    ⟨Sn, hn, hv, hevar, Eventually.of_forall hc, hlim⟩, hbounds⟩

end EmcsfAcExtension.Local
