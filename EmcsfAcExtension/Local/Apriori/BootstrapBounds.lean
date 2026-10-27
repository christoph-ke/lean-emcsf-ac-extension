module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Defs.Bounds
import EmcsfAcExtension.Local.Apriori.GeometryBox
import EmcsfAcExtension.Local.Apriori.GeometryBoxMass
import EmcsfAcExtension.Local.Apriori.GeometryEnvelope
import EmcsfAcExtension.Local.Apriori.GeometryTV
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseFinal
import EmcsfAcExtension.Local.Apriori.BootstrapIncoming
import EmcsfAcExtension.Local.Apriori.BootstrapCross
import EmcsfAcExtension.Local.Apriori.BootstrapBudgets
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Apriori.Mass

/-! # Assembling every smooth a priori conclusion inside the temporary box

One finite sum of positive constants is chosen before the datum. Each
localized variation and Hardy clause keeps its own section envelope.
The subsequent positive-margin bootstrap discharges the setting premise.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

/-- Every smooth bound follows from a sufficiently small a priori setting.
All positive thresholds and the single conclusion constant precede every
datum and depend only on the fixed box, uniformly in higher derivatives.
No conclusion bundle is a premise; the temporary box is discharged by the
separate positive-margin continuity bootstrap. -/
theorem smoothBounds_of_apriori_setting : ∃ ε₀ δ₀ C : ℝ,
    0 < ε₀ ∧ 0 < δ₀ ∧ 0 < C ∧
    ∀ (e T ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e T ε M S h → ε ≤ ε₀ → |e| * (T / 2) * M ≤ δ₀ →
      SmoothBounds C e T ε M S := by
  obtain ⟨εg, δg, Cg, hεg, hδg, hCg, hgeom⟩ := geometry_bootstrap_improvement
  obtain ⟨εe, δe, Ce, hεe, hδe, hCe, henv⟩ := bv_envelope_final
  obtain ⟨εt, δt, Ct, hεt, hδt, hCt, htv⟩ := bv_geometry_tv
  obtain ⟨εo, δo, Co, hεo, hδo, hCo, hout⟩ := outgoing_geometric_envelope
  obtain ⟨εi, δi, Ci, hεi, hδi, hCi, hin⟩ := incoming_geometric_envelope
  obtain ⟨εb, δb, Cb, hεb, hδb, hCb, hincoming⟩ := ordinary_incoming_variation
  obtain ⟨εr, δr, Cr, hεr, hδr, hCr, hcross⟩ := normalized_cross_variations
  obtain ⟨εw, δw, Cw, hεw, hδw, hCw, hmass⟩ := weighted_mass_budgets
  let C := 1000 + Cg + Ce + Ct + Co + Ci + Cb + Cr + 2 * Cw
  refine ⟨min εg (min εe (min εt (min εo (min εi (min εb (min εr (min εw (1 / 8)))))))),
    min δg (min δe (min δt (min δo (min δi (min δb (min δr (min δw 1))))))), C,
    by positivity, by positivity, by dsimp only [C]; positivity, ?_⟩
  intro e T ε M S h hset hε hδ
  have hes : ε ≤ εg ∧ ε ≤ εe ∧ ε ≤ εt ∧ ε ≤ εo ∧ ε ≤ εi ∧ ε ≤ εb ∧
      ε ≤ εr ∧ ε ≤ εw ∧ ε ≤ 1 / 8 := by simpa only [le_min_iff] using hε
  have hds : |e| * (T / 2) * M ≤ δg ∧ |e| * (T / 2) * M ≤ δe ∧
      |e| * (T / 2) * M ≤ δt ∧ |e| * (T / 2) * M ≤ δo ∧
      |e| * (T / 2) * M ≤ δi ∧ |e| * (T / 2) * M ≤ δb ∧
      |e| * (T / 2) * M ≤ δr ∧ |e| * (T / 2) * M ≤ δw ∧
      |e| * (T / 2) * M ≤ 1 := by simpa only [le_min_iff] using hδ
  rcases hes with ⟨heg, hee, het, heo, hei, heb, her, hew, he8⟩
  rcases hds with ⟨hdg, hde, hdt, hdo, hdi, hdb, hdr, hdw, hd1⟩
  have hCs : Cg ≤ C ∧ Ce ≤ C ∧ Ct ≤ C ∧ Co + Ci ≤ C ∧ Cb ≤ C ∧ Cr ≤ C ∧
      2 * Cw ≤ C ∧ 100 ≤ C := by
    dsimp only [C]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      linarith only [hCg, hCe, hCt, hCo, hCi, hCb, hCr, hCw]
  rcases hCs with ⟨hCgC, hCeC, hCtC, hCoiC, hCbC, hCrC, hCwC, h100⟩
  have he0 := hset.eps_nonneg
  have h3C : 3 ≤ C := by linarith only [h100]
  have up {D x : ℝ} (hDC : D ≤ C) (hx : 0 ≤ x) :
      ENNReal.ofReal (D * x) ≤ ENNReal.ofReal (C * x) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hDC hx)
  have hs (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :=
    localized_scalar_budgets hset he8 hu huv hvT
  have hTV := htv e T ε M S h hset het hdt
  have hCross := hcross e T ε M S h hset her hdr
  have hd0 : 0 ≤ |e| * (T / 2) * M := by have := hset.pos; have := hset.one_le_M; positivity
  have hd2 : (|e| * (T / 2) * M) ^ 2 ≤ 1 := by nlinarith only [hd0, hd1]
  have hMassUp : ENNReal.ofReal (Cw * ε ^ 2 * (1 + (|e| * (T / 2) * M) ^ 2)) ≤
      ENNReal.ofReal (C * ε ^ 2) := by
    apply ENNReal.ofReal_le_ofReal
    have h1 := mul_le_mul_of_nonneg_left hd2 (mul_nonneg hCw.le (sq_nonneg ε))
    have h2 := mul_le_mul_of_nonneg_right hCwC (sq_nonneg ε)
    nlinarith only [h1, h2]
  refine {
    geom := ?_
    mu_nonneg := fun p hp => hset.mu_nonneg hp
    phi_le := fun p hp => (hset.box p hp).2.2.2.2.2.1
    ratio := ?_
    charge := ?_
    env := (henv e T ε M S h hset hee hde).1.trans (up hCeC he0)
    tvj := ?_
    tvk := ?_
    tv_in := ?_
    geomTV_out := fun u hu => (hTV.1 u hu).trans (up hCtC (sq_nonneg ε))
    geomTV_in := fun v hv => (hTV.2 v hv).trans (up hCtC (sq_nonneg ε))
    geomEnv := ?_
    crossTV := ⟨fun v hv => (hCross.1 v hv).trans (ENNReal.ofReal_le_ofReal hCrC),
      fun u hu => (hCross.2 u hu).trans (ENNReal.ofReal_le_ofReal hCrC)⟩
    hardyOut := ?_
    hardyIn := ?_
    massFlux := ?_
  }
  · intro p hp
    have hg := hgeom e T ε M S h hset heg hdg p.1 p.2 hp
    have heq : |-S.nu p.1 p.2 - 1 / 2| = |S.nu p.1 p.2 + 1 / 2| := by
      rw [show -S.nu p.1 p.2 - 1 / 2 = -(S.nu p.1 p.2 + 1 / 2) by ring, abs_neg]
    rw [heq, abs_of_nonneg (hset.mu_nonneg hp)] at hg
    exact hg.trans (mul_le_mul_of_nonneg_right hCgC (sq_nonneg ε))
  · intro p hp
    have hb := hset.box p hp
    have hn : 8 * ε ≤ C * ε := mul_le_mul_of_nonneg_right (by linarith only [h100]) he0
    linarith only [hb.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2, hn]
  · intro p hp
    apply (hset.charge_le hp).trans
    have hn : 0 ≤ |e| * M * ε * S.r p.1 p.2 ^ 2 := by
      have := hset.one_le_M
      positivity
    have hi := mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ C by linarith only [h100]) hn
    nlinarith only [hi]
  · intro u v hu huv hvT
    exact (hs u v hu huv hvT).1.trans (up h3C
      (intervalIntegral.integral_nonneg huv (fun _ _ => ENNReal.toReal_nonneg)))
  · intro u v hu huv hvT
    exact (hs u v hu huv hvT).2.1.trans (up h3C
      (intervalIntegral.integral_nonneg huv (fun _ _ => ENNReal.toReal_nonneg)))
  · intro v hv
    exact (hincoming e T ε M S h hset heb hdb v hv).trans (up hCbC he0)
  · have hb := add_le_add (hout e T ε M S h hset heo hdo) (hin e T ε M S h hset hei hdi)
    apply hb.trans
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    calc
      ENNReal.ofReal (Co * ε ^ 2 + Ci * ε ^ 2) =
          ENNReal.ofReal ((Co + Ci) * ε ^ 2) := by congr 1; ring
      _ ≤ _ := up hCoiC (sq_nonneg ε)
  · intro u v hu huv hvT
    exact (hs u v hu huv hvT).2.2.1.trans (up h3C
      (intervalIntegral.integral_nonneg huv (fun _ _ => ENNReal.toReal_nonneg)))
  · intro u v hu huv hvT
    exact (hs u v hu huv hvT).2.2.2.trans (up h3C
      (intervalIntegral.integral_nonneg huv (fun _ _ => ENNReal.toReal_nonneg)))
  · constructor
    · intro u hu
      have hb := ((hmass e T ε M S h hset hew hdw u T hu.1 hu.2 le_rfl).1).trans hMassUp
      convert hb using 1
      congr 1
      funext v
      congr 1
      ring
    · intro v hv
      have hb := ((hmass e T ε M S h hset hew hdw 0 v le_rfl hv.1 hv.2).2).trans hMassUp
      convert hb using 1
      congr 1
      funext u
      congr 1
      ring

end EmcsfAcExtension.Local
