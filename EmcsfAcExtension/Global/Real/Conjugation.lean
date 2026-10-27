module

public import EmcsfAcExtension.Frozen.IsSolution

/-! # Conjugation symmetry of the uncharged solution class

This implements internal project record R1. Only the three complex scalar fields are conjugated.
-/

@[expose] public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension

namespace Fields

/-- Conjugate the scalar fields, preserving all six real fields (internal project record R1). -/
def conj (S : Fields) : Fields where
  r := S.r
  lam := S.lam
  nu := S.nu
  m := S.m
  Q := S.Q
  phi := fun u v => starRingEnd ℂ (S.phi u v)
  A := S.A
  theta := fun u v => starRingEnd ℂ (S.theta u v)
  xi := fun u v => starRingEnd ℂ (S.xi u v)

/-- Conjugation commutes with the normalized outgoing scalar. -/
theorem conj_a (S : Fields) (u v : ℝ) :
    S.conj.a u v = starRingEnd ℂ (S.a u v) := by
  simp [conj, a]

/-- Conjugation commutes with the normalized incoming scalar. -/
theorem conj_b (S : Fields) (u v : ℝ) :
    S.conj.b u v = starRingEnd ℂ (S.b u v) := by
  simp [conj, b]

end Fields

namespace Global.Real

/-- [internal] Conjugation preserves the integral form of a scalar equation. -/
private theorem integralForm_conjugate {f g : ℝ → ℂ} {a b : ℝ}
    (h : IntegralForm f g a b) :
    IntegralForm (fun x => starRingEnd ℂ (f x))
      (fun x => starRingEnd ℂ (g x)) a b := by
  refine ⟨?_, ?_⟩
  · exact ⟨Complex.conjCLE.toContinuousLinearMap.integrable_comp h.1.1,
      Complex.conjCLE.toContinuousLinearMap.integrable_comp h.1.2⟩
  · rw [intervalIntegral.intervalIntegral_conj, ← h.2, map_sub]

/-- [internal] Conjugation does not increase characteristic variation. -/
private theorem variation_conjugate_le (f : ℝ → ℂ) (K : Set ℝ) :
    eVariationOn (fun x => starRingEnd ℂ (f x)) K ≤ eVariationOn f K := by
  have h := Complex.conjLIE.isometry.lipschitzWith.lipschitzOnWith.comp_eVariationOn_le
    (s := K) (g := f) (mapsTo_univ f K)
  simpa [Function.comp_def, Complex.conjLIE_apply] using h

/-- [internal] Conjugation preserves absolute continuity on an interval. -/
private theorem ac_conjugate {f : ℝ → ℂ} {a b : ℝ}
    (h : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => starRingEnd ℂ (f x)) a b :=
  Complex.conjLIE.isometry.lipschitzWith.comp_absolutelyContinuousOnInterval h

/-- At zero coupling, conjugating the scalar fields preserves the complete frozen
AC/BV solution class on every domain (internal project record R1). -/
theorem isSolution_conj {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution 0 S D) : IsSolution 0 S.conj D where
  subset := hS.subset
  r_pos := hS.r_pos
  lam_pos := hS.lam_pos
  nu_neg := hS.nu_neg
  one_sub_mu_pos := hS.one_sub_mu_pos
  cont_r := hS.cont_r
  cont_lam := hS.cont_lam
  cont_nu := hS.cont_nu
  cont_m := hS.cont_m
  cont_Q := hS.cont_Q
  cont_phi := Complex.continuous_conj.comp_continuousOn
    (f := Function.uncurry S.phi) hS.cont_phi
  cont_A := hS.cont_A
  cont_theta := Complex.continuous_conj.comp_continuousOn
    (f := Function.uncurry S.theta) hS.cont_theta
  cont_xi := Complex.continuous_conj.comp_continuousOn
    (f := Function.uncurry S.xi) hS.cont_xi
  eq_out := by
    intro u a b hua hab hs
    obtain ⟨hr, hn, hm, hq, hA, hp, hx⟩ := hS.eq_out u a b hua hab hs
    refine ⟨hr, hn, ?_, ?_, hA, ?_, ?_⟩
    · change IntegralForm (S.m u) (fun v => S.conj.mV u v) a b
      simpa [Fields.mV, Fields.mu, Fields.conj] using
        (show IntegralForm (S.m u) (fun v => S.mV u v) a b from hm)
    · change IntegralForm (S.Q u) (fun v => S.conj.QV 0 u v) a b
      simpa [Fields.QV, Fields.conj] using
        (show IntegralForm (S.Q u) (fun v => S.QV 0 u v) a b from hq)
    · change IntegralForm (fun v => S.conj.phi u v) (fun v => S.conj.phiV u v) a b
      simpa [Fields.phiV, Fields.conj] using integralForm_conjugate hp
    · change IntegralForm (fun v => S.conj.xi u v) (fun v => S.conj.xiV 0 u v) a b
      simpa [Fields.xiV, Fields.waveSource, Fields.conj] using integralForm_conjugate hx
  eq_in := by
    intro a b v hab hbv hs
    obtain ⟨hr, hl, hm, hq, hp, ht⟩ := hS.eq_in a b v hab hbv hs
    refine ⟨hr, hl, ?_, ?_, ?_, ?_⟩
    · simpa [Fields.mU, Fields.mu, Fields.conj] using hm
    · simpa [Fields.QU, Fields.conj] using hq
    · simpa [Fields.phiU, Fields.conj] using integralForm_conjugate hp
    · simpa [Fields.thetaU, Fields.waveSource, Fields.conj] using integralForm_conjugate ht
  ac_out := by
    intro u a b hab hs
    obtain ⟨hr, hm, hq, hp, ha⟩ := hS.ac_out u a b hab hs
    refine ⟨hr, hm, hq, ac_conjugate hp, ?_⟩
    change AbsolutelyContinuousOnInterval (fun v => S.conj.a u v) a b
    simpa only [Fields.conj_a] using ac_conjugate ha
  ac_in := by
    intro a b v hab hs
    obtain ⟨hr, hm, hq, hp⟩ := hS.ac_in a b v hab hs
    exact ⟨hr, hm, hq, ac_conjugate hp⟩
  bv_loc := by
    intro K hK hc
    obtain ⟨B, hB, ho, hi⟩ := hS.bv_loc K hK hc
    refine ⟨B, hB, ?_, ?_⟩
    · intro u a b hs
      obtain ⟨hl, hn, ha, hb⟩ := ho u a b hs
      refine ⟨hl, hn, ?_, ?_⟩
      · change eVariationOn (fun v => S.conj.a u v) (Icc a b) ≤ B
        simpa only [Fields.conj_a] using (variation_conjugate_le _ _).trans ha
      · change eVariationOn (fun v => S.conj.b u v) (Icc a b) ≤ B
        simpa only [Fields.conj_b] using (variation_conjugate_le _ _).trans hb
    · intro a b v hs
      obtain ⟨hl, hn, ha, hb⟩ := hi a b v hs
      refine ⟨hl, hn, ?_, ?_⟩
      · simpa only [Fields.conj_a] using (variation_conjugate_le _ _).trans ha
      · simpa only [Fields.conj_b] using (variation_conjugate_le _ _).trans hb
  axis_small_var := by
    intro t ht η hη
    obtain ⟨δ, hδ, ho, hi⟩ := hS.axis_small_var t ht η hη
    exact ⟨δ, hδ, fun u a b hs => (variation_conjugate_le _ _).trans (ho u a b hs),
      fun a b v hs => (variation_conjugate_le _ _).trans (hi a b v hs)⟩
  axis := by
    intro t ht
    obtain ⟨hr, hm, hq, hln, ha, hb⟩ := hS.axis t ht
    refine ⟨hr, hm, hq, hln, ?_, ?_⟩
    · rw [Fields.conj_a, ha]
      rfl
    · rw [Fields.conj_b, hb]
      rfl
  axis_mu := hS.axis_mu

end Global.Real

end EmcsfAcExtension
