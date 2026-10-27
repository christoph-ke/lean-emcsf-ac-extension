module

public import EmcsfAcExtension.Global.Observation.SourceInnerGeometry
public import EmcsfAcExtension.Global.Observation.CorePotential
public import EmcsfAcExtension.Global.Observation.InnerCharge
public import EmcsfAcExtension.Global.Observation.OuterOutgoing
public import EmcsfAcExtension.Global.Observation.IncomingClockDischarge
import Mathlib

/-! # Discharging the inner normalization record

All comparison errors come from the landed outer comparison and incoming
trace. The primitive charge and retained potential come from the global
core estimates. Source: charged_SF_new_version.tex:L2587–2755; approved internal project record.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
Assemble the inner record from the actual source geometry and core
bounds. The source consumer discharges every geometric and core premise
using the original solution and constructed window. Both outer comparison
suprema, outgoing errors and the incoming clock trace are discharged
here. Every constant precedes all physical fields and errors; their
scope is exactly the displayed fixed parameters. No incoming pointwise
smallness, mass-comparison estimate or new gauge is assumed. -/
theorem inner_record_of_geometry_and_core (Kstatic : ℝ) (hKs : 0 ≤ Kstatic) :
    ∃ Lmin > 0, ∀ Ct : ℝ, 0 < Ct →
    ∀ δ rStar Lzero c K Ccore : ℝ,
    0 < δ → 0 < rStar → rStar ≤ Lzero → Lmin ≤ Lzero →
    0 < c → 0 ≤ K → 0 ≤ Ccore →
    ∃ CB CE Cq Ctheta Cmass Cxi Bcharge Amax Cscalar Qmax : ℝ,
      0 < CB ∧ 0 < CE ∧ 0 < Cq ∧ 0 < Ctheta ∧ 0 < Cmass ∧ 0 < Cxi ∧
      0 < Bcharge ∧ 0 < Amax ∧ 0 < Cscalar ∧ 0 < Qmax ∧
    ∀ (P : Fields) (D : Set (ℝ × ℝ)) (H Pzero : ℂ)
      (phiOut yOut yIn : ℝ → ℂ) (mOut mIn : ℝ → ℝ)
      (a b L epsilon eta qStar e rho delta Kref Gref : ℝ) (U V : ℝ ≃o ℝ),
    let Q := nullPullback P U V
    let E := {p : ℝ × ℝ | (U p.1, V p.2) ∈ D}
    let R := sidewaysTruncation Q E (-K) K rho Lzero
    OuterNormalizationData Kstatic Ct Ct P D H Pzero phiOut yOut mOut
      a b Lzero L epsilon eta qStar e →
    4 * (CB * epsilon + CE * eta) ≤ 1 / 2 → Cq * eta ≤ 1 →
    rStar ≤ rho → rho ≤ Lzero →
    ContDiff ℝ 1 (U : ℝ → ℝ) → ContDiff ℝ 1 (U.symm : ℝ → ℝ) →
    (∀ x, 0 < deriv (U : ℝ → ℝ) x) →
    (∀ x, 0 < deriv (V : ℝ → ℝ) x) →
    (∀ t ∈ Icc (-K) K,
      (U t, V t) ∈ sidewaysTruncation P D a b Lzero L ∧ P.r (U t) (V t) = Lzero ∧
      deriv (U : ℝ → ℝ) t ≤ 1 / (2 * c) ∧ Q.nu t t = -1 / 2 ∧ Q.lam t t = 1 / 2) →
    (∀ p ∈ R, (U p.1, V p.2) ∈ sidewaysTruncation P D a b rStar L) →
    (∀ p ∈ sidewaysTruncation P D a b rStar L,
      sidewaysTriangle p.2 p.1 ⊆ sidewaysTruncation P D a b rStar L) →
    (ContinuousOn (Function.uncurry P.r) (sidewaysTruncation P D a b rStar L) ∧
      ContinuousOn (Function.uncurry P.lam) (sidewaysTruncation P D a b rStar L) ∧
      ContinuousOn (Function.uncurry P.A) (sidewaysTruncation P D a b rStar L) ∧
      ContinuousOn (Function.uncurry P.nu) (sidewaysTruncation P D a b rStar L) ∧
      ContinuousOn (Function.uncurry P.Q) (sidewaysTruncation P D a b rStar L) ∧
      ContinuousOn (Function.uncurry P.m) (sidewaysTruncation P D a b rStar L)) →
    (∀ p ∈ sidewaysTruncation P D a b rStar L,
      HasDerivAt (P.r p.1) (P.lam p.1 p.2) p.2 ∧ HasDerivAt (P.A p.1) (P.AV p.1 p.2) p.2) →
    (∀ t, (t,t) ∈ sidewaysTruncation P D a b rStar L → P.A t t = 0) →
    (∀ p ∈ sidewaysTruncation P D a b rStar L,
      P.m p.1 p.2 ∈ Icc 0 2 ∧ δ ≤ 1 - P.mu p.1 p.2 ∧
      0 ≤ P.lam p.1 p.2 ∧ |P.nu p.1 p.2| ≤ 1 / 2 ∧
      P.Q p.1 p.2 ^ 2 / P.r p.1 p.2 ^ 2 ≤ P.mu p.1 p.2 ∧
      ‖P.phi p.1 p.2‖ ≤ ‖H‖ + (2 + 2 / Real.sqrt δ) / Real.sqrt (P.r p.1 p.2) ∧
      P.Q p.1 p.2 ^ 2 ≤ Ccore * e ^ 2 * P.m p.1 p.2 *
        (‖H‖ ^ 2 * P.r p.1 p.2 ^ 3 + P.r p.1 p.2 ^ 2)) →
    IsCompact R → (∀ p ∈ R, sidewaysTriangle p.2 p.1 ⊆ R) →
    (ContinuousOn (Function.uncurry Q.r) R ∧ ContinuousOn (Function.uncurry Q.nu) R ∧
      ContinuousOn (Function.uncurry Q.lam) R ∧ ContinuousOn (Function.uncurry Q.A) R ∧
      ContinuousOn (Function.uncurry Q.phi) R ∧ ContinuousOn (Function.uncurry Q.theta) R ∧
      ContinuousOn (Function.uncurry Q.m) R ∧ ContinuousOn (Function.uncurry Q.Q) R ∧
      ContinuousOn (Function.uncurry Q.xi) R) →
    (∀ p ∈ R, -Q.nu p.1 p.2 ∈ Icc c (1 / 2) ∧ Q.lam p.1 p.2 ∈ Icc c (1 / 2) ∧
      Q.m p.1 p.2 ∈ Icc 0 2 ∧ delta ≤ 1 - Q.mu p.1 p.2) →
    (∀ p ∈ R,
      HasDerivAt (fun u => Q.r u p.2) (Q.nu p.1 p.2) p.1 ∧
      HasDerivAt (Q.r p.1) (Q.lam p.1 p.2) p.2 ∧
      HasDerivAt (Q.m p.1) (Q.mV p.1 p.2) p.2 ∧
      HasDerivAt (fun u => Q.lam u p.2) (Q.rUV p.1 p.2) p.1 ∧
      HasDerivAt (fun u => Q.theta u p.2) (Q.thetaU e p.1 p.2) p.1 ∧
      HasDerivAt (Q.nu p.1) (Q.rUV p.1 p.2) p.2 ∧
      HasDerivAt (Q.xi p.1) (Q.xiV e p.1 p.2) p.2) →
    ContinuousOn yIn (Icc rho Lzero) → ContinuousOn mIn (Icc rho Lzero) →
    (∀ r ∈ Icc rho Lzero, ‖yIn r‖ ≤ Kref ∧ delta ≤ 1 - 2 * mIn r / r ∧
      |1 - 2 * mIn r / r| ≤ Gref) →
    (∀ r ∈ Ioo rho Lzero,
      let k := (2 * mIn r / r - qStar ^ 2 / r ^ 2) / (1 - 2 * mIn r / r)
      HasDerivAt yIn (((-(1 + k) / r : ℝ) : ℂ) * yIn r) r ∧
      HasDerivAt mIn ((1 - 2 * mIn r / r) * ‖yIn r‖ ^ 2 / 2 + qStar ^ 2 / (2 * r ^ 2)) r) →
    yIn Lzero = yOut Lzero → mIn Lzero = mOut Lzero →
    IntervalIntegrable (fun t => ‖P.phi t t - H + P.xi t t / P.nu t t‖ ^ 2) volume a b →
    (∫ t in a..b, ‖P.phi t t - H + P.xi t t / P.nu t t‖ ^ 2) ≤ epsilon ^ 2 / L →
    InnerComparisonData rho Lzero delta c Kref Gref Qmax Cscalar Bcharge Amax
      Q E H yIn mIn (-K) K qStar e eta (Ctheta * (epsilon + eta))
        (Cmass * (epsilon + eta)) (Cxi * (epsilon + eta)) := by
  obtain ⟨Lo, hLo, hout⟩ := outer_outgoing_of_normalization Kstatic hKs
  obtain ⟨Li, hLi, htrace⟩ := incoming_trace_on_inner_maps_of_normalization Kstatic hKs
  refine ⟨max 1 (max Lo Li), zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro Ct hCt δ rStar Lzero c K Ccore hδ hrStar hrStarL hLzero hc hK hCcore
  have hL1 : 1 ≤ Lzero := (le_max_left _ _).trans hLzero
  have hLo' : Lo ≤ Lzero := (le_max_left _ _).trans ((le_max_right _ _).trans hLzero)
  have hLi' : Li ≤ Lzero := (le_max_right _ _).trans ((le_max_right _ _).trans hLzero)
  obtain ⟨CBout, CEout, Cqout, Ctheta, Cmass, hCBout, hCEout, hCqout, hCtheta, hCmass, hout⟩ :=
    hout Ct Ct hCt.le hCt.le
  obtain ⟨CBtrace, CEtrace, Cqtrace, hCBtrace, hCEtrace, hCqtrace, htrace⟩ :=
    htrace Ct Ct hCt.le hCt.le
  obtain ⟨Cxi, hCxi, htrace⟩ := htrace K hK
  obtain ⟨Ca, hCa, habsQ⟩ := inner_charge_constant_of_core_estimate Ccore Lzero hCcore hL1
  let Bcharge := 2 * Ca + max Cqout Cqtrace
  let Amax := 1 / (c * δ * rStar)
  let Cscalar := (2 + 2 / Real.sqrt δ) / Real.sqrt rStar
  let Qmax := Ca + 1
  have hCs : 0 < Cscalar := by dsimp [Cscalar]; positivity
  have hAm : 0 < Amax := by dsimp [Amax]; positivity
  refine ⟨max CBout CBtrace, max CEout CEtrace, max Cqout Cqtrace,
    Ctheta, Cmass, Cxi, Bcharge, Amax, Cscalar, Qmax,
    lt_of_lt_of_le hCBout (le_max_left _ _), lt_of_lt_of_le hCEout (le_max_left _ _),
    lt_of_lt_of_le hCqout (le_max_left _ _), hCtheta, hCmass, hCxi,
    by dsimp [Bcharge]; positivity, hAm, hCs, by dsimp [Qmax]; positivity, ?_⟩
  intro P D H Pzero phiOut yOut yIn mOut mIn a b L epsilon eta qStar e rho delta Kref Gref U V
  dsimp only
  intro ho hsmall hcharge hrho hrhoL hU hUi hUp hVp hboundary himage
    htri hfields heq hdiag hcore hcompact htriInner hfieldsInner hboxInner heqInner
    cyIn cmIn hstaticBox hstaticEq hyMatch hmMatch hgi hgb
  let Q := nullPullback P U V
  let E := {p : ℝ × ℝ | (U p.1,V p.2) ∈ D}
  let R := sidewaysTruncation Q E (-K) K rho Lzero
  have he := ho.errors.1.1
  have heta := ho.errors.2.1
  have hL : 1 ≤ L := hL1.trans ho.ordered
  have hboundSmall (B E : ℝ) (hB : B ≤ max CBout CBtrace) (hE : E ≤ max CEout CEtrace) :
      4 * (B * epsilon + E * eta) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_right hB he) (mul_le_mul_of_nonneg_right hE heta)) (by norm_num)).trans
          hsmall
  have hout' := hout P D H Pzero phiOut yOut mOut a b Lzero L epsilon eta qStar e ho hLo'
    (hboundSmall _ _ (le_max_left _ _) (le_max_left _ _))
    ((mul_le_mul_of_nonneg_right (le_max_left _ _) heta).trans hcharge)
  have htrace' := htrace P D H Pzero phiOut yOut mOut a b Lzero L epsilon eta qStar e U V
    ho hLi' (hboundSmall _ _ (le_max_right _ _) (le_max_right _ _))
    ((mul_le_mul_of_nonneg_right (le_max_right _ _) heta).trans hcharge) hU hUi hUp
    (fun t ht => ⟨(hboundary t ht).1, (hboundary t ht).2.1, (hboundary t ht).2.2.2.1⟩) hgi hgb
  have hpotential := potential_of_core_on_complete_region hδ hrStar hL ho.scale htri hfields heq
      hdiag
    (fun p hp => ⟨(hcore p hp).1, (hcore p hp).2.1, (hcore p hp).2.2.1,
      (hcore p hp).2.2.2.1, (hcore p hp).2.2.2.2.1⟩)
  have hQabs (p) (hp : p ∈ sidewaysTruncation P D a b rStar L) (hr : P.r p.1 p.2 ≤ Lzero) :=
    habsQ (P.r p.1 p.2) (P.m p.1 p.2) (P.Q p.1 p.2) e L eta H
      (hrStar.trans_le hp.2.1) hr (hcore p hp).1 hL heta ho.scale (hcore p hp).2.2.2.2.2.2
  have hKK : -K ≤ K := by linarith only [hK]
  have hzero : (0 : ℝ) ∈ Icc (-K) K := ⟨by linarith only [hK], hK⟩
  have hlev := hboundary 0 hzero
  have hlevel : (U 0,V 0) ∈ sidewaysTruncation P D a b rStar L :=
    sidewaysTruncation_mono_radius P D a b L hrStarL hlev.1
  have hlevelQ := hQabs _ hlevel hlev.2.1.le
  refine { ordered := hKK
           errors := ⟨heta, by positivity, by positivity, by positivity⟩
           compact := hcompact
           boundary_mem := ?_
           triangles := htriInner
           fields := hfieldsInner
           box := hboxInner
           charged := ?_
           scale := ?_
           reference_charge := ho.reference_charge.trans (by dsimp [Qmax]; linarith only [hCa])
           static_continuous := ⟨cyIn, cmIn⟩
           static_bounds := hstaticBox
           static_equations := hstaticEq
           equations := heqInner
           boundary := ?_
           trace := ?_ }
  · intro t ht
    have hb := hboundary t ht
    exact ⟨⟨hb.1.1.1, ht.1, le_rfl, ht.2⟩,
      by change rho ≤ P.r (U t) (V t); rw [hb.2.1]; exact hrhoL,
      by change P.r (U t) (V t) ≤ Lzero; exact hb.2.1.le⟩
  · intro p hp
    have him := himage p hp
    have hcp := hcore _ him
    have hQp := hQabs _ him (show P.r (U p.1) (V p.2) ≤ Lzero from hp.2.2)
    have hsqrt := Real.sqrt_le_sqrt him.2.1
    have hscalar : ‖P.phi (U p.1) (V p.2)‖ ≤ ‖H‖ + Cscalar :=
      hcp.2.2.2.2.2.1.trans (add_le_add le_rfl (div_le_div_of_nonneg_left
        (by positivity : 0 ≤ 2 + 2 / Real.sqrt δ) (Real.sqrt_pos.mpr hrStar) hsqrt))
    have hchargeDiff := inner_charge_difference_of_level_point hQp hlevelQ (hout' _ hlev.1).1
    have huI : p.1 ∈ Icc (-K) K := ⟨hp.1.2.1.trans hp.1.2.2.1,hp.1.2.2.2⟩
    have hdu : 0 ≤ deriv (U : ℝ → ℝ) p.1 := (hUp _).le
    have hderiv := (hboundary p.1 huI).2.2.1
    have hpA := mul_le_mul_of_nonneg_left (hpotential _ him) hdu
    have hpA' : |e * Q.A p.1 p.2| * (1 + ‖H‖) ≤ Amax * eta := by
      calc
        _ = deriv (U : ℝ → ℝ) p.1 * (|e * P.A (U p.1) (V p.2)| * (1 + ‖H‖)) := by
          dsimp only [Q, nullPullback]
          rw [abs_mul, abs_mul, abs_of_nonneg hdu, abs_mul]
          ring
        _ ≤ deriv (U : ℝ → ℝ) p.1 * ((2 / (δ * rStar)) * eta) := hpA
        _ ≤ (1 / (2 * c)) * ((2 / (δ * rStar)) * eta) :=
          mul_le_mul_of_nonneg_right hderiv (by positivity)
        _ = Amax * eta := by dsimp [Amax]; ring
    refine ⟨hscalar, ?_, ?_, hpA'⟩
    · exact hQp.trans ((mul_le_mul_of_nonneg_left ho.errors.2.2 hCa.le).trans
        (by dsimp [Qmax]; linarith))
    · exact hchargeDiff.trans (mul_le_mul_of_nonneg_right
        (by dsimp [Bcharge]; linarith only [le_max_left Cqout Cqtrace]) heta)
  · have hh := mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ |e| * (1 + ‖H‖))
    rw [mul_one] at hh
    exact hh.trans_eq (by rw [← ho.scale]; ring)
  · intro t ht
    have hb := hboundary t ht
    have hy := (nullPullback_ratios P U V
      (hU.differentiable (by norm_num) t).hasDerivAt
      ((differentiableAt_of_deriv_ne_zero (hVp t).ne').hasDerivAt)
      (hUp t).ne' (hVp t).ne').1
    refine ⟨hb.2.1, ?_, ?_⟩
    · change ‖Q.theta t t / Q.lam t t - yIn Lzero‖ ≤ _
      rw [show Q.theta t t / Q.lam t t = P.theta (U t) (V t) / P.lam (U t) (V t) from hy,
        hyMatch, ← hb.2.1]
      exact (hout' _ hb.1).2.1
    · change |P.m (U t) (V t) - mIn Lzero| ≤ _
      rw [hmMatch, ← hb.2.1]
      exact (hout' _ hb.1).2.2
  · rw [hyMatch]
    exact htrace'

end EmcsfAcExtension.Global.Observation
