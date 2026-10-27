module

public import EmcsfAcExtension.Global.Observation.InnerClosure
import EmcsfAcExtension.Global.Observation.InnerMass
import Mathlib

/-! # All inner estimates after construction of the actual inner record

The physical-source export constructs the record and its four charged controls,
outer errors and incoming clock trace. Source: charged_SF_new_version.tex:L2602–2735.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Observation

/-- [internal] All inner source, transport, Volterra and closed comparison
conclusions. No part of this predicate is used as a source hypothesis. -/
@[expose] noncomputable def innerConclusions (_rStar Lzero _delta _c _K _G Qmax Cscalar Bcharge Amax
    A B E Cm Cz Cv Cclose _sigma Ctheta Cmass Cxi : ℝ)
    (rho : ℝ) (S : Fields) (D : Set (ℝ × ℝ)) (H : ℂ)
    (yStar : ℝ → ℂ) (mStar : ℝ → ℝ) (a b qStar e epsilon eta : ℝ) : Prop :=
  let R := sidewaysTruncation S D a b rho Lzero
  let Y := fun u v => S.theta u v / (S.lam u v : ℂ) - yStar (S.r u v)
  let Z := fun u v => S.xi u v / (S.nu u v : ℂ) - yStar (S.r u v)
  let F := fun d => sSup ((fun p : ℝ × ℝ => ‖Y p.1 p.2‖) ''
    sidewaysTruncation S D a b (Lzero - d) Lzero)
  let N := fun d => sSup ((fun p : ℝ × ℝ => ‖massComparison S mStar p.1 p.2‖) ''
    sidewaysTruncation S D a b (Lzero - d) Lzero)
  (∀ p ∈ R, ‖S.phi p.1 p.2‖ ≤ ‖H‖ + Cscalar ∧ |S.Q p.1 p.2| ≤ Qmax ∧
    |S.Q p.1 p.2 - qStar| ≤ Bcharge * eta ∧ |e * S.A p.1 p.2| * (1 + ‖H‖) ≤ Amax * eta) ∧
  (∀ p ∈ sidewaysTruncation S D a b rho Lzero,
      let r := S.r p.1 p.2
      let Y := S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ) - yStar r
      let Z := S.xi p.1 p.2 / (S.nu p.1 p.2 : ℂ) - yStar r
      let k := (S.mu p.1 p.2 - S.Q p.1 p.2 ^ 2 / r ^ 2) / (1 - S.mu p.1 p.2)
      let ks := (2 * mStar r / r - qStar ^ 2 / r ^ 2) / (1 - 2 * mStar r / r)
      let electric := I * e * S.Q p.1 p.2 * S.phi p.1 p.2 / ((1 - S.mu p.1 p.2) * r : ℝ)
      let potential := I * e * S.A p.1 p.2 * yStar r
      |k / r| ≤ A ∧
      ‖-((1 / r : ℝ) : ℂ) * Y - (((k - ks) / r : ℝ) : ℂ) * yStar r + electric‖ ≤
        B * (‖Y‖ + |massComparison S mStar p.1 p.2| + eta) ∧
      ‖((-S.nu p.1 p.2 : ℝ) : ℂ) *
        (((1 / r : ℝ) : ℂ) * Z + ((k / r : ℝ) : ℂ) * Y +
          (((k - ks) / r : ℝ) : ℂ) * yStar r + electric) - potential‖ ≤
        (-S.nu p.1 p.2) * B * (‖Z‖ + ‖Y‖ + |massComparison S mStar p.1 p.2| + eta) ∧
      |(S.Q p.1 p.2 ^ 2 - qStar ^ 2) / (2 * r ^ 2)| ≤ E * eta) ∧
  (∀ v x y : ℝ, ‖Complex.exp (I * ((∫ u in x..y, e * S.A u v : ℝ) : ℂ))‖ = 1) ∧
  (∀ d ∈ Icc 0 (Lzero - rho), (∀ s ∈ Icc 0 d, F s ≤ 1) →
    N d ≤ Cm * (Cmass * (epsilon + eta)) + Cm * eta + Cm * ∫ s in 0..d, F s) ∧
  (∀ p ∈ R, ‖Z p.1 p.2‖ ≤ Cz * ‖S.xi p.1 p.1 / S.nu p.1 p.1 - yStar Lzero‖ +
    Cz * eta + Cz * ∫ s in 0..(Lzero - S.r p.1 p.2), F s + N s) ∧
  (F 0 ≤ Cv * (Ctheta * (epsilon + eta) + Cmass * (epsilon + eta) + Cxi * (epsilon + eta) + eta) ∧
    ∀ d ∈ Icc 0 (Lzero - rho), (∀ s ∈ Icc 0 d, F s ≤ 1) →
      F d + N d ≤ Cv * (Ctheta * (epsilon + eta) + Cmass * (epsilon + eta) + Cxi * (epsilon + eta) +
          eta) +
        Cv * ∫ s in 0..d, F s + N s) ∧
  ((∀ d ∈ Icc 0 (Lzero - rho), F d + N d ≤ Cclose * (epsilon + eta) ∧ F d < 1) ∧
    ∀ p ∈ R, ‖Y p.1 p.2‖ + |massComparison S mStar p.1 p.2| ≤ Cclose * (epsilon + eta))

/-- [internal] Derive every inner estimate from the completed record.
All positive coefficients and the tolerance depend only on the displayed
fixed annulus, primitive/reference bounds and outer error coefficients,
before the stopping member, fields, coupling, background and errors. -/
theorem inner_conclusions_of_normalization
    (rStar Lzero delta c K G Qmax Cscalar Bcharge Amax Ctheta Cmass Cxi : ℝ)
    (hrStar : 0 < rStar) (hLzero : rStar ≤ Lzero) (hdelta : 0 < delta) (hc : 0 < c)
    (hK : 0 ≤ K) (hG : 0 ≤ G) (hQmax : 0 ≤ Qmax) (hCs : 0 ≤ Cscalar)
    (hBq : 0 ≤ Bcharge) (hAm : 0 ≤ Amax) (hCt : 0 ≤ Ctheta) (hCm : 0 ≤ Cmass) (hCx : 0 ≤ Cxi) :
    ∃ A B E Cm Cz Cv Cclose sigma : ℝ,
      0 < A ∧ 0 < B ∧ 0 < E ∧ 0 < Cm ∧ 0 < Cz ∧ 0 < Cv ∧ 0 < Cclose ∧ 0 < sigma ∧
    ∀ (rho : ℝ) (S : Fields) (D : Set (ℝ × ℝ)) (H : ℂ)
      (yStar : ℝ → ℂ) (mStar : ℝ → ℝ) (a b qStar e epsilon eta : ℝ),
    rStar ≤ rho → rho ≤ Lzero → 0 ≤ epsilon →
    InnerComparisonData rho Lzero delta c K G Qmax Cscalar Bcharge Amax
      S D H yStar mStar a b qStar e eta (Ctheta * (epsilon + eta))
        (Cmass * (epsilon + eta)) (Cxi * (epsilon + eta)) →
    epsilon + eta ≤ sigma →
    innerConclusions rStar Lzero delta c K G Qmax Cscalar Bcharge Amax
      A B E Cm Cz Cv Cclose sigma Ctheta Cmass Cxi rho S D H yStar mStar a b qStar e epsilon eta :=
          by
  obtain ⟨A, B, E, hA, hB, hE, hsources⟩ := inner_sources_of_normalization
    rStar delta c K Qmax Cscalar Bcharge Amax hrStar hdelta hc hK hQmax hCs hBq hAm
  obtain ⟨Cm, hCm', hmass⟩ := inner_mass_volterra_of_charge_bound rStar Lzero K G E hrStar hLzero hK
      hG hE.le
  obtain ⟨Cz, hCz, hincoming⟩ := inner_incoming_transport_of_normalization
    (G := G) hrStar hLzero hdelta hc hK hQmax hCs hBq hAm
  obtain ⟨Cv, hCv, hcoupled⟩ := inner_coupled_volterra_of_normalization
    hrStar hLzero hdelta hc hK hG hQmax hCs hBq hAm
  obtain ⟨Cclose, hCclose, sigma, hsigma, hclose⟩ := inner_comparison_closure_of_normalization
    hrStar hLzero hdelta hc hK hG hQmax hCs hBq hAm Ctheta Cmass Cxi hCt hCm hCx
  refine ⟨A, B, E, Cm, Cz, Cv, Cclose, sigma, hA, hB, hE, hCm', hCz, hCv, hCclose, hsigma, ?_⟩
  intro rho S D H yStar mStar a b qStar e epsilon eta hrho hrhoL hepsilon h hsmall
  have sources := hsources rho Lzero G S D H yStar mStar a b qStar e eta
    (Ctheta * (epsilon + eta)) (Cmass * (epsilon + eta)) (Cxi * (epsilon + eta)) hrho h
  refine ⟨h.charged, sources, ?_, ?_,
    hincoming rho S D H yStar mStar a b qStar e eta
      (Ctheta * (epsilon + eta)) (Cmass * (epsilon + eta)) (Cxi * (epsilon + eta)) hrho hrhoL h,
    hcoupled rho S D H yStar mStar a b qStar e eta
      (Ctheta * (epsilon + eta)) (Cmass * (epsilon + eta)) (Cxi * (epsilon + eta)) hrho hrhoL h,
    hclose rho S D H yStar mStar a b qStar e epsilon eta hrho hrhoL hepsilon h hsmall⟩
  · intro v x y
    rw [Complex.norm_exp]
    simp
  · intro d hd hstop
    rcases h.fields with ⟨cr, cn, cl, ca, cp, ct, cm, cq, cx⟩
    apply hmass rho S D yStar mStar a b qStar eta (Cmass * (epsilon + eta)) d
      hrho hrhoL h.errors.1 h.errors.2.2.1 hd h.compact cr cl ct cm cq
      h.static_continuous.1 h.static_continuous.2
      (fun s hs => (h.static_equations s hs).2)
      ⟨(a,a), h.boundary_mem a ⟨le_rfl,h.ordered⟩, (h.boundary a ⟨le_rfl,h.ordered⟩).1⟩
      h.triangles (fun p hp => (h.equations p hp).1)
      (fun p hp => by linarith only [(h.box p hp).1.1, hc])
      (fun p hp => ⟨(h.equations p hp).2.1, (h.equations p hp).2.2.1⟩)
      (fun p hp => ⟨hc.trans_le (h.box p hp).2.1.1,
        (h.static_bounds (S.r p.1 p.2) hp.2).1,
        (h.static_bounds (S.r p.1 p.2) hp.2).2.2, (sources p hp).2.2.2⟩)
      (fun t ht => by
        have hb := h.boundary t ⟨ht.1.2.1, ht.1.2.2.2⟩
        refine ⟨hb.1, ?_⟩
        simpa only [massComparison, hb.1] using hb.2.2) hstop

end EmcsfAcExtension.Global.Observation
