module

public import EmcsfAcExtension.Global.Observation.InnerTransport
import EmcsfAcExtension.Global.Observation.InnerPotential
import Mathlib

/-! # Ordinary retained potential and individual inner sources

internal project record–F5. Source: charged_SF_new_version.tex:L2602–2608, L2644–2649;
approved internal project record. These helpers are discharged on the actual source chart.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Observation

/-- [internal] Bound the ordinary retained potential by integrating its actual
outgoing constraint from the inner boundary. `C` depends only on the fixed
lower radius, gap, charge bound and ordinary boundary bound. It precedes all
fields, members, outer scales, backgrounds, couplings and errors. The exact
outer scale identity gives the sharper charged bound with `eta / L`. -/
theorem inner_ordinary_potential_of_normalization
    (rStar delta Qmax Aouter : ℝ) (hrStar : 0 < rStar) (hdelta : 0 < delta)
    (hQmax : 0 ≤ Qmax) (hAouter : 0 ≤ Aouter) :
    ∃ C > 0, ∀ (rho Lzero c K G Cscalar Bcharge Amax : ℝ)
      (S : Fields) (D : Set (ℝ × ℝ)) (H : ℂ)
      (yStar : ℝ → ℂ) (mStar : ℝ → ℝ) (a b qStar e eta etheta em exi L : ℝ),
    rStar ≤ rho → 0 < c → 0 < L →
    InnerComparisonData rho Lzero delta c K G Qmax Cscalar Bcharge Amax
      S D H yStar mStar a b qStar e eta etheta em exi →
    (∀ t ∈ Icc a b, |S.A t t| ≤ Aouter) →
    (∀ p ∈ sidewaysTruncation S D a b rho Lzero,
      HasDerivAt (S.A p.1) (S.AV p.1 p.2) p.2) →
    |e| * L * (1 + ‖H‖) = eta →
    ∀ p ∈ sidewaysTruncation S D a b rho Lzero,
      |S.A p.1 p.2| ≤ C ∧ |e * S.A p.1 p.2| * (1 + ‖H‖) ≤ C * eta / L := by
  let C := Aouter + Qmax / (delta * rStar) + 1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro rho Lzero c K G Cscalar Bcharge Amax S D H yStar mStar a b qStar e eta
    etheta em exi L hrho hc hL h hboundary heq hscale p hp
  let R := sidewaysTruncation S D a b rho Lzero
  let B : Fields := { S with A := fun u v => S.A u v - S.A u u }
  have hsec {E : Type} [TopologicalSpace E] {f : ℝ → ℝ → E}
      (hf : ContinuousOn (Function.uncurry f) R) :=
    continuousOn_outgoing_of_subtriangle hf (h.triangles p hp)
  have hpath (t) (ht : t ∈ Icc p.2 p.1) :=
    h.triangles p hp (sidewaysTriangle_outgoing ht)
  rcases h.fields with ⟨cr, cn, cl, ca, cp, ct, cm, cq, cx⟩
  have hA := potential_on_outgoing_of_mass_charge_bounds delta Qmax hdelta hQmax B
    hp.1.2.2.1 (hsec cr) (hsec cl) ((hsec ca).sub continuousOn_const)
    (hsec cn) (hsec cq) (hsec cm)
    (fun t ht => (h.equations _ (hpath t (Ioo_subset_Icc_self ht))).2.1)
    (fun t ht => (heq _ (hpath t (Ioo_subset_Icc_self ht))).sub_const (S.A p.1 p.1))
    (sub_self _)
    (fun t ht => by
      have hb := h.box _ (hpath t ht)
      refine ⟨hrStar.trans_le (hrho.trans (hpath t ht).2.1), hc.le.trans hb.2.1.1,
        ?_, (h.charged _ (hpath t ht)).2.1, hb.2.2.2⟩
      exact abs_le.mpr ⟨by linarith only [hb.1.2], by linarith only [hb.1.1, hc]⟩)
  have hbound : |S.A p.1 p.2| ≤ C := by
    have hb := hboundary p.1 ⟨hp.1.2.1.trans hp.1.2.2.1, hp.1.2.2.2⟩
    have hden := mul_le_mul_of_nonneg_left (hrho.trans hp.2.1) hdelta.le
    have hfrac := div_le_div_of_nonneg_left hQmax (mul_pos hdelta hrStar) hden
    have ha : |S.A p.1 p.2| ≤ |S.A p.1 p.2 - S.A p.1 p.1| + |S.A p.1 p.1| := by
      simpa only [sub_add_cancel] using abs_add_le (S.A p.1 p.2 - S.A p.1 p.1) (S.A p.1 p.1)
    change |S.A p.1 p.2 - S.A p.1 p.1| ≤ _ at hA
    dsimp only [C]
    linarith only [ha, hb, hA, hfrac]
  refine ⟨hbound, ?_⟩
  calc
    _ = (|e| * (1 + ‖H‖)) * |S.A p.1 p.2| := by rw [abs_mul]; ring
    _ ≤ (|e| * (1 + ‖H‖)) * C := mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = C * eta / L := by rw [← hscale]; field_simp

/-- [internal] Expose the geometric coefficient difference and the combined
and individual electric/potential sources. `Cg,Ce` depend only on the displayed
fixed annular, reference and primitive bounds, before every member, field,
background, coupling, scale and error. No scalar stop is needed. -/
theorem inner_individual_sources_of_normalization
    (rStar delta K Qmax Cscalar Bcharge Amax : ℝ)
    (hrStar : 0 < rStar) (hdelta : 0 < delta) (hK : 0 ≤ K)
    (hQmax : 0 ≤ Qmax) (hCs : 0 ≤ Cscalar) (hBq : 0 ≤ Bcharge) (hAm : 0 ≤ Amax) :
    ∃ Cg Ce : ℝ, 0 < Cg ∧ 0 < Ce ∧
    ∀ (rho Lzero c G : ℝ) (S : Fields) (D : Set (ℝ × ℝ)) (H : ℂ)
      (yStar : ℝ → ℂ) (mStar : ℝ → ℝ) (a b qStar e eta etheta em exi : ℝ),
    rStar ≤ rho → InnerComparisonData rho Lzero delta c K G Qmax Cscalar Bcharge Amax
      S D H yStar mStar a b qStar e eta etheta em exi →
    ∀ p ∈ sidewaysTruncation S D a b rho Lzero,
      let r := S.r p.1 p.2
      let k := (S.mu p.1 p.2 - S.Q p.1 p.2 ^ 2 / r ^ 2) / (1 - S.mu p.1 p.2)
      let ks := (2 * mStar r / r - qStar ^ 2 / r ^ 2) / (1 - 2 * mStar r / r)
      let electric := I * e * S.Q p.1 p.2 * S.phi p.1 p.2 / ((1 - S.mu p.1 p.2) * r : ℝ)
      let potential := I * e * S.A p.1 p.2 * yStar r
      |k - ks| ≤ Cg * (|massComparison S mStar p.1 p.2| + eta) ∧
      ‖electric‖ + ‖potential‖ ≤ Ce * eta ∧
      ‖electric‖ ≤ Ce * eta ∧ ‖potential‖ ≤ Ce * eta := by
  obtain ⟨Cg, hCg, hgeo⟩ := inner_geometric_source_bound rStar delta Qmax Bcharge
    hrStar hdelta hQmax hBq
  obtain ⟨Ce, hCe, hcharged⟩ := inner_charged_source_bound rStar delta Qmax Cscalar K Amax
    hrStar hdelta hQmax hCs hK hAm
  refine ⟨Cg, Ce, hCg, hCe, ?_⟩
  intro rho Lzero c G S D H yStar mStar a b qStar e eta etheta em exi hrho h p hp
  dsimp only
  have hst := h.static_bounds (S.r p.1 p.2) hp.2
  have hq := h.charged p hp
  have hdif := hgeo (S.r p.1 p.2) (S.m p.1 p.2) (mStar (S.r p.1 p.2))
    (S.Q p.1 p.2) qStar eta (hrho.trans hp.2.1) h.errors.1
    (h.box p hp).2.2.2 hst.2.1 hq.2.1 h.reference_charge hq.2.2.1
  have hsrc := hcharged (S.r p.1 p.2) 1 (1 - S.mu p.1 p.2) (S.Q p.1 p.2) e eta
    (S.A p.1 p.2) H (S.phi p.1 p.2) (yStar (S.r p.1 p.2))
    (hrho.trans hp.2.1) le_rfl (h.box p hp).2.2.2 h.errors.1 hq.2.1 hq.1 hst.1
    (by simpa only [mul_one] using h.scale) hq.2.2.2
  refine ⟨?_, hsrc, ?_, ?_⟩
  · simpa only [Fields.mu, massComparison] using hdif
  · exact (le_add_of_nonneg_right (norm_nonneg _)).trans hsrc
  · exact (le_add_of_nonneg_left (norm_nonneg _)).trans hsrc

end EmcsfAcExtension.Global.Observation
