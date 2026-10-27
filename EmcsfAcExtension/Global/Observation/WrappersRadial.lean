module

public import EmcsfAcExtension.Global.Observation.WrappersExact
import EmcsfAcExtension.Global.Observation.OuterMass
import Mathlib

/-! # Radial identities on actual normalized outgoing sections

Radius inverses, scalar energy, Maxwell integration by parts and the backward
mass weight are derived on the same complete triangle. No arbitrary radial
profile is an input to the source export. Source: charged_SF_new_version.tex:L2359–2512.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Observation

/-- [internal] Maxwell's identity and the weighted energy on an actual section.
The radius inverse is returned together with its field identifications. This
predicate is only a conclusion, never an additional source hypothesis. -/
@[expose] noncomputable def outerRadial (S : Fields) (D : Set (ℝ × ℝ)) (H : ℂ)
    (a b Lzero L e : ℝ) : Prop :=
  ∀ p ∈ sidewaysTruncation S D a b Lzero L,
    ∃ inv : ℝ → ℝ,
    let r := S.r p.1 p.2
    let phi := fun s => S.phi p.1 (inv s)
    let y := fun s => S.theta p.1 (inv s) / (S.lam p.1 (inv s) : ℂ)
    let Q := fun s => S.Q p.1 (inv s)
    let psi := fun s : ℝ => (s : ℂ) * (phi s - H)
    Continuous inv ∧ (∀ s, inv s ∈ Icc p.2 p.1) ∧
    (∀ s ∈ Icc r L, S.r p.1 (inv s) = s) ∧ inv r = p.2 ∧ inv L = p.1 ∧
    ContinuousOn Q (Icc r L) ∧
    (∫ s in r..L, ‖y s‖ ^ 2) ≤ 8 ∧
    Q r = Q L + e *
      (starRingEnd ℂ H * ((L : ℂ) * psi L - (r : ℂ) * psi r - 2 * ∫ s in r..L, psi s) +
        ∫ s in r..L, starRingEnd ℂ (psi s) * deriv psi s).im ∧
    (∫ s in r..L, ‖y s‖ ^ 2 / s) ≤ 8 / Lzero ∧
    ∀ s ∈ Icc r L,
      Real.exp (∫ t in r..s, ‖y t‖ ^ 2 / t) ≤ Real.exp (8 / Lzero)

/-- [internal] Produce the radial Maxwell identity and weighted mass integral
from normalized fields. The numerical energy coefficient `8` is universal. -/
theorem outer_radial_of_normalization
    {Kstatic Ct Bboundary a b Lzero L epsilon eta qStar e : ℝ}
    {S : Fields} {D : Set (ℝ × ℝ)} {H P : ℂ}
    {phiStar yStar : ℝ → ℂ} {mStar : ℝ → ℝ}
    (hLzero : 0 < Lzero)
    (h : OuterNormalizationData Kstatic Ct Bboundary S D H P phiStar yStar mStar
      a b Lzero L epsilon eta qStar e) : outerRadial S D H a b Lzero L e := by
  intro p hp
  let R := sidewaysTruncation S D a b Lzero L
  have path := (sidewaysTruncation_paths (h.triangles p hp)).2
  have sec {E : Type} [TopologicalSpace E] {f : ℝ → ℝ → E}
      (hc : ContinuousOn (Function.uncurry f) R) : ContinuousOn (f p.1) (Icc p.2 p.1) :=
    continuousOn_outgoing_of_subtriangle hc (h.triangles p hp)
  have hr : 0 < S.r p.1 p.2 := hLzero.trans_le hp.2.1
  have hd (t) (ht : t ∈ Ioo p.2 p.1) := h.equations (p.1,t) (path t (Ioo_subset_Icc_self ht))
  have hl (t) (ht : t ∈ Icc p.2 p.1) : 0 < S.lam p.1 t :=
    (by norm_num : (0 : ℝ) < 1 / 8).trans_le (h.box (p.1,t) (path t ht)).2.1.1
  rcases h.fields with ⟨cr, cn, cl, cA, cp, ct, cm, cQ⟩
  obtain ⟨inv, hrL, ci, mem, rad, left, right, di, cy, _cm, cq, _dm, _ac, _box, energy⟩ :=
    outgoing_radial_mass_data_of_normalization S hp.1.2.2.1 hr
      (h.boundary p.1 (path p.1 ⟨hp.1.2.2.1, le_rfl⟩)).1
      (sec cr) (sec cl) (sec ct) (sec cm) (sec cQ)
      (fun t ht => (hd t ht).2.1) (fun t ht => (hd t ht).2.2.1)
      (fun t ht => ⟨hl t ht, (h.box (p.1,t) (path t ht)).2.2⟩)
  let phi := fun s => S.phi p.1 (inv s)
  let y := fun s => S.theta p.1 (inv s) / (S.lam p.1 (inv s) : ℂ)
  let Q := fun s => S.Q p.1 (inv s)
  have cphi : ContinuousOn phi (Icc (S.r p.1 p.2) L) :=
    (sec cp).comp ci.continuousOn (fun s _ => mem s)
  have dphi (s) (hs : s ∈ Ioo (S.r p.1 p.2) L) :
      HasDerivAt phi (y s / (s : ℂ)) s := by
    convert ((hd (inv s) (di s hs).1).2.2.2.1).scomp s (di s hs).2 using 1
    · rfl
    · dsimp only [Fields.phiV, y]
      simp only [real_smul, Complex.ofReal_inv]
      rw [rad s (Ioo_subset_Icc_self hs)]
      ring
  have dQ (s) (hs : s ∈ Ioo (S.r p.1 p.2) L) :
      HasDerivAt Q (-e * (s * (starRingEnd ℂ (phi s) * y s).im)) s := by
    convert ((hd (inv s) (di s hs).1).2.2.2.2.1).scomp s (di s hs).2 using 1
    · rfl
    · dsimp only [Fields.QV, phi, y]
      rw [rad s (Ioo_subset_Icc_self hs)]
      simp only [smul_eq_mul, ← mul_div_assoc, Complex.div_im,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, normSq_ofReal]
      field_simp [(hl (inv s) (mem s)).ne']
      ring
  have cweight : ContinuousOn (fun s => ‖y s‖ ^ 2 / s) (Icc (S.r p.1 p.2) L) :=
    (cy.norm.pow 2).div continuousOn_id (fun s hs => (hr.trans_le hs.1).ne')
  have weighted : (∫ s in (S.r p.1 p.2)..L, ‖y s‖ ^ 2 / s) ≤ 8 / Lzero := by
    calc
      _ ≤ ∫ s in (S.r p.1 p.2)..L, ‖y s‖ ^ 2 / Lzero :=
        intervalIntegral.integral_mono_on hrL (cweight.intervalIntegrable_of_Icc hrL)
          ((cy.norm.pow 2).intervalIntegrable_of_Icc hrL |>.div_const Lzero)
          (fun s hs => div_le_div_of_nonneg_left (sq_nonneg _) hLzero (hp.2.1.trans hs.1))
      _ = (∫ s in (S.r p.1 p.2)..L, ‖y s‖ ^ 2) / Lzero := by
        rw [intervalIntegral.integral_div]
      _ ≤ 8 / Lzero := div_le_div_of_nonneg_right energy hLzero.le
  refine ⟨inv, ci, mem, rad, left, right, cq, energy,
    co_maxwell_ibp_of_normalization e _ L H phi y Q hr hrL cphi cy cq dphi dQ,
    weighted, ?_⟩
  intro s hs
  exact (backward_mass_integrating_factor_of_normalization hr hrL cy energy s hs).trans
    (Real.exp_le_exp.mpr (div_le_div_of_nonneg_left (by norm_num) hLzero hp.2.1))

/-- [internal] The electric mass integral with the actual charge profile and
its actual radial Jacobian. Used only as a source-wrapper conclusion. -/
@[expose] noncomputable def outerElectricMass (S : Fields) (D : Set (ℝ × ℝ))
    (a b Lzero L qStar eta B C : ℝ) : Prop :=
  ∀ p ∈ sidewaysTruncation S D a b Lzero L, ∃ inv : ℝ → ℝ,
    (∀ s, inv s ∈ Icc p.2 p.1) ∧
    (∀ s ∈ Icc (S.r p.1 p.2) L, S.r p.1 (inv s) = s) ∧
    inv (S.r p.1 p.2) = p.2 ∧ inv L = p.1 ∧
    (∫ s in (S.r p.1 p.2)..L, |S.Q p.1 (inv s) ^ 2 - qStar ^ 2| / s ^ 2) ≤ C * B * eta / Lzero

/-- [internal] Specialize the electric mass integral after the proved charge
improvement. The universal coefficient precedes all data and charge constants. -/
theorem outer_electric_mass_of_normalization :
    ∃ C > 0, ∀ (Kstatic Ct Bboundary a b Lzero L epsilon eta qStar e B : ℝ)
      (S : Fields) (D : Set (ℝ × ℝ)) (H P : ℂ)
      (phiStar yStar : ℝ → ℂ) (mStar : ℝ → ℝ),
    0 < Lzero → 0 ≤ B →
    OuterNormalizationData Kstatic Ct Bboundary S D H P phiStar yStar mStar
      a b Lzero L epsilon eta qStar e →
    (∀ p ∈ sidewaysTruncation S D a b Lzero L,
      |S.Q p.1 p.2| ≤ 2 ∧ |S.Q p.1 p.2 - qStar| ≤ B * eta) →
    outerElectricMass S D a b Lzero L qStar eta B C := by
  obtain ⟨C, hC, hbound⟩ := co_electric_mass_error
  refine ⟨C, hC, ?_⟩
  intro Kstatic Ct Bboundary a b Lzero L epsilon eta qStar e B S D H P phiStar yStar mStar
    hLzero hB h hcharge p hp
  obtain ⟨inv, _ci, mem, rad, left, right, cq, _energy, _maxwell, _weight, _factor⟩ :=
    outer_radial_of_normalization hLzero h p hp
  refine ⟨inv, mem, rad, left, right, ?_⟩
  have hr : 0 < S.r p.1 p.2 := hLzero.trans_le hp.2.1
  have hh := hbound (S.r p.1 p.2) L B eta qStar (fun s => S.Q p.1 (inv s))
    hr hp.2.2 hB h.errors.2.1 h.reference_charge cq
    (fun s hs => hcharge (p.1,inv s) ((sidewaysTruncation_paths (h.triangles p hp)).2 _ (mem s)))
  have heta := h.errors.2.1
  exact hh.trans (div_le_div_of_nonneg_left (by positivity) hLzero hp.2.1)

end EmcsfAcExtension.Global.Observation
