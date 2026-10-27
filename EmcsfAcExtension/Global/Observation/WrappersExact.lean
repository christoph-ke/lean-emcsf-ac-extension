module

public import EmcsfAcExtension.Global.Observation.IncomingTransfer
import EmcsfAcExtension.Global.Observation.OuterMass
import Mathlib

/-! # Exact identities on the constructed observation chart

The source consumer in `WrappersOuter` constructs the normalization record.
These internal lemmas extract the actual derivatives, including their boundary
traces, without assuming a comparison equation. Source: charged_SF_new_version.tex:L2359–2512.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Observation

/-- [internal] The literal outgoing derivative of the scalar comparison. -/
@[expose] noncomputable def outerWv (S : Fields) (H : ℂ) (phiStar yStar : ℝ → ℂ) (u v : ℝ) : ℂ :=
  (S.lam u v : ℂ) * (S.phi u v - H - (phiStar (S.r u v) + yStar (S.r u v))) + S.theta u v

/-- [internal] The full retained-background source in the covariant comparison equation. -/
@[expose] noncomputable def outerWaveSource (S : Fields) (H : ℂ) (phiStar yStar : ℝ → ℂ)
    (mStar : ℝ → ℝ) (qStar e u v : ℝ) : ℂ :=
  let r := S.r u v
  let k := (S.mu u v - S.Q u v ^ 2 / r ^ 2) / (1 - S.mu u v)
  let ks := (2 * mStar r / r - qStar ^ 2 / r ^ 2) / (1 - 2 * mStar r / r)
  (-(((-S.nu u v) * S.lam u v * k / r ^ 2 : ℝ) : ℂ) * scalarComparison S H phiStar u v +
    (((-S.nu u v) * S.lam u v / r : ℝ) : ℂ) * yStar r * ((k - ks : ℝ) : ℂ) -
    I * ((e * S.A u v * S.lam u v : ℝ) : ℂ) * (H + (phiStar r + yStar r)) +
    I * ((e * (-S.nu u v) * S.lam u v * S.Q u v /
      ((1 - S.mu u v) * r ^ 2) : ℝ) : ℂ) * (shiftedRphi S H u v + (r : ℂ) * H))

/-- [internal] Exact outgoing and mixed derivatives, boundary data and unitary phase.
This predicate is used only as a conclusion of the source-setting wrapper. -/
@[expose] noncomputable def outerExact (S : Fields) (D : Set (ℝ × ℝ)) (H : ℂ)
    (phiStar yStar : ℝ → ℂ) (mStar : ℝ → ℝ)
    (a b Lzero L epsilon qStar e Ct : ℝ) : Prop :=
  let R := sidewaysTruncation S D a b Lzero L
  (∀ p ∈ R,
    HasDerivAt (shiftedRphi S H p.1)
      ((S.lam p.1 p.2 : ℂ) * (S.phi p.1 p.2 - H) + S.theta p.1 p.2) p.2 ∧
    HasDerivAt (scalarComparison S H phiStar p.1) (outerWv S H phiStar yStar p.1 p.2) p.2 ∧
    HasDerivAt (fun u => (S.lam u p.2 : ℂ) * (S.phi u p.2 - H) + S.theta u p.2)
      (-(((-S.nu p.1 p.2) * S.lam p.1 p.2 / S.r p.1 p.2 ^ 2 *
        ((S.mu p.1 p.2 - S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2) /
          (1 - S.mu p.1 p.2)) : ℝ) : ℂ) * shiftedRphi S H p.1 p.2 -
      I * e * S.A p.1 p.2 * ((S.lam p.1 p.2 : ℂ) * (S.phi p.1 p.2 - H) +
        S.theta p.1 p.2 + S.lam p.1 p.2 * H) +
      I * e * (-S.nu p.1 p.2) * S.lam p.1 p.2 * S.Q p.1 p.2 /
        ((1 - S.mu p.1 p.2 : ℝ) * S.r p.1 p.2 ^ 2 : ℝ) *
          (shiftedRphi S H p.1 p.2 + S.r p.1 p.2 * H)) p.1 ∧
    HasDerivAt (fun u => outerWv S H phiStar yStar u p.2)
      (outerWaveSource S H phiStar yStar mStar qStar e p.1 p.2 -
        I * e * S.A p.1 p.2 * outerWv S H phiStar yStar p.1 p.2) p.1 ∧
    let r := S.r p.1 p.2
    let y := S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ)
    let Y := y - yStar r
    HasDerivAt (massComparison S mStar p.1)
      (-(S.lam p.1 p.2 / r) * ‖y‖ ^ 2 * massComparison S mStar p.1 p.2 +
        S.lam p.1 p.2 * (S.Q p.1 p.2 ^ 2 - qStar ^ 2) / (2 * r ^ 2) +
        S.lam p.1 p.2 * (1 - 2 * mStar r / r) * (starRingEnd ℂ (yStar r) * Y).re +
        S.lam p.1 p.2 * (1 - 2 * mStar r / r) / 2 * ‖Y‖ ^ 2) p.2) ∧
  (∀ t, (t,t) ∈ R → ‖scalarComparison S H phiStar t t‖ ≤ Ct * epsilon ∧
    deriv (scalarComparison S H phiStar t) t = (S.a t t - H) / 2 ∧
    ‖deriv (scalarComparison S H phiStar t) t‖ ≤ epsilon / (2 * L)) ∧
  ∀ (v x y : ℝ),
    ‖Complex.exp (I * ((∫ u in x..y, e * S.A u v : ℝ) : ℂ))‖ = 1

/-- [internal] Discharge every derivative and boundary input of `outerExact`
from the complete normalization record. There are no selected constants. -/
theorem outer_exact_of_normalization
    {Kstatic Ct Bboundary a b Lzero L epsilon eta qStar e : ℝ}
    {S : Fields} {D : Set (ℝ × ℝ)} {H P : ℂ}
    {phiStar yStar : ℝ → ℂ} {mStar : ℝ → ℝ}
    (hLzero : 0 < Lzero)
    (h : OuterNormalizationData Kstatic Ct Bboundary S D H P phiStar yStar mStar
      a b Lzero L epsilon eta qStar e) :
    outerExact S D H phiStar yStar mStar a b Lzero L epsilon qStar e Ct := by
  have hr (p) (hp : p ∈ sidewaysTruncation S D a b Lzero L) : S.r p.1 p.2 ≠ 0 :=
    (hLzero.trans_le hp.2.1).ne'
  have hl (p) (hp : p ∈ sidewaysTruncation S D a b Lzero L) : S.lam p.1 p.2 ≠ 0 :=
    ((by norm_num : (0 : ℝ) < 1 / 8).trans_le (h.box p hp).2.1.1).ne'
  have hg (p) (hp : p ∈ sidewaysTruncation S D a b Lzero L) : 1 - S.mu p.1 p.2 ≠ 0 := by
    linarith only [(h.box p hp).2.2.2]
  have hd (p) (hp : p ∈ sidewaysTruncation S D a b Lzero L) :=
    scalar_comparison_out_deriv_of_normalization (H := H) phiStar yStar (hr p hp)
      (h.equations p hp).2.1 (h.equations p hp).2.2.2.1
      (h.static_equations (S.r p.1 p.2) hp.2).1
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    have he := h.equations p hp
    have hs := h.static_equations (S.r p.1 p.2) hp.2
    refine ⟨shifted_rphi_out_deriv_of_normalization (hr p hp) he.2.1 he.2.2.2.1,
      hd p hp, co_shifted_wave_of_normalization H (hr p hp) (hg p hp)
        he.2.2.2.2.2.2.1 he.2.2.2.2.2.2.2.1 he.2.2.2.2.2.2.2.2, ?_, ?_⟩
    · simpa only [outerWv, outerWaveSource, Complex.ofReal_mul, Complex.ofReal_sub,
        Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_neg, mul_assoc, mul_div_assoc] using
        co_wv_exact_of_normalization H phiStar yStar (hr p hp) he.1
          he.2.2.2.2.2.2.1 he.2.2.2.2.2.2.2.1 he.2.2.2.2.2.2.2.2 hs.2.1
    · exact co_mass_difference_of_normalization mStar yStar (hr p hp) (hl p hp)
        he.2.1 he.2.2.1 hs.2.2
  · intro t ht
    have hb := h.boundary t ht
    have hh := outer_boundary_difference_data_of_normalization S H P phiStar yStar
      (hLzero.trans_le h.ordered) hb.1 hb.2.1 h.static_boundary.1 h.static_boundary.2
      hb.2.2.1 hb.2.2.2.1
    have hid : deriv (scalarComparison S H phiStar t) t = (S.a t t - H) / 2 :=
      (hd (t,t) ht).deriv.trans hh.2.1
    exact ⟨hh.1, hid, by rw [hid]; exact hh.2.2⟩
  · intro v x y
    rw [Complex.norm_exp]
    simp

end EmcsfAcExtension.Global.Observation
