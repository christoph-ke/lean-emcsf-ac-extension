module

public import EmcsfAcExtension.Local.Calculus.AxisRates
public import EmcsfAcExtension.Local.Defs.Renormalized
import EmcsfAcExtension.Infra.Calculus.DiagonalChain

/-! # Matching the two renormalized geometric derivatives at the center

The quadratic corrections have their literal zero values at the axis. The continuous
center factors show that both cross expansion partials vanish, so the diagonal chain
rule identifies the remaining two logarithmic partials.
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- The outgoing geometric renormalization at the axis is `∂ᵥλ/λ`. -/
theorem geomL_axis_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    geomL (triangle 0 T) S t t = pdV (triangle 0 T) S.lam t t / S.lam t t := by
  simp [geomL, (hS.axis t ⟨ht.1, le_rfl, ht.2⟩).1]

/-- The incoming geometric renormalization at the axis is `∂ᵤν/ν`. -/
theorem geomN_axis_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    geomN (triangle 0 T) S t t = pdU (triangle 0 T) S.nu t t / S.nu t t := by
  simp [geomN, (hS.axis t ⟨ht.1, le_rfl, ht.2⟩).1]

/-- [node restart-sec-independent-area#smooth-geometric-axis-match]
Both geometric renormalizations equal the diagonal logarithmic derivative at the
regular center, charged_SF_new_version.tex:L4891–4892 and internal project record's approved repair.
The proof
already holds for the C¹ class and is gauge independent. -/
theorem Area.smooth_geometric_axis_match {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    geomL (triangle 0 T) S t t = geomN (triangle 0 T) S t t ∧
      HasDerivWithinAt (fun s => Real.log (S.lam s s))
        (geomL (triangle 0 T) S t t) (Icc 0 T) t := by
  have hc := expansion_axis_cross_partials_aux hT hS ht
  have hp : (t, t) ∈ triangle 0 T := ⟨ht.1, le_rfl, ht.2⟩
  have haxis (s : ℝ) (hs : s ∈ Icc 0 T) : S.lam s s = -S.nu s s :=
    eq_neg_of_add_eq_zero_left (hS.axis s ⟨hs.1, le_rfl, hs.2⟩).2.2.2.1
  have hl : HasDerivWithinAt (fun s => S.lam s s)
      (pdV (triangle 0 T) S.lam t t) (Icc 0 T) t := by
    have h := hasDerivWithinAt_diagonal hS.c1_lam ht
    change HasDerivWithinAt (fun s => S.lam s s)
      (pdU (triangle 0 T) S.lam t t + pdV (triangle 0 T) S.lam t t) (Icc 0 T) t at h
    simpa only [hc.1, zero_add] using h
  have hn : HasDerivWithinAt (fun s => S.lam s s)
      (-pdU (triangle 0 T) S.nu t t) (Icc 0 T) t := by
    have h := (hasDerivWithinAt_diagonal hS.c1_nu ht).neg.congr haxis (haxis t ht)
    change HasDerivWithinAt (fun s => S.lam s s)
      (-(pdU (triangle 0 T) S.nu t t + pdV (triangle 0 T) S.nu t t)) (Icc 0 T) t at h
    simpa only [hc.2, add_zero] using h
  constructor
  · have he := (uniqueDiffOn_Icc hT t ht).eq_deriv _ hl hn
    rw [geomL_axis_aux hS ht, geomN_axis_aux hS ht, he]
    have hnu := eq_neg_of_add_eq_zero_right (hS.axis t hp).2.2.2.1
    rw [hnu, div_neg, neg_div]
  · rw [geomL_axis_aux hS ht]
    exact hl.log (hS.lam_pos _ hp).ne'

end EmcsfAcExtension.Local
