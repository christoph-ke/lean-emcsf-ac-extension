module

public import EmcsfAcExtension.Local.Calculus.AxisCross
public import EmcsfAcExtension.Local.Defs.Renormalized
import EmcsfAcExtension.Infra.Calculus.DiagonalChain

/-! # Covariant and gauge-fixed scalar axis matching

The C¹ axis calculation uses canonical domain partials, including both vertices of the
closed triangle. internal project record supplies the axis gauge for the paper's ordinary
derivative;
internal project record supplies the positive-time nondegeneracy needed for uniqueness of
derivatives.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local

/-- At the axis the literal outgoing renormalization is the outgoing partial of
`a`: the radius divisions and the mass ratio have their defined zero values. -/
theorem jC1_axis_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    jC1 (triangle 0 T) S t t = pdV (triangle 0 T) S.a t t := by
  simp [jC1, Fields.mu, (hS.axis t ⟨ht.1, le_rfl, ht.2⟩).1]

/-- The literal incoming renormalization at the axis includes exactly the
connection correction `ieAφ`; no gauge assumption is needed. -/
theorem kC1_axis_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    kC1 e (triangle 0 T) S t t =
      pdU (triangle 0 T) S.b t t + I * e * S.A t t * S.phi t t := by
  have ha := hS.axis t ⟨ht.1, le_rfl, ht.2⟩
  simp [kC1, Fields.mu, ha.1, ha.2.2.2.2.2]

/-- Gauge-free axis matching, as required by internal project record. The common value is the
covariant diagonal derivative. Positive time excludes the singleton-domain
counterexample recorded in the run-2 diagnostic. -/
theorem bv_axis_match_covariant {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    jC1 (triangle 0 T) S t t = kC1 e (triangle 0 T) S t t ∧
      HasDerivWithinAt (fun s => S.phi s s)
        (jC1 (triangle 0 T) S t t - I * e * S.A t t * S.phi t t) (Icc 0 T) t := by
  have hcross := scalar_axis_cross_partials_aux hT hS ht
  have hda : HasDerivWithinAt (fun s => S.phi s s)
      (pdU (triangle 0 T) S.a t t + pdV (triangle 0 T) S.a t t) (Icc 0 T) t :=
    (hasDerivWithinAt_diagonal (c1_a_aux hS) ht).congr
      (fun s hs => (hS.axis s ⟨hs.1, le_rfl, hs.2⟩).2.2.2.2.1.symm)
      (hS.axis t ⟨ht.1, le_rfl, ht.2⟩).2.2.2.2.1.symm
  have hdb : HasDerivWithinAt (fun s => S.phi s s)
      (pdU (triangle 0 T) S.b t t + pdV (triangle 0 T) S.b t t) (Icc 0 T) t :=
    (hasDerivWithinAt_diagonal (c1_b_aux hS) ht).congr
      (fun s hs => (hS.axis s ⟨hs.1, le_rfl, hs.2⟩).2.2.2.2.2.symm)
      (hS.axis t ⟨ht.1, le_rfl, ht.2⟩).2.2.2.2.2.symm
  rw [hcross.1] at hda
  rw [hcross.2, add_zero] at hdb
  constructor
  · have heq := (uniqueDiffOn_Icc hT t ht).eq_deriv _ hda hdb
    rw [jC1_axis_aux hS ht, kC1_axis_aux hS ht]
    linear_combination heq
  · apply hda.congr_deriv
    rw [jC1_axis_aux hS ht]
    ring

/-- [node restart-bv-axis-match]
In the approved zero-axis potential gauge the common renormalized derivative is the
ordinary diagonal derivative, charged_SF_new_version.tex:L4559–4586. No estimate or constant occurs.
-/
theorem bv_axis_match {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T))
    (hA : ∀ t ∈ Icc 0 T, S.A t t = 0) {t : ℝ} (ht : t ∈ Icc 0 T) :
    jC1 (triangle 0 T) S t t = kC1 e (triangle 0 T) S t t ∧
      HasDerivWithinAt (fun s => S.phi s s) (jC1 (triangle 0 T) S t t) (Icc 0 T) t := by
  simpa only [hA t ht, ofReal_zero, mul_zero, zero_mul, sub_zero] using
    bv_axis_match_covariant hT hS ht

/-- [node restart-stab-axis]
The smooth scalar center matching used in stability (charged_SF_new_version.tex:L4980–4986),
in the common axis gauge. It already holds on the C¹ class. -/
theorem stab_axis {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T))
    (hA : ∀ t ∈ Icc 0 T, S.A t t = 0) {t : ℝ} (ht : t ∈ Icc 0 T) :
    kC1 e (triangle 0 T) S t t = jC1 (triangle 0 T) S t t ∧
      HasDerivWithinAt (fun s => S.phi s s) (jC1 (triangle 0 T) S t t) (Icc 0 T) t := by
  have h := bv_axis_match hT hS hA ht
  exact ⟨h.1.symm, h.2⟩

/-- [node restart-sec-independent-null-construction#smooth-axis-derivative]
The derivative of each classical approximant's axis scalar is its diagonal `j`,
charged_SF_new_version.tex:L6453–6457, with the approved axis gauge. -/
theorem Null.smooth_axis_derivative {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T))
    (hA : ∀ t ∈ Icc 0 T, S.A t t = 0) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun s => S.phi s s) (jC1 (triangle 0 T) S t t) (Icc 0 T) t :=
  (bv_axis_match hT hS hA ht).2

/-- [node restart-sec-independent-null-construction#smooth-axis-matching]
The incoming and outgoing diagonal derivatives have the positive matching sign,
charged_SF_new_version.tex:L6207–6207, and both equal the ordinary axis derivative. -/
theorem Null.smooth_axis_matching {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T))
    (hA : ∀ t ∈ Icc 0 T, S.A t t = 0) {t : ℝ} (ht : t ∈ Icc 0 T) :
    kC1 e (triangle 0 T) S t t = jC1 (triangle 0 T) S t t ∧
      HasDerivWithinAt (fun s => S.phi s s) (jC1 (triangle 0 T) S t t) (Icc 0 T) t :=
  stab_axis hT hS hA ht

end EmcsfAcExtension.Local
