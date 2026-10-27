module

public import EmcsfAcExtension.Local.Stability.AssemblyIdentity
public import EmcsfAcExtension.Local.Stability.OrderedKernelPointwise
import EmcsfAcExtension.Local.Stability.OrderedKernelL1
import EmcsfAcExtension.Local.Stability.OrderedKernelIncomingL1

/-! # Ordered curvature estimates assembled from field identities

The literal primitives are identified with the actual field transport sources
by `stab_j_transport_split` and `stab_k_transport_split`. The constants are
universal and retain the explicit small ratio factor, with no minimum radius.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [internal]
Outgoing scalar primitive pointwise bound, charged_SF_new_version.tex:L5050–5053.
The constant `256` is universal.
All constants are uniform in the admissible exponent and all field parameters. -/
theorem stab_ordered_pointwise
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h)
    {p u v : ℝ} (hp0 : 1 / 2 ≤ p) (hp : p ≤ 1 - ε ^ 2)
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    ‖(S.nu u v : ℂ) * S.theta u v / (S.r u v : ℂ) ^ 2 *
      curvScalar (triangle 0 T) S u v‖ₑ ≤
      ENNReal.ofReal (256 * ε) * stabOrderedKernel p
        ((Icc 0 T).indicator (inEnv T (kC1 e (triangle 0 T) S)))
        ((Icc 0 T).indicator (outEnv 0 (jC1 (triangle 0 T) S))) u v := by
  exact stab_ordered_pointwise_of_identity hset
    (fun _ _ hu huv hvT => stab_in_reconstruction_smul hset.c1 hu huv hvT) hp0 hp hu huv hvT

/-- [internal]
Full outgoing scalar transport source area bound, charged_SF_new_version.tex:L5059–5064.
The constant `1536` is universal, independent of `T,e,M,A,S,h,p` and derivative suprema.
All constants are uniform in the admissible exponent and all field parameters. -/
theorem stab_ordered_l1
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h)
    {p : ℝ} (hp0 : 1 / 2 ≤ p) (hp : p ≤ 1 - ε ^ 2) :
    (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v,
      ‖(S.nu u v : ℂ) * S.theta u v / (S.r u v : ℂ) ^ 2 *
        (curvScalar (triangle 0 T) S u v +
          2 * starRingEnd ℂ (curvScalar (triangle 0 T) S u v))‖ₑ) ≤
      ENNReal.ofReal (1536 * ε) *
        (∫⁻ s in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S) s) *
        (∫⁻ w in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S) w) := by
  exact stab_ordered_source_l1_of_identity hset
    (fun _ _ hu huv hvT => stab_in_reconstruction_smul hset.c1 hu huv hvT) hp0 hp

/-- [internal]
Full incoming scalar transport source area bound, charged_SF_new_version.tex:L5065–5068.
The constant `1536` is universal, independent of `T,e,M,A,S,h,p` and derivative suprema.
The incoming primitive has the approved conjugate orientation.
All constants are uniform in the admissible exponent and all field parameters. -/
theorem stab_incoming_ordered_l1
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h)
    {p : ℝ} (hp0 : 1 / 2 ≤ p) (hp : p ≤ 1 - ε ^ 2) :
    (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v,
      ‖(S.lam u v : ℂ) * S.xi u v / (S.r u v : ℂ) ^ 2 *
        (curvScalarIn e (triangle 0 T) S u v +
          2 * starRingEnd ℂ (curvScalarIn e (triangle 0 T) S u v))‖ₑ) ≤
      ENNReal.ofReal (1536 * ε) *
        (∫⁻ s in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S) s) *
        (∫⁻ w in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S) w) := by
  simpa only [stab_curvScalarInConj_eq] using stab_incoming_ordered_l1_of_identity hset
    (fun _ _ hu huv hvT => stab_out_reconstruction_smul hset.c1 hu huv hvT) hp0 hp

end EmcsfAcExtension.Local
