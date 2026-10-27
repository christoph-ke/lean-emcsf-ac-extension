module

public import EmcsfAcExtension.Local.Stability.AssemblyIdentity
import EmcsfAcExtension.Local.Stability.Moments
import EmcsfAcExtension.Local.Stability.MomentsAllExponents
import EmcsfAcExtension.Local.Stability.MomentsQuadratic
import EmcsfAcExtension.Local.Stability.MomentsIncoming

/-! # Stability moments and Hardy node theorems

The internal project record analytic cores applied to the internal project record field identities.
The estimates use the fixed geometric box in `StabSetting` and universal
numerical constants, uniformly in all solution and scale parameters.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [node restart-stab-out-moment]
Outgoing radial moment for every real `p ≤ 1 - ε²`, charged_SF_new_version.tex:L5012–5023.
The literal constant `4` is universal, independent of `T,e,ε,M,A,S,h,p`.
The small-data condition is the standing separated-exponent regime. -/
theorem stab_out_moment
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h)
    (hε : ε ^ 2 ≤ 1 / 4) {p u v : ℝ} (hp : p ≤ 1 - ε ^ 2)
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    ENNReal.ofReal ‖S.theta u v / (S.lam u v : ℂ)‖ ≤
      ENNReal.ofReal 4 * ∫⁻ s in Ioc u v,
        ENNReal.ofReal ((S.r u s / S.r u v) ^ p) *
          outEnv 0 (jC1 (triangle 0 T) S) s := by
  rcases huv.eq_or_lt with heq | huv
  · subst v
    rw [stab_out_ratio_axis hset ⟨hu, hvT⟩, norm_zero, ENNReal.ofReal_zero]
    exact bot_le
  · exact stab_out_moment_all_exponents_of_identity hset
      (fun _ _ hu huv hvT => stab_out_reconstruction_smul hset.c1 hu huv hvT) hε hp hu huv hvT

/-- [node restart-stab-in-moment]
Incoming radial moment for every real `p ≤ 1 - ε²`, charged_SF_new_version.tex:L5012–5023.
The literal constant `4` is universal, independent of `T,e,ε,M,A,S,h,p`.
The small-data condition is the standing separated-exponent regime. -/
theorem stab_in_moment
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h)
    (hε : ε ^ 2 ≤ 1 / 4) {p u v : ℝ} (hp : p ≤ 1 - ε ^ 2)
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    ENNReal.ofReal ‖S.xi u v / (S.nu u v : ℂ)‖ ≤
      ENNReal.ofReal 4 * ∫⁻ s in Icc u v,
        ENNReal.ofReal ((S.r s v / S.r u v) ^ p) *
          inEnv T (kC1 e (triangle 0 T) S) s := by
  rcases huv.eq_or_lt with heq | huv
  · subst v
    rw [stab_in_ratio_axis hset ⟨hu, hvT⟩, norm_zero, ENNReal.ofReal_zero]
    exact bot_le
  · exact stab_in_moment_all_exponents_of_identity hset
      (fun _ _ hu huv hvT => stab_in_reconstruction_smul hset.c1 hu huv hvT) hε hp hu huv hvT

/-- [node restart-stab-out-hardy]
Outgoing linear Hardy bound, charged_SF_new_version.tex:L5027–5038.
The numerical constant `16/3` is universal and independent of all parameters. -/
theorem stab_out_hardy
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h)
    (hε : ε ^ 2 ≤ 1 / 4) {u : ℝ} (hu : 0 ≤ u) (huT : u ≤ T) :
    (∫⁻ s in Ioc u T, ENNReal.ofReal
      (S.lam u s / S.r u s * ‖S.theta u s / (S.lam u s : ℂ)‖)) ≤
        ENNReal.ofReal (16 / 3) * ∫⁻ s in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S) s := by
  exact stab_out_hardy_of_identity hset
    (fun _ _ hu huv hvT => stab_out_reconstruction_smul hset.c1 hu huv hvT) hε hu huT

/-- [node restart-stab-out-hardy]
Outgoing quadratic Hardy bound, charged_SF_new_version.tex:L5027–5038.
The numerical constant `16/3` is universal and independent of all parameters
with the small ratio factor `ε` displayed. -/
theorem stab_out_hardy_quadratic
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h)
    (hε : ε ^ 2 ≤ 1 / 4) {u : ℝ} (hu : 0 ≤ u) (huT : u ≤ T) :
    (∫⁻ s in Ioc u T, ENNReal.ofReal
      (S.lam u s / S.r u s * ‖S.theta u s / (S.lam u s : ℂ)‖ ^ 2)) ≤
      ENNReal.ofReal ((16 / 3) * ε) *
        ∫⁻ s in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S) s := by
  exact stab_out_hardy_quadratic_of_identity hset
    (fun _ _ hu huv hvT => stab_out_reconstruction_smul hset.c1 hu huv hvT) hε hu huT

/-- [node restart-stab-in-hardy]
Incoming linear Hardy bound, charged_SF_new_version.tex:L5027–5038.
The numerical constant `16/3` is universal and independent of all parameters. -/
theorem stab_in_hardy
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h)
    (hε : ε ^ 2 ≤ 1 / 4) {v : ℝ} (hv : 0 ≤ v) (hvT : v ≤ T) :
    (∫⁻ s in Icc 0 v, ENNReal.ofReal
      (-S.nu s v / S.r s v * ‖S.xi s v / (S.nu s v : ℂ)‖)) ≤
      ENNReal.ofReal (16 / 3) * ∫⁻ s in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S) s := by
  exact stab_in_hardy_of_identity hset
    (fun _ _ hu huv hvT => stab_in_reconstruction_smul hset.c1 hu huv hvT) hε hv hvT

/-- [node restart-stab-in-hardy]
Incoming quadratic Hardy bound, charged_SF_new_version.tex:L5027–5038.
The numerical constant `16/3` is universal and independent of all parameters
with the small ratio factor `ε` displayed. -/
theorem stab_in_hardy_quadratic
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h)
    (hε : ε ^ 2 ≤ 1 / 4) {v : ℝ} (hv : 0 ≤ v) (hvT : v ≤ T) :
    (∫⁻ s in Icc 0 v, ENNReal.ofReal
      (-S.nu s v / S.r s v * ‖S.xi s v / (S.nu s v : ℂ)‖ ^ 2)) ≤
      ENNReal.ofReal ((16 / 3) * ε) *
        ∫⁻ s in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S) s := by
  exact stab_in_hardy_quadratic_of_identity hset
    (fun _ _ hu huv hvT => stab_in_reconstruction_smul hset.c1 hu huv hvT) hε hv hvT

end EmcsfAcExtension.Local
