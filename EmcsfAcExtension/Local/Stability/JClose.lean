module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.AssemblyMoments

/-! # Incoming homogeneous budget for the outgoing derivative comparison

The coefficient in the exact j transport is the incoming quadratic Hardy
integrand. This is the first estimate in charged_SF_new_version.tex:L5345–5345.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

/-- The incoming real j coefficient is exactly its quadratic normalized
flux, including the totalized axis value. No estimate constant is used. -/
theorem j_coefficient_eq_flux {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) {u v : ℝ}
    (hp : (u, v) ∈ triangle 0 T) :
    -‖S.xi u v‖ ^ 2 / (S.nu u v * S.r u v) =
      -S.nu u v / S.r u v * ‖S.xi u v / (S.nu u v : ℂ)‖ ^ 2 := by
  have hn := (hset.c1.nu_neg (u, v) hp).ne
  by_cases hr : S.r u v = 0
  · simp [hr]
  rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  field_simp

/-- [node restart-sec-bv-stability-independent#j-homogeneous-integral]
The real j coefficient has incoming integral at most `C ε ‖K‖₁`,
charged_SF_new_version.tex:L5345–5345. `C` is universal, independent of the box envelope
constant, coupling, length, background, data, and derivative suprema. -/
theorem j_homogeneous_integral : ∃ C : ℝ, 0 < C ∧
    ∀ (e T ε M A : ℝ) (S : Fields) (h : ℝ → ℂ),
      StabSetting e T ε M A S h → ε ^ 2 ≤ 1 / 4 →
      ∀ v ∈ Icc 0 T,
        (∫⁻ u in Icc 0 v, ENNReal.ofReal
          (-‖S.xi u v‖ ^ 2 / (S.nu u v * S.r u v))) ≤
          ENNReal.ofReal (C * ε) *
            ∫⁻ u in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S) u := by
  refine ⟨16 / 3, by norm_num, ?_⟩
  intro e T ε M A S h hset hε v hv
  calc
    _ = ∫⁻ u in Icc 0 v, ENNReal.ofReal
        (-S.nu u v / S.r u v * ‖S.xi u v / (S.nu u v : ℂ)‖ ^ 2) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro u hu
      dsimp only
      rw [j_coefficient_eq_flux hset ⟨hu.1, hu.2, hv.2⟩]
    _ ≤ _ := stab_in_hardy_quadratic hset hε hv.1 hv.2

end EmcsfAcExtension.Local.Stab
